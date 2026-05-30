#include <Arduino.h>
#include <SPIFFS.h>
#include <Wire.h>
#include <nvs_flash.h>
#include <BluetoothA2DPSource.h>

#include <Adafruit_GFX.h>
#include <Adafruit_SSD1306.h>
#include <TJpg_Decoder.h>

#include "minimp3.h"

// ─────────────────────────────
// OLED
// ─────────────────────────────
#define SCREEN_WIDTH  128
#define SCREEN_HEIGHT 64
Adafruit_SSD1306 display(SCREEN_WIDTH, SCREEN_HEIGHT, &Wire, -1);

// Add this global
static bool audioConfigured = false;

// ─────────────────────────────
// Bluetooth
// ─────────────────────────────
BluetoothA2DPSource a2dp;

// ─────────────────────────────
// MP3
// ─────────────────────────────
#define MP3_PATH "/song.mp3"

static File      mp3File;
static uint32_t  mp3Start = 0;   // byte offset where audio data starts (after ID3)
static mp3dec_t  mp3d;

// ─────────────────────────────
// RING BUFFER  (thread-safe)
// ─────────────────────────────
#define PCM_SIZE 8192   // yield logic in mp3Task prevents overflow; keep DRAM under budget
static int16_t         pcmRing[PCM_SIZE];
static volatile int    pcmRead  = 0;
static volatile int    pcmWrite = 0;
static portMUX_TYPE    pcmMux   = portMUX_INITIALIZER_UNLOCKED;

void pushPCM(const int16_t *data, int len) {
  portENTER_CRITICAL(&pcmMux);
  for (int i = 0; i < len; i++) {
    int next = (pcmWrite + 1) % PCM_SIZE;
    if (next == pcmRead) break;   // buffer full — stop (don't corrupt reader)
    pcmRing[pcmWrite] = data[i];
    pcmWrite = next;
  }
  portEXIT_CRITICAL(&pcmMux);
}

bool popPCM(int16_t &out) {
  portENTER_CRITICAL(&pcmMux);
  if (pcmRead == pcmWrite) {
    portEXIT_CRITICAL(&pcmMux);
    return false;
  }
  out = pcmRing[pcmRead];
  pcmRead = (pcmRead + 1) % PCM_SIZE;
  portEXIT_CRITICAL(&pcmMux);
  return true;
}

// ─────────────────────────────
// ALBUM ART  (TJpgDec → OLED)
// ─────────────────────────────
bool jpegMCU(int16_t x, int16_t y, uint16_t w, uint16_t h, uint16_t *bitmap) {
  if (y >= SCREEN_HEIGHT) return false;
  for (uint16_t row = 0; row < h; row++) {
    for (uint16_t col = 0; col < w; col++) {
      uint16_t px = bitmap[row * w + col];
      // RGB565 → luminance (simple green-channel proxy)
      uint8_t  g  = (px >> 5) & 0x3F;
      display.drawPixel(x + col, y + row, (g > 16) ? WHITE : BLACK);
    }
  }
  return true;
}

// ─────────────────────────────
// ID3v2 parser
// Extracts the first APIC (attached picture) frame.
// Sets mp3Start to the first byte after the entire ID3 tag so the
// decoder never tries to parse tag bytes as audio frames.
// ─────────────────────────────
static uint8_t jpegBuf[16384];
static size_t  jpegLen      = 0;
static bool    albumArtReady = false;

bool extractAlbumArt(File &f) {
  f.seek(0);
  uint8_t hdr[10];
  if (f.read(hdr, 10) != 10) return false;
  if (memcmp(hdr, "ID3", 3) != 0) {
    // No ID3 tag — audio starts at byte 0
    mp3Start = 0;
    f.seek(0);
    return false;
  }

  // ID3v2 syncsafe size
  uint32_t tagSize = ((uint32_t)(hdr[6] & 0x7F) << 21)
                   | ((uint32_t)(hdr[7] & 0x7F) << 14)
                   | ((uint32_t)(hdr[8] & 0x7F) <<  7)
                   |  (uint32_t)(hdr[9] & 0x7F);

  // Audio data starts immediately after the ID3 block (10-byte header + payload)
  mp3Start = 10 + tagSize;

  bool found = false;
  uint32_t pos = 10;

  while (pos + 10 <= 10 + tagSize) {
    uint8_t fhdr[10];
    if (f.read(fhdr, 10) != 10) break;
    pos += 10;

    // Frame size (ID3v2.3 — big-endian, not syncsafe)
    uint32_t fsize = ((uint32_t)fhdr[4] << 24) | ((uint32_t)fhdr[5] << 16)
                   | ((uint32_t)fhdr[6] <<  8) |  (uint32_t)fhdr[7];

    if (fsize == 0) break;  // padding reached

    if (!found && memcmp(fhdr, "APIC", 4) == 0) {
      // Layout: encoding(1) + MIME(null) + picType(1) + desc(null) + data
      uint8_t  tmp[256];
      uint32_t peek = min((uint32_t)sizeof(tmp), fsize);
      f.read(tmp, peek);

      uint32_t i = 1;                              // skip encoding byte
      while (i < peek && tmp[i] != 0) i++;        // skip MIME string
      i++;                                          // skip null terminator
      i++;                                          // skip picture type byte
      while (i < peek && tmp[i] != 0) i++;        // skip description string
      i++;                                          // skip null terminator

      // Absolute offset of the image data inside the file
      uint32_t imgOffset = (f.position() - peek) + i;
      uint32_t imgLen    = fsize - i;
      if (imgLen > sizeof(jpegBuf)) imgLen = sizeof(jpegBuf);

      f.seek(imgOffset);
      jpegLen = f.read(jpegBuf, imgLen);
      found   = (jpegLen > 0);

      // Don't break — still need to advance pos correctly below
    }

    // Advance to next frame
    f.seek(pos + fsize);
    pos += fsize;
  }

  // Always leave file pointer at start of audio data
  f.seek(mp3Start);
  return found;
}

// ─────────────────────────────
// MP3 DECODE TASK  (Core 0)
// ─────────────────────────────
static uint8_t mp3InBuf[2048];    // larger read buffer = fewer SPIFFS reads
static int16_t mp3PcmBuf[1152 * 2];

void mp3Task(void *p) {
  int inLen = 0;

  // Start reading from the actual audio data (past ID3 tag)
  mp3File.seek(mp3Start);

  while (true) {
    // Top up the input buffer
    int space = (int)sizeof(mp3InBuf) - inLen;
    if (space > 0 && mp3File.available()) {
      inLen += mp3File.read(mp3InBuf + inLen, space);
    } else if (!mp3File.available()) {
      // Loop the track
      mp3File.seek(mp3Start);
      inLen = 0;
      vTaskDelay(10 / portTICK_PERIOD_MS);
      continue;
    }

    mp3dec_frame_info_t info;
    int samples = mp3dec_decode_frame(&mp3d, mp3InBuf, inLen, mp3PcmBuf, &info);

    if (info.frame_bytes > 0) {
      memmove(mp3InBuf, mp3InBuf + info.frame_bytes, inLen - info.frame_bytes);
      inLen -= info.frame_bytes;
    } else if (samples == 0 && info.frame_bytes == 0) {
      // Decoder is stuck (corrupt frame) — skip one byte
      if (inLen > 0) {
        memmove(mp3InBuf, mp3InBuf + 1, inLen - 1);
        inLen--;
      }
    }

    if (samples > 0) {
      if (!audioConfigured) {
        audioConfigured = true;
        Serial.printf("MP3: %d Hz, %d ch\n", info.hz, info.channels);
      }
      pushPCM(mp3PcmBuf, samples * info.channels);
    }

    // Yield when buffer is ≥75% full to let A2DP drain it; prevents sample drops
    int used = (pcmWrite - pcmRead + PCM_SIZE) % PCM_SIZE;
    vTaskDelay((used > PCM_SIZE * 3 / 4) ? pdMS_TO_TICKS(20) : 1);
  }
}

// ─────────────────────────────
// OLED TASK  (Core 1)
// ─────────────────────────────
void oledTask(void *p) {
  while (true) {
    if (albumArtReady && jpegLen > 0) {
      // Re-render every loop so clearDisplay() doesn't erase the art permanently
      display.clearDisplay();
      TJpgDec.drawJpg(0, 0, jpegBuf, jpegLen);
      display.setCursor(0, 56);
      display.setTextSize(1);
      display.setTextColor(WHITE);
      display.print("  Now Playing...");
      display.display();
      vTaskDelay(5000 / portTICK_PERIOD_MS); // slow refresh — art doesn't change
    } else {
      display.clearDisplay();
      display.setTextSize(1);
      display.setTextColor(WHITE);
      display.setCursor(16, 24);
      display.print("Now Playing...");
      display.setCursor(24, 40);
      display.print("via Bluetooth");
      display.display();
      vTaskDelay(500 / portTICK_PERIOD_MS);
    }
  }
}

// ─────────────────────────────
// A2DP AUDIO CALLBACK
// Called from the Bluetooth stack — must be fast and non-blocking.
// ─────────────────────────────
int32_t get_audio(Frame *frame, int32_t count) {
  for (int i = 0; i < count; i++) {
    int16_t sL = 0, sR = 0;
    popPCM(sL);
    if (!popPCM(sR)) sR = sL;   // mono source → duplicate to both channels
    frame[i].channel1 = sL;
    frame[i].channel2 = sR;
  }
  return count;
}

// ─────────────────────────────
// SETUP
// ─────────────────────────────
void setup() {
  Serial.begin(115200);
  delay(200);  // let serial settle

  // ── 1. NVS: safe init (only erase if genuinely corrupt) ──────────────
  esp_err_t nvsRet = nvs_flash_init();
  if (nvsRet == ESP_ERR_NVS_NO_FREE_PAGES ||
      nvsRet == ESP_ERR_NVS_NEW_VERSION_FOUND) {
    Serial.println("NVS corrupt — erasing and reinitialising");
    ESP_ERROR_CHECK(nvs_flash_erase());
    ESP_ERROR_CHECK(nvs_flash_init());
  } else {
    ESP_ERROR_CHECK(nvsRet);
  }

  // ── 2. SPIFFS ─────────────────────────────────────────────────────────
  if (!SPIFFS.begin(true)) {
    Serial.println("[ERROR] SPIFFS mount failed — halting");
    while (true) delay(1000);
  }
  Serial.println("SPIFFS OK");

  // ── 3. Open MP3 file ──────────────────────────────────────────────────
  mp3File = SPIFFS.open(MP3_PATH, FILE_READ);
  if (!mp3File) {
    Serial.printf("[ERROR] Cannot open %s — halting\n", MP3_PATH);
    while (true) delay(1000);
  }
  Serial.printf("Opened %s (%d bytes)\n", MP3_PATH, (int)mp3File.size());

  // ── 4. Parse ID3 + extract album art ──────────────────────────────────
  mp3dec_init(&mp3d);
  albumArtReady = extractAlbumArt(mp3File);
  Serial.printf("Album art: %s  |  audio starts at byte %u\n",
                albumArtReady ? "found" : "not found", mp3Start);

  // ── 5. OLED ───────────────────────────────────────────────────────────
  Wire.begin();
  if (!display.begin(SSD1306_SWITCHCAPVCC, 0x3C)) {
    Serial.println("[WARN] SSD1306 init failed — continuing without OLED");
  } else {
    TJpgDec.setJpgScale(1);
    TJpgDec.setCallback(jpegMCU);
    display.clearDisplay();
    display.display();
    Serial.println("OLED OK");
  }

  // ── 6. Bluetooth A2DP ─────────────────────────────────────────────────
  // Change "WH-1000XM4" to the exact Bluetooth name of your headphones.
  a2dp.set_auto_reconnect(true);
  a2dp.start("WH-1000XM4", get_audio);
  Serial.println("A2DP started — searching for headphones...");

  // ── 7. FreeRTOS tasks ─────────────────────────────────────────────────
  // MP3 decoder on Core 0 (same core as BT stack is fine; BT runs its own task)
  xTaskCreatePinnedToCore(mp3Task,  "mp3",  32768, NULL, 2, NULL, 0);
  // OLED renderer on Core 1
  xTaskCreatePinnedToCore(oledTask, "oled", 8192,  NULL, 1, NULL, 1);

  Serial.println("Setup complete");
}

void loop() {
  // Nothing to do — all work is in FreeRTOS tasks
  delay(1000);
}