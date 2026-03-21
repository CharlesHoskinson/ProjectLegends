# Plan 1: Critical Bug Fixes

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Fix all 8 critical bugs and replace 6 stubs masquerading as implementations identified by the audit.

**Architecture:** Each task is an independent fix. No task depends on another. All can be executed in any order.

**Tech Stack:** C++23, GoogleTest, gsl-lite

---

### Task 1: Fix CRC-32 Lookup Table

**Audit ref:** Agent 7 — `save_manager.cpp:42-57`, duplicate rows in CRC-32 table
**Risk:** Save state integrity checks produce incorrect checksums

**Files:**
- Modify: `src/app/save_manager.cpp:42-95` (CRC-32 table)
- Test: `tests/unit/test_save_manager.cpp`

- [ ] **Step 1: Write a regression test**

Add a test that computes CRC-32 of a known string and asserts against a known-good value (use an external CRC-32 calculator to get the expected value for `"Hello, World!"`):

```cpp
TEST(SaveManagerCRC, KnownVectorHelloWorld) {
    const char* data = "Hello, World!";
    uint32_t crc = legends::SaveManager::computeCRC32(data, 13);
    EXPECT_EQ(crc, 0xEC4AC3D0u);  // Known CRC-32 of "Hello, World!"
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cmake --build build/dev --target legends_unit_tests && ctest --test-dir build/dev -R SaveManagerCRC -V`
Expected: FAIL (incorrect CRC due to duplicated table rows)

- [ ] **Step 3: Replace the CRC-32 table with a correct, generated table**

Generate the standard CRC-32 table (polynomial 0xEDB88320) using a `constexpr` generator function, or replace with the well-known 256-entry table from RFC 3720. Verify all 256 entries are unique.

Add a `static_assert` after the table:
```cpp
static_assert(kCrcTable[1] != kCrcTable[49], "CRC table has duplicate rows");
static_assert(kCrcTable[128] != kCrcTable[0], "CRC table second half is unique");
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cmake --build build/dev --target legends_unit_tests && ctest --test-dir build/dev -R SaveManagerCRC -V`
Expected: PASS

- [ ] **Step 5: Run full save manager tests**

Run: `ctest --test-dir build/dev -R test_save_manager -V`
Expected: All existing tests PASS

- [ ] **Step 6: Commit**

```bash
git add src/app/save_manager.cpp tests/unit/test_save_manager.cpp
git commit -m "fix: replace duplicate CRC-32 table rows with correct polynomial 0xEDB88320"
```

---

### Task 2: Add IPC Payload Size Cap

**Audit ref:** Agent 8 — `message_codec.cpp`, unbounded allocation from untrusted wire data
**Risk:** Remote DoS via crafted IPC message with payload_size=0xFFFFFFFF

**Files:**
- Modify: `include/legends_ipc/message_codec.h` (add constant)
- Modify: `src/legends_ipc/message_codec.cpp` (add check)
- Test: `tests/unit/test_ipc_message_codec.cpp`

- [ ] **Step 1: Write a test that sends an oversized payload header**

```cpp
TEST(MessageCodecTest, RejectsOversizedPayload) {
    legends_ipc::MessageCodec codec;
    // Craft a header with payload_size = 256MB + 1
    std::array<uint8_t, 10> header{};
    legends_ipc::write_u16_le(std::span{header}.subspan(0, 2), static_cast<uint16_t>(legends_ipc::MsgType::StepMsReq));
    legends_ipc::write_u32_le(std::span{header}.subspan(2, 4), 256 * 1024 * 1024 + 1);  // 256MB+1
    legends_ipc::write_u32_le(std::span{header}.subspan(6, 4), 1);  // seq_id
    codec.feed(std::span<const uint8_t>{header});
    auto result = codec.try_decode();
    ASSERT_FALSE(result.has_value());
    EXPECT_EQ(result.error(), legends_ipc::IpcError::InvalidHeader);
}
```

- [ ] **Step 2: Run test to verify it fails (currently accepts any size)**

- [ ] **Step 3: Add `kMaxPayloadSize` constant and rejection check**

In `message_codec.h`:
```cpp
static constexpr uint32_t kMaxPayloadSize = 64 * 1024 * 1024;  // 64 MB
```

In `message_codec.cpp` `try_decode()`, after deserializing the header:
```cpp
if (hdr.payload_size > kMaxPayloadSize) {
    buffer_.clear();
    return std::unexpected(IpcError::InvalidHeader);
}
```

- [ ] **Step 4: Run test to verify it passes**

- [ ] **Step 5: Run all IPC tests**

Run: `ctest --test-dir build/dev -R test_ipc -V`

- [ ] **Step 6: Commit**

```bash
git add include/legends_ipc/message_codec.h src/legends_ipc/message_codec.cpp tests/unit/test_ipc_message_codec.cpp
git commit -m "fix: reject IPC messages with payload > 64MB to prevent DoS"
```

---

### Task 3: Fix SDL3 AudioSink Zero-Channel Division

**Audit ref:** Agent 9 — `audio_sink_sdl3.cpp:29`, division by zero in `getQueuedFrames()`
**Risk:** Crash on malformed audio config

**Files:**
- Modify: `src/pal/sdl3/audio_sink_sdl3.cpp`
- Test: `tests/unit/test_pal_audio_sink.cpp`

- [ ] **Step 1: Write a test for zero-channel config**

```cpp
TEST_F(PalAudioSinkTest, OpenWithZeroChannelsReturnsError) {
    pal::AudioConfig config{};
    config.sample_rate = 44100;
    config.channels = 0;
    config.buffer_frames = 1024;
    auto sink = pal::Platform::createAudioSink();
    ASSERT_NE(sink, nullptr);
    EXPECT_EQ(sink->open(config), pal::Result::InvalidParameter);
}
```

- [ ] **Step 2: Run test to verify it fails (currently no validation)**

- [ ] **Step 3: Add zero-channel/zero-rate guard at top of `open()`**

```cpp
if (config.channels == 0 || config.sample_rate == 0) {
    return Result::InvalidParameter;
}
```

- [ ] **Step 4: Run test to verify it passes**

- [ ] **Step 5: Commit**

```bash
git add src/pal/sdl3/audio_sink_sdl3.cpp tests/unit/test_pal_audio_sink.cpp
git commit -m "fix: reject zero channels/sample_rate in SDL3 AudioSink to prevent div-by-zero"
```

---

### Task 4: Fix SDL3 Null Window in Mouse Mode Shutdown

**Audit ref:** Agent 9 — `input_source_sdl3.cpp:36`, `SDL_SetWindowRelativeMouseMode(nullptr, false)`
**Risk:** Undefined behavior on shutdown

**Files:**
- Modify: `src/pal/sdl3/input_source_sdl3.cpp`

- [ ] **Step 1: Add null guard before SDL call**

Change line ~36 from:
```cpp
SDL_SetWindowRelativeMouseMode(nullptr, false);
```
to:
```cpp
// Only reset mouse mode if we have a valid window reference
// (shutdown may be called after window is already destroyed)
```
Remove the call entirely — on shutdown, the window is being destroyed anyway and SDL cleans up mouse state internally.

- [ ] **Step 2: Run PAL input source tests**

Run: `ctest --test-dir build/dev -R test_pal_input -V`

- [ ] **Step 3: Commit**

```bash
git add src/pal/sdl3/input_source_sdl3.cpp
git commit -m "fix: remove SDL_SetWindowRelativeMouseMode(nullptr) call on shutdown"
```

---

### Task 5: Fix SDL2 Volume Data Race

**Audit ref:** Agent 9 — `audio_sink_sdl2.cpp:274,292`, `volume_` read from callback without sync
**Risk:** Audio corruption / undefined behavior

**Files:**
- Modify: `src/pal/sdl2/audio_sink_sdl2.cpp`

- [ ] **Step 1: Change `volume_` to `std::atomic<float>`**

In the class declaration, change:
```cpp
float volume_ = 1.0f;
```
to:
```cpp
std::atomic<float> volume_{1.0f};
```

Update `setVolume()` to use `.store(val, std::memory_order_relaxed)` and the audio callback to use `.load(std::memory_order_relaxed)`.

Also make `dropped_frames_` atomic: `std::atomic<uint64_t> dropped_frames_{0};`

- [ ] **Step 2: Run PAL audio tests**

Run: `ctest --test-dir build/dev -R test_pal_audio -V`

- [ ] **Step 3: Commit**

```bash
git add src/pal/sdl2/audio_sink_sdl2.cpp
git commit -m "fix: make SDL2 volume_ and dropped_frames_ atomic for audio callback thread safety"
```

---

### Task 6: Fix Proxy connected_ Data Race

**Audit ref:** Agent 8 — `proxy_connection.h:62`, plain `bool` read without mutex
**Risk:** Data race between `is_connected()` and `connect()`/`disconnect()`

**Files:**
- Modify: `src/legends_proxy/proxy_connection.h`

- [ ] **Step 1: Change `connected_` to `std::atomic<bool>`**

```cpp
std::atomic<bool> connected_{false};
```

Update `connect()` and `disconnect()` to use `.store()`, `is_connected()` to use `.load(std::memory_order_acquire)`.

- [ ] **Step 2: Run proxy tests**

Run: `ctest --test-dir build/dev -R test_proxy -V`

- [ ] **Step 3: Commit**

```bash
git add src/legends_proxy/proxy_connection.h
git commit -m "fix: make ProxyConnection::connected_ atomic to prevent data race"
```

---

### Task 7: Fix Config Parser Field Length Limits

**Audit ref:** Agent 2 (Security) — `config_parser.cpp`, REQ-SEC-014 marked "Done" but zero enforcement
**Risk:** Memory exhaustion from adversarial config files

**Files:**
- Modify: `src/app/config_parser.cpp`
- Test: `tests/unit/test_config_parser.cpp`

- [ ] **Step 1: Write tests for oversized fields**

```cpp
TEST_F(ConfigParserTest, RejectsSectionNameOver256Chars) {
    std::string long_section(300, 'a');
    std::string content = "[" + long_section + "]\nkey=value\n";
    auto path = writeTempFile("oversized_", content);
    ConfigParser parser;
    EXPECT_TRUE(parser.loadFile(path));  // loads but truncates/skips
    EXPECT_FALSE(parser.hasSection(long_section));
}

TEST_F(ConfigParserTest, RejectsValueOver4096Chars) {
    std::string long_value(5000, 'x');
    std::string content = "[test]\nkey=" + long_value + "\n";
    auto path = writeTempFile("longval_", content);
    ConfigParser parser;
    parser.loadFile(path);
    EXPECT_LE(parser.get("test", "key").size(), 4096u);
}
```

- [ ] **Step 2: Run tests to verify they fail**

- [ ] **Step 3: Add field length limits in the parsing loop**

In the line-parsing logic, add:
```cpp
constexpr size_t kMaxSectionNameLen = 256;
constexpr size_t kMaxKeyLen = 256;
constexpr size_t kMaxValueLen = 4096;
```
Skip/truncate lines that exceed these limits.

- [ ] **Step 4: Run tests to verify they pass**

- [ ] **Step 5: Commit**

```bash
git add src/app/config_parser.cpp tests/unit/test_config_parser.cpp
git commit -m "fix: enforce config parser field length limits (REQ-SEC-014)"
```

---

### Task 8: Wire formatScreenContext into AI Query Path

**Audit ref:** Agent 2 (Security) — `application.cpp:964-965`, REQ-SEC-018 prompt injection
**Risk:** Screen content injected directly into system prompt without structured delimiters

**Files:**
- Modify: `src/app/application.cpp`

- [ ] **Step 1: Replace raw screen text embedding with formatScreenContext()**

At the AI query submission handler (around line 964), change from directly embedding screen text to:
```cpp
auto formatted = legends::formatScreenContext(screen_text, width, height, cursor_x, cursor_y);
// Use formatted text (with structured delimiters) in the system prompt
```

- [ ] **Step 2: Run application event tests**

Run: `ctest --test-dir build/dev -R test_application -V`

- [ ] **Step 3: Commit**

```bash
git add src/app/application.cpp
git commit -m "fix: use formatScreenContext() for AI prompt injection separation (REQ-SEC-018)"
```

---

### Task 9: Fix PerfOverlay Font Rendering

**Audit ref:** Agent 7 — `perf_overlay.h`, font data is zero-initialized, renders solid white blocks
**Risk:** Performance overlay is unreadable

**Files:**
- Modify: `src/app/perf_overlay.h`

- [ ] **Step 1: Import the CP437 4x7 bitmap font data**

Replace the zero-initialized `font_4x7[128][7] = {}` with actual bitmap font data. The CP437 8x16 font already exists in `src/legends/internal/cp437_font_8x16.h` — extract or create a compact 4x7 version for the overlay, or reuse the existing `drawChar` function from menu_system.cpp with the 8x16 font scaled down.

- [ ] **Step 2: Update `drawChar()` to actually render character glyphs**

Replace the solid-fill block with proper bit-testing against the font data.

- [ ] **Step 3: Remove the `(void)font_4x7;` dead code suppression**

- [ ] **Step 4: Manual visual verification (if SDL3 available) or unit test**

- [ ] **Step 5: Commit**

```bash
git add src/app/perf_overlay.h
git commit -m "fix: implement actual font rendering in PerfOverlay (was solid white blocks)"
```

---

### Task 10: Fix MapperUI commitRemaps() Never Called

**Audit ref:** Agent 7 — `mapper_ui.cpp`, `commitRemaps()` never called, remaps discarded on close
**Risk:** Key remapping UI has no effect

**Files:**
- Modify: `src/app/mapper_ui.cpp`
- Test: `tests/unit/test_mapper_ui.cpp`

- [ ] **Step 1: Write a test that verifies remaps are committed on close**

- [ ] **Step 2: Call `commitRemaps()` in the close handler**

In the method that handles closing the mapper UI (Escape key or explicit close), add:
```cpp
commitRemaps();
```
before setting state to Idle.

- [ ] **Step 3: Run mapper UI tests**

- [ ] **Step 4: Commit**

```bash
git add src/app/mapper_ui.cpp tests/unit/test_mapper_ui.cpp
git commit -m "fix: call commitRemaps() when closing MapperUI so key remaps take effect"
```

---

### Task 11: Fix Dual Error Code Systems

**Audit ref:** Agent 8 — `legends_embed.h` (negative) vs `ffi_core.h` (positive) error codes
**Risk:** Inconsistent error reporting across code paths

**Files:**
- Modify: `src/legends/internal/ffi_core.h`
- Modify: `src/legends/internal/ffi.h`

- [ ] **Step 1: Audit all usages of ffi_core.h error codes**

Search for all references to determine if the positive-value codes from `ffi_core.h` ever escape to the public API.

- [ ] **Step 2: Align error code values**

Either:
a) Make `ffi_core.h` error codes match the negative values in `legends_embed.h`, or
b) Ensure the `safe_call` wrapper in `ffi.h` correctly maps between the two systems

- [ ] **Step 3: Add a static_assert or compile-time test**

```cpp
static_assert(LEGENDS_ERR_NULL_HANDLE != legends_error_t(1), "Error code systems must not collide");
```

- [ ] **Step 4: Run all embed tests**

- [ ] **Step 5: Commit**

```bash
git add src/legends/internal/ffi_core.h src/legends/internal/ffi.h
git commit -m "fix: align dual error code systems between legends_embed.h and ffi_core.h"
```

---

### Task 12: Fix Platform Dirs CoTaskMemFree Leak

**Audit ref:** Agent 3 (C++23) — `platform_dirs.cpp:37-38`, memory leak when WideCharToMultiByte returns 0
**Risk:** Memory leak on Windows

**Files:**
- Modify: `src/app/platform_dirs.cpp`

- [ ] **Step 1: Add gsl::finally (or manual scope guard) for CoTaskMemFree**

```cpp
auto cleanup = gsl::finally([&] { if (path) CoTaskMemFree(path); });
```
Place immediately after the `SHGetKnownFolderPath` call.

- [ ] **Step 2: Run platform dirs tests**

- [ ] **Step 3: Commit**

```bash
git add src/app/platform_dirs.cpp
git commit -m "fix: prevent CoTaskMemFree memory leak in getKnownFolderPath (Windows)"
```
