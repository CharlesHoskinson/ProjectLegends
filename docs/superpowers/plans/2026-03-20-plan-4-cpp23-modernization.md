# Plan 4: C++23 & gsl-lite Modernization

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Bring the codebase from C++17-era patterns to idiomatic C++23 with consistent gsl-lite contract usage, prioritized by the audit's quantitative findings.

**Architecture:** Mechanical, sweeping changes organized by pattern. Each task is one pattern applied across the codebase. Depends on Plan 2 (test infrastructure) being complete so shared fixtures absorb signature changes.

**Tech Stack:** C++23, gsl-lite v1.0.0

**Prerequisite:** Plan 2 (Test Infrastructure) tasks 1-4 complete.

---

### Task 1: Add `[[nodiscard]]` to All Headers

**Audit ref:** Agent 9 (Public Headers) — 0 of 353 value-returning functions annotated

**Files:**
- Modify: All 7 `include/pal/*.h` headers
- Modify: All 11 `include/legends_ipc/*.h` headers
- Modify: All ~38 `src/app/*.h` headers

**Approach:** Systematic sweep. Add `[[nodiscard]]` to every function that returns a non-void type. Also add `[[nodiscard]]` to the `pal::Result` and `IpcError` enum class declarations themselves.

- [ ] **Step 1: PAL headers (7 files, ~56 functions)**
- [ ] **Step 2: Build to verify no warnings from existing code that discards results**
- [ ] **Step 3: Fix any callsites that trigger `-Wunused-result` warnings**
- [ ] **Step 4: IPC headers (11 files, ~72 functions)**
- [ ] **Step 5: App headers (38 files, ~190 functions)**
- [ ] **Step 6: Full build + test suite**
- [ ] **Step 7: Commit**

```bash
git commit -m "chore: add [[nodiscard]] to all value-returning functions (353 sites)"
```

---

### Task 2: Replace `const std::string&` with `std::string_view`

**Audit ref:** Agent 9 — 0 of 75 read-only string parameters use string_view

**Files:**
- Modify: `src/app/config_parser.h` (highest impact — most-called API)
- Modify: `src/app/mount_manager.h`
- Modify: `src/app/save_manager.h`
- Modify: `src/app/capture.h`
- Modify: `src/app/input_mapper.h`
- Modify: `src/app/midi_config.h`, `pc98_config.h`
- Modify: `src/app/error_reporter.h`, `crash_reporter.h`
- Modify: `src/app/update_checker.h`
- Modify: `src/app/image_validator.h`
- Modify: All corresponding `.cpp` files
- Modify: `include/legends_ipc/*.h` (10 name/path params)

**Approach:** Change parameter types from `const std::string&` to `std::string_view` where the function only reads the string (doesn't store it). For functions that store the string, keep `const std::string&` or accept by value.

- [ ] **Step 1: config_parser.h — change `section`, `key`, `default_val` params**
- [ ] **Step 2: Build and fix any compilation errors (callers passing temporaries, etc.)**
- [ ] **Step 3: Remaining app headers (batches of 5)**
- [ ] **Step 4: IPC headers**
- [ ] **Step 5: Full build + test suite**
- [ ] **Step 6: Commit**

```bash
git commit -m "refactor: use std::string_view for read-only string parameters (~75 sites)"
```

---

### Task 3: Link gsl-lite to PAL and Add `gsl_Expects`

**Audit ref:** Agent 7 (PAL) — not linked to gsl-lite at all; Agents 2,3,5 — most preconditions are manual `if` checks

**Files:**
- Modify: `CMakeLists.txt` (add `target_link_libraries(legends_pal PRIVATE gsl::gsl-lite-v1)`)
- Modify: All `src/pal/headless/*.cpp` files
- Modify: `src/app/save_manager.cpp`, `capture.cpp`, `input_mapper.cpp`, `ai_panel.cpp`, `config_parser.cpp`

**Approach:** Replace manual `if (!ptr) return Error` checks with `gsl_Expects(ptr != nullptr)`. Keep the early-return for cases where null is a valid "nothing to do" signal.

- [ ] **Step 1: Link gsl-lite to legends_pal in CMakeLists.txt**
- [ ] **Step 2: Add `gsl_Expects` to headless PAL implementations (~20 sites)**
- [ ] **Step 3: Add `gsl_Expects` to app layer files (~15 sites)**
- [ ] **Step 4: Full build + test suite (tests must be configured with `gsl_CONFIG_CONTRACT_VIOLATION_THROWS`)**
- [ ] **Step 5: Commit**

```bash
git commit -m "refactor: add gsl_Expects preconditions to PAL and app layers (~35 sites)"
```

---

### Task 4: Replace `static_cast` Narrowing with `gsl::narrow`

**Audit ref:** Agent 8 (SDL) — 30+ in SDL backends; Agent 3 — 15+ in app config files

**Files:**
- Modify: `src/pal/sdl2/*.cpp` and `src/pal/sdl3/*.cpp` (30+ casts)
- Modify: `src/app/ai_config.cpp`, `midi_config.cpp`, `ipx_config.cpp`, `glide_config.cpp` (15+ casts)
- Modify: `src/app/cli_parser.cpp` (2 casts)

- [ ] **Step 1: SDL backends — replace `static_cast<uint32_t>(int_val)` with `gsl::narrow<uint32_t>(int_val)`**
- [ ] **Step 2: App config files — replace `static_cast<uint16_t>(config.getInt(...))` patterns**
- [ ] **Step 3: Full build + test suite**
- [ ] **Step 4: Commit**

```bash
git commit -m "refactor: replace static_cast narrowing with gsl::narrow (~45 sites)"
```

---

### Task 5: Make Wire Format Helpers `constexpr`

**Audit ref:** Agent 5 (IPC) — 16 helpers missing constexpr, all do only bitwise ops

**Files:**
- Modify: `include/legends_ipc/wire_format.h`

- [ ] **Step 1: Add `constexpr` to all 16 read/write helpers**
- [ ] **Step 2: Add `static_assert` tests that verify constexpr evaluation**

```cpp
static_assert([] {
    std::array<uint8_t, 4> buf{};
    write_u32_le(std::span{buf}, 0x12345678u);
    return read_u32_le(std::span<const uint8_t>{buf});
}() == 0x12345678u);
```

- [ ] **Step 3: Build + test**
- [ ] **Step 4: Commit**

---

### Task 6: Replace `std::stoi`/`catch(...)` with `std::from_chars`

**Audit ref:** Agent 1 — `config_parser.cpp:97`, `cli_parser.cpp:88-100`

**Files:**
- Modify: `src/app/config_parser.cpp`
- Modify: `src/app/cli_parser.cpp`

- [ ] **Step 1: In config_parser.cpp, replace `std::stoi` with `std::from_chars`**
- [ ] **Step 2: In cli_parser.cpp, replace `std::strtoul` with `std::from_chars`**
- [ ] **Step 3: Run parser tests**
- [ ] **Step 4: Commit**

---

### Task 7: Add `std::span` to Rendering and Audio Interfaces

**Audit ref:** Agent 10 — 25+ raw pointer+size signatures in app layer

**Files:**
- Modify: `src/app/audio_mixer.h` (5 functions)
- Modify: `src/app/video_capture.h` (3 functions)
- Modify: `src/app/zmbv_codec.h` (2 functions)
- Modify: Corresponding `.cpp` files

- [ ] **Step 1: AudioMixer — change all pointer+count to `std::span`**
- [ ] **Step 2: VideoCapture — change `addVideoFrame(uint8_t*)` to `std::span<const uint8_t>`**
- [ ] **Step 3: ZMBVCodec — change encode/decode to `std::span`**
- [ ] **Step 4: Update callers**
- [ ] **Step 5: Build + test**
- [ ] **Step 6: Commit**

---

### Task 8: Extract Shared Overlay Rendering Code

**Audit ref:** Agent 7, 10 — ~500 lines of CP437 rendering duplicated across 5 files

**Files:**
- Create: `src/app/overlay_render.h`
- Create: `src/app/overlay_render.cpp`
- Modify: `src/app/menu_system.cpp` (remove inline drawChar/drawString/darkenRect/fillRect)
- Modify: `src/app/ai_panel.cpp`
- Modify: `src/app/mapper_ui.cpp`
- Modify: `src/app/save_browser.cpp`
- Modify: `src/app/perf_overlay.h`
- Modify: `CMakeLists.txt` (add overlay_render.cpp)

- [ ] **Step 1: Create `overlay_render.h` with shared function declarations**

Use `std::span<uint8_t>` for buffer parameters with `gsl_Expects` contracts.

- [ ] **Step 2: Create `overlay_render.cpp` with the canonical implementation**
- [ ] **Step 3: Migrate menu_system.cpp first (largest user)**
- [ ] **Step 4: Migrate remaining 4 files**
- [ ] **Step 5: Build + full test suite**
- [ ] **Step 6: Commit**

```bash
git commit -m "refactor: extract shared overlay rendering to overlay_render.h/cpp (~500 lines dedup)"
```

---

### Task 9: Add `static_assert(is_always_lock_free)` for SHM Atomics

**Audit ref:** Agent 5 (IPC) — lock-free design assumed but not validated

**Files:**
- Modify: `include/legends_ipc/framebuffer_shm.h`
- Modify: `include/legends_ipc/audio_ring.h`

- [ ] **Step 1: Add static_asserts**

```cpp
static_assert(std::atomic<uint64_t>::is_always_lock_free, "Framebuffer SHM requires lock-free uint64_t atomics");
static_assert(std::atomic<uint32_t>::is_always_lock_free, "Audio ring requires lock-free uint32_t atomics");
```

- [ ] **Step 2: Build on all platforms**
- [ ] **Step 3: Commit**
