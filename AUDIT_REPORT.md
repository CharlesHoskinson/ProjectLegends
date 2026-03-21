# Project Legends: Comprehensive Codebase Audit Report

**Date:** 2026-03-20
**Auditors:** 12 parallel agents in isolated git worktrees
**Scope:** 135 source files, 117 unit tests, 34 integration tests, 4 fuzz harnesses, build system, CI pipeline, security posture, documentation, and all 220 ROADMAP requirements

---

## Executive Summary

12 agents audited the entire codebase across isolated worktrees, examining every source file, test, build config, and documentation artifact. The project is substantially built but has **critical gaps between claimed and actual completion status** that must be resolved before release. The ROADMAP overstates completion in several sections (Security, Quality Engineering, UX), while significantly understating progress in others (GPL Process Isolation).

**Key numbers:**
- 4,606 test cases across the codebase
- 8 critical bugs identified
- 6 stubs masquerading as implementations
- 7 security requirements overstated as "Done"
- ~1,190 lines of test/code boilerplate that can be eliminated
- 8 of 34 integration tests are empty stubs for critical acceptance gates

---

## 1. ROADMAP vs. Reality — What's Actually Done

### Phase Completion (Verified)

| Phase | ROADMAP Claims | Audit Finds | Delta |
|-------|---------------|-------------|-------|
| Phase -1: Engine I/O Plumbing | COMPLETE | **COMPLETE** | Accurate |
| Phase 0: Build Infrastructure | COMPLETE | **COMPLETE** | Accurate |
| Phase 1: MVP (Display/Input/Audio) | COMPLETE | **COMPLETE** | Accurate |
| Phase 2: Core Experience | COMPLETE | **COMPLETE** | Accurate |
| Phase 3: Enhanced Features | 7/14 done | **6 done, 4 partial, 3 stub** | 4 "partial" items have code written but not wired |
| Phase 4: Polish & Release | COMPLETE | **MOSTLY COMPLETE** | ErrorReporter, CrashReporter, UpdateChecker, PerfOverlay are stubs/broken |
| Section 9: Security | 17/22 done | **10 genuinely done, 7 overstated** | TLS, field limits, AI sanitization all missing despite claims |
| Section 10: Embedding API | 10/11 done | **8/11 fully done** | Step result extensibility, capability reporting bugs |
| Section 11: Ops Infrastructure | 14/16 done | **~11/16 done** | Crash reporter, update checker, LGPL linking all stubs |
| Section 12: Quality Engineering | 19/19 done | **~13/19 done** | Missing: frame cap, step error handling, DPI, debouncing |
| Section 13: UX & Accessibility | 5/11 done | **2-3/11 done** | Host key, DPI scaling, keyboard nav not found in code |
| Section 14: GPL Process Isolation | 2/16 done | **12-13/16 done** | ROADMAP massively understates -- IPC infra is substantially built |
| Section 15: Wasm Sandbox | 0/50 | **0/50** | Only a CMake option exists |

---

## 2. Critical Bugs (Must Fix Before Any Release)

| # | Issue | Location | Risk |
|---|-------|----------|------|
| 1 | **CRC-32 lookup table has duplicate rows** — indices 48-95 duplicated from 0-47 | `src/app/save_manager.cpp:42-57` | Save state integrity checks produce incorrect checksums |
| 2 | **No IPC payload size cap** — unbounded 4GB allocation from untrusted wire data | `src/legends_ipc/message_codec.cpp` | Remote DoS via crafted IPC message |
| 3 | **SDL3 AudioSink missing zero-channel validation** — division by zero in `getQueuedFrames()` | `src/pal/sdl3/audio_sink_sdl3.cpp:29` | Crash on malformed audio config |
| 4 | **SDL3 null window in mouse mode shutdown** — `SDL_SetWindowRelativeMouseMode(nullptr, false)` | `src/pal/sdl3/input_source_sdl3.cpp:36` | Undefined behavior on shutdown |
| 5 | **SDL2 volume_ data race** between main thread and audio callback thread | `src/pal/sdl2/audio_sink_sdl2.cpp:274,292` | Audio corruption / undefined behavior |
| 6 | **Dual error code systems** — negative values in `legends_embed.h`, positive in `ffi_core.h` | Both headers in same TU | Inconsistent error reporting across code paths |
| 7 | **Proxy sentinel handle** — `reinterpret_cast<legends_handle>(1)` returned as valid handle | `src/legends_proxy/proxy_api.cpp` | Crash if any code dereferences the handle |
| 8 | **Config parser field limits not enforced** despite being marked "Done" (REQ-SEC-014) | `src/app/config_parser.cpp` | Memory exhaustion from adversarial config files |

---

## 3. Stubs Masquerading as Implementations

These components appear in the build and are referenced as "implemented" but contain no functional code:

| Component | What It Claims | Reality |
|-----------|---------------|---------|
| **ErrorReporter** | Error collection & user display | All methods are no-ops |
| **CrashReporter** | Crash dump generation/reporting | All methods are no-ops |
| **UpdateChecker** | Version checking against releases | JSON parsing is stub; Linux/macOS fetchers are stubs |
| **PerfOverlay** | FPS/metrics display overlay | Font data is zero-initialized — renders solid white blocks (unreadable) |
| **AI HTTP Client** | HTTP transport to Anthropic API | `start()` sets a flag but never creates a thread or makes HTTP calls |
| **MapperUI** | Key remapping via UI | `commitRemaps()` is never called — all remaps discarded on close |
| **ssim.cpp** | SSIM image quality comparison | Single line: `// Stub -- not yet implemented` |
| **protocol.cpp** (IPC) | High-level IPC protocol state machine | Single line: `// Stub -- not yet implemented` |

---

## 4. Security Gaps (Overstated as "Done" in ROADMAP)

| REQ | Claimed Status | Reality | Risk |
|-----|---------------|---------|------|
| REQ-SEC-005 (TLS verification) | Done | HTTP client has **no transport layer** — no TLS code exists anywhere | MITM / API key exfiltration |
| REQ-SEC-014 (config field limits) | Done | **Zero length enforcement** — uses unbounded `std::string` | Memory exhaustion |
| REQ-SEC-008 (AI response sanitization) | Done | **Not implemented** — `addResponse()` accepts raw text | Low risk currently (CP437 rendering), but no defense-in-depth |
| REQ-SEC-018 (prompt injection separation) | Done | `formatScreenContext()` exists but **is not called** — screen text embedded directly in prompt | Prompt injection from malicious DOS programs |
| REQ-SEC-016 (image depth/cycle limits) | Done | `kMaxDirectoryDepth=32` declared but **never checked** | Stack exhaustion from crafted disk images |
| REQ-SEC-006 (API key storage) | Done | No detection/rejection of raw `api_key=sk-...` in config | Users accidentally commit API keys |
| REQ-SEC-013 (CWD config warning) | Done | Warning exists but **cannot be disabled** via config flag | Incomplete control |

---

## 5. Phase 3 Enhanced Features — Detailed Status

| REQ ID | Feature | Status | What Exists | What's Missing | Effort |
|--------|---------|--------|-------------|---------------|--------|
| REQ-SHADER-001/002 | OpenGL Shaders | **PARTIAL** | Complete `ShaderRenderer` class, 5 GLSL presets | `renderFrame()` never creates GL context or calls shader pipeline | M |
| REQ-AI-001 | AI Panel | **DONE** | Full chat UI, keyboard input, word wrap, streaming | HTTP transport is a stub (see above) | - |
| REQ-AI-002 | AI Screen Context | **DONE** | CP437-to-UTF-8, structured prompt formatting | - | - |
| REQ-AI-003 | AI Configuration | **DONE** | Full .conf [ai] section, privacy mode, env key | - | - |
| REQ-PRINT-001 | Printer Emulation | **PARTIAL** | PrinterManager + engine LPT1 code | End-to-end data path untested, PDF rendering unconfirmed | M |
| REQ-MIDI-001 | MIDI Output | **DONE** | Config -> engine -> MPU-401, audio mixing | - | - |
| REQ-TTF-001 | TrueType Fonts | **PARTIAL** | Full stb_truetype renderer with glyph cache | `renderCell()` never called; engine bridge is TODO stub | S |
| REQ-FULLSCREEN-001 | Fullscreen Toggle | **DONE** | Alt+Enter, menu toggle, all 3 PAL backends | - | - |
| REQ-JOYSTICK-001 | Joystick Support | **PARTIAL** | Full axis/button mapping with deadzone | `legends_joystick_event()` discards all values (TODO stub) | S |
| REQ-NET-001 | IPX Networking | **STUB** | Config + engine UDP code (inherited from DOSBox-X) | Never validated end-to-end, no error UX | L |
| REQ-HW-001 | 3dfx/Glide | **STUB** | Config parsing only | No Glide-to-OpenGL translation layer exists | XL |
| REQ-HW-002 | NEC PC-98 | **STUB** | Config parsing only | No PC-98 memory map, GDC, text VRAM, or OPNA audio | XL |
| REQ-AUDIO-003 | FluidSynth/MUNT | **DONE** | Both libraries compiled, MIDI audio mixed into pipeline | - | - |

---

## 6. Integration Test Coverage Gaps

### 8 Empty Stubs (Critical Acceptance Criteria with Zero Coverage)

| Stub File | Maps To | Impact |
|-----------|---------|--------|
| `test_boot_to_prompt.cpp` | REQ-TEST-002 | **Core acceptance gate** — can't verify the app boots |
| `test_golden_visual.cpp` | REQ-TEST-004 | **Gate G1** — can't verify framebuffer correctness |
| `test_replay_determinism.cpp` | REQ-TEST-006 | Deterministic replay verification |
| `test_cross_platform_smoke.cpp` | REQ-TEST-007 | Cross-platform baseline |
| `test_save_state_compat.cpp` | REQ-TEST-011 | Forward compatibility of save states |
| `test_pairwise_config.cpp` | REQ-QA-008 | Configuration combination testing |
| `test_frame_timing.cpp` | REQ-THROTTLE-001 | Frame pacing verification |
| `test_visual_regression.cpp` | REQ-QA-019 | SSIM-based visual regression |

### Additional Coverage Gaps

- **IPC integration test is DISABLED** — zero active coverage for GPL process isolation
- **No integration tests for any Phase 3 feature** (shaders, AI panel, joystick, etc.)
- **No tests for**: window resize/aspect ratio, mouse capture toggle, menu system, screenshot capture, clipboard paste, block device mounting, path confinement, readonly mounts
- **Missing fuzz targets**: IPX packet parser, IPC message deserializer, shader file parser
- **`fuzz_config_parser.cpp` exists but has no CMake target** — CI references it but it can't build
- **Platform gaps**: soak test RSS monitoring returns 0 on Windows/macOS

---

## 7. Code Quality Findings

### src/app/ (Application Shell)

- **Code duplication**: CP437 rendering functions (`drawChar`, `drawString`, `darkenRect`, `fillRect`) copy-pasted across 5 files (~500 lines)
- **Menu system**: `render()` and `renderBar()` share ~150 lines of near-identical dropdown code
- **Per-frame allocation**: `pumpAudio()` allocates `std::vector<int16_t>` for MIDI every frame
- **file_logger.cpp**: Windows UTF-8→wstring conversion broken for non-ASCII paths (`std::wstring(begin, end)` instead of `MultiByteToWideChar`)
- **Crash autosave handler**: Calls `saveToSlot()` from signal handler — async-signal-unsafe (heap alloc, mutex, filesystem I/O)
- **AVI frame count**: Always written as 0 in header — some players will reject
- **AI panel**: `handleTextInput()` only accepts ASCII 0x20-0x7E, silently drops accented characters
- **IPX config**: No hostname/IP validation — arbitrary strings passed to network connect

### src/legends/ (Core Embedding API)

- **Strengths**: Comprehensive exception boundary, thread-affinity enforcement, reentrancy guard, single-instance CAS, robust save state validation, portable wire serialization
- **Dual error codes**: `legends_embed.h` (negative) vs `ffi_core.h` (positive) — fragile collision
- **Video capture/joystick/TTF stubs return `LEGENDS_OK`** — callers believe operations succeeded
- **`legends_force_destroy` bypasses thread check intent** — returns WRONG_THREAD from non-owner

### src/legends_ipc/ (IPC Layer)

- **Strengths**: Clean wire format, RAII-correct, atomic double-buffering, correct SPSC ring buffer
- **No payload size validation** — `try_decode()` accepts `payload_size = 0xFFFFFFFF`
- **Mount path truncated at 255 bytes** (`uint8_t path_len`) — Windows paths can reach 32K
- **Framebuffer torn read potential** — non-atomic width/height between active_buffer flip
- **No message sequence correlation** — out-of-order responses silently accepted
- **POSIX SHM objects never unlinked** — leaked in `/dev/shm`
- **No reconnection logic** — broken pipe = permanent failure

### src/legends_proxy/ (Proxy Layer)

- **Sentinel handle value 1** — crash if dereferenced
- **`legends_key_event_ext` loses extended flag** — arrow keys broken in IPC mode
- **`legends_capture_rgb` always passes `last_index=0`** — defeats dirty-tracking
- **`crash_handler.restart()` spawns process but doesn't reconnect IPC**
- **`connected_` is not atomic** — data race with `connect()`/`disconnect()`

### src/pal/ (Platform Abstraction Layer)

- **Strengths**: Clean pure-virtual interfaces, RAII throughout, no raw new/delete
- **SDL2 `getTicksMs()`**: 32-bit subtraction wraps after ~49 days
- **SDL3 `unlockSurface()`**: Triggers full present on every unlock (no batching)
- **SDL3 backpressure**: Clears ALL queued audio instead of minimum needed
- **`setVsync()` is a no-op** in both SDL2 and SDL3 backends
- **InputEvent anonymous-struct pragma** only covers Clang, not GCC
- **Engine host**: drops oversized messages silently, has no signal handler, `g_handle` is a global singleton

---

## 8. Build System and CI Findings

### CMake

- **Strengths**: Modern target-based, C++23 per-target, two-tier warning strategy, FetchContent with pinning
- **Global `add_compile_options()`** leaks warnings/hardening into FetchContent dependencies (SDL3, GoogleTest)
- **Bare `include_directories()`** in engine/CMakeLists.txt (line 149) — directory-scope pollution
- **Duplicated source lists** — `src/app/*.cpp` listed in both `project_legends` and `legends_unit_tests`
- **No `CMakePresets.json`** — developers must memorize complex option combinations
- **`_FORTIFY_SOURCE=2` applied at `-O0`** — GCC will warn
- **No `TIMEOUT` on unit test discovery** — tests can hang indefinitely
- **GoogleTest declared twice** (root and engine) — version drift risk

### CI Pipeline

- **Strengths**: 14+ jobs, 3 platforms, 4 sanitizers, TLA+ model checking, fuzz testing, clang-tidy, code coverage
- **No `LEGENDS_USE_IPC=ON` CI job** — entire IPC architecture never tested in CI
- **No Debug build CI job** — assertions disabled in Release
- **No macOS sanitizer builds**
- **No benchmark regression tracking**
- **Dependency scanning non-blocking** (`continue-on-error: true`)
- **SDL2 backend never tested** in main CI
- **`pal-ci.yml` builds SDL3 from `main` branch** instead of pinned tag
- **No ARM/aarch64 builds**

### Packaging

- **No NSIS customization** — Windows installer would be unprofessional
- **No macOS code signing** — Gatekeeper will block unsigned DMGs
- **`legends_ipc` and `legends_proxy` not installable** — not in install targets
- **`VerifyGPLIsolation.cmake` references `project_legends` without guard** — fails in headless-only builds

---

## 9. Documentation Assessment

### Current State (Strengths)

- **63 markdown files** covering architecture, requirements, TLA+ specs, threat model, contract gates
- **6,451 Doxygen annotations** across public headers (excellent API docs)
- **Formal EARS requirements** with traceability to tests and TLA+ specs
- **Only 11 project-specific TODOs** — codebase is remarkably clean
- **ROADMAP is 3,800+ lines** with risk register (32 risks) and verification matrix

### Missing for Release

| Document | Priority | Effort |
|----------|----------|--------|
| `CONTRIBUTING.md` — contributor guide | High | S |
| `CHANGELOG.md` — user-facing release notes | High | S |
| Project-level `Doxyfile` to render existing annotations | High | S |
| User getting-started guide (install, configure, run games) | High | M |
| Fix `wasm.md` reference in README (doesn't exist) | Low | S |

---

## 10. Test Simplification and Boilerplate Reduction Plan

### Current State

- **4,606 test cases** across the codebase
- **Zero shared test helpers** under `tests/` (no `.h` files at all)
- **~390 lines of duplicated fixture boilerplate** across 10 patterns
- **~500 lines of duplicated rendering code** across 5 production files
- **`test_legends_embed.cpp`** is a 2,652-line monolith with 12 fixture classes
- **Production sources recompiled** into test target instead of linking a library
- **Temp directory cleanup is not exception-safe** — assertions that fail leak dirs

### Step 1: Create `tests/unit/test_utils/` (3 shared headers)

**`temp_file_fixture.h`**
- `TempFileFixture` base class with `writeTempFile()` + auto-cleanup in TearDown
- `ScopedTempDir` RAII class (constructor creates, destructor removes)
- Consumers: `test_config_parser`, `test_glide_config`, `test_ipx_config`, `test_pc98_config`, `test_input_mapper`, `test_capture`, `test_save_manager`, `test_portable_mode`, `test_video_capture`, `test_mount_manager`
- **Saves ~155 lines**, fixes temp dir leak-on-failure bug

**`pal_headless_fixture.h`**
- `PalHeadlessFixture` with `Platform::shutdown()/initialize(Headless)` in SetUp/TearDown
- Consumers: `test_pal_window`, `test_pal_context`, `test_pal_audio_sink`, `test_pal_input_source`, `test_pal_host_clock`, `test_pal_platform`
- **Saves ~60 lines**

**`ipc_test_helpers.h`**
- `ipc_test_unique_name()` (cross-platform PID+counter name generation)
- `SKIP_IF_NO_SHM(result)` macro
- `makeShortLivedSpawnConfig()` / `makeLongRunningSpawnConfig()`
- Consumers: `test_ipc_shared_memory`, `test_ipc_framebuffer_shm`, `test_ipc_audio_ring`, `test_ipc_control_channel`, `test_heartbeat`, `test_proxy_connection`, `test_crash_handler`, `test_engine_spawner`
- **Saves ~65 lines**

### Step 2: Create `tests/integration/test_utils/integration_fixture.h`

- `LegendsIntegrationTest` — standard engine + headless PAL (replaces 15+ copies of identical SetUp/TearDown)
- `LegendsConfiguredTest` — engine with `deterministic=1`
- `LegendsWarmupTest` — engine with N warmup frames
- `PalOnlyTest` — headless PAL without engine
- Shared helpers: `save_state()`, `get_hash()`, `capture_screen_chars()`, `stepFrames()`
- **Saves ~200 lines** across integration tests

### Step 3: Split the monoliths

- Split `test_legends_embed.cpp` (2,652 lines, 165 tests) into 5+ files by fixture class: lifecycle, stepping, capture, input, save state, security, determinism, reentrancy
- Extract `LegendsInstanceFixture` base class shared by 9 internal fixtures
- **Saves ~100 lines** and dramatically improves compile time for incremental changes

### Step 4: Build system improvements

- Create `legends_app` intermediate STATIC library target
- Link `legends_unit_tests` against `legends_app` instead of recompiling 40 source files
- **Halves compile time** for incremental test rebuilds
- Add `fuzz_config_parser` CMake target (source exists, no build target)
- Deduplicate GoogleTest FetchContent between root and engine
- Add `TIMEOUT` to all `gtest_discover_tests()` calls

### Step 5: Extract shared production code

- Move `drawChar()`, `drawString()`, `darkenRect()`, `fillRect()` from `menu_system.cpp`, `ai_panel.cpp`, `mapper_ui.cpp`, `save_browser.cpp`, `perf_overlay.h` into shared `overlay_render.h/cpp`
- **Saves ~500 lines** of production code duplication

### Estimated Total Savings

| Category | Lines Saved |
|----------|-------------|
| Unit test fixture extraction | ~390 |
| Integration fixture extraction | ~200 |
| Monolith split + base class | ~100 |
| Production code dedup (rendering) | ~500 |
| Build time reduction | ~50% for incremental test rebuilds |
| **Total** | **~1,190 lines + major build speedup** |

---

## 11. Release A Minimum Viable Checklist

Based on the ROADMAP's own gates (G1-G5) and the audit findings:

| Gate | Status | Blocker |
|------|--------|---------|
| **G1** (Framebuffer correctness) | Code complete | Golden visual test is a stub |
| **G2** (Audio correctness) | Code complete | Spectral test exists and runs |
| **G3** (Compatibility corpus) | Not testable | No compatibility corpus testing infrastructure |
| **G4** (Installer smoke) | Partially ready | CPack configured but no NSIS customization, no macOS signing |
| **G5** (Security baseline) | Partially ready | Threat model done, but 7 REQ-SEC items overstated |

---

## 12. Items Safely Deferrable to Release B

| Feature | Current Status | Why Defer |
|---------|---------------|-----------|
| Glide emulation (REQ-HW-001) | Config-only stub | XL effort — needs full Glide-to-OpenGL translation layer |
| PC-98 architecture (REQ-HW-002) | Config-only stub | XL effort — needs memory map, GDC, text VRAM, OPNA audio |
| IPX network security (REQ-SEC-001/002) | Not implemented | Release B networking feature |
| Shader/SoundFont file validation (REQ-SEC-038/039) | Not implemented | Release B content validation |
| Wasm Sandbox (Section 15) | 0/50 requirements | Not on Release A critical path |
| Command palette, settings dialog, per-game profiles | Not implemented | Release B UX features |
| First-run wizard, drag-and-drop | Not implemented | Release B UX features |
| Hung guest detection (REQ-UX-011) | Not implemented | Release B reliability |

---

## 13. Top 10 Priorities Before Tagging Release A

| Priority | Action | Effort | Impact |
|----------|--------|--------|--------|
| 1 | **Fix CRC-32 table** in `save_manager.cpp` | S | Data integrity at risk |
| 2 | **Add IPC payload size cap** in `MessageCodec` | S | Remote DoS vector |
| 3 | **Fix 3 SDL bugs** (null window, zero-channel, volume race) | S | Crashes / UB |
| 4 | **Enforce config parser field limits** (REQ-SEC-014) | S | Memory exhaustion |
| 5 | **Wire `formatScreenContext()`** into AI query path (REQ-SEC-018) | S | Prompt injection |
| 6 | **Implement 8 stub integration tests** | L | Gates G1/G3 can't pass |
| 7 | **Create shared test fixtures** | M | Unblocks rapid test development |
| 8 | **Wire shader renderer** into render loop | M | Most impactful Phase 3 completion |
| 9 | **Add Windows DPI manifest + suspend/resume frame cap** | S | Quality on Windows |
| 10 | **Create `CONTRIBUTING.md` + `CHANGELOG.md`** | S | Release documentation |

---

## Appendix A: Agent Assignment Matrix

| Agent # | Focus Area | Files Examined | Key Findings |
|---------|-----------|---------------|-------------|
| 1 | Phase 3 Features | 14 REQs, ~30 source files | 6 done, 4 partial (code exists but unwired), 3 stubs |
| 2 | Security Hardening | 22 REQ-SECs, security docs | 10 genuinely done, 7 overstated |
| 3 | Embedding API + Ops + GPL | Sections 10, 11, 14 | API mostly done; crash/update stubs; IPC underreported |
| 4 | Quality Eng + UX + Wasm | Sections 12, 13, 15 | Multiple QA gaps; UX overstated; Wasm 0/50 |
| 5 | Unit Test Boilerplate | 22 test files in depth | ~390 lines duplicated; zero shared helpers |
| 6 | Integration Test Quality | All 34 integration tests | 8 stubs; IPC disabled; 15+ files share boilerplate |
| 7 | src/app Code Quality | All 78 files in src/app/ | CRC-32 bug; 6 stubs; CP437 code duplication |
| 8 | Legends Core + IPC | src/legends/, legends_ipc/, legends_proxy/ | Payload cap missing; dual error codes; proxy bugs |
| 9 | PAL + Engine Host | src/pal/, src/engine_host/, src/libs/ | 3 SDL bugs; no signal handler; ZMBV stub |
| 10 | Build System + CI | CMakeLists.txt, CI workflows | No IPC CI; global compile options leak; no presets |
| 11 | Test Infrastructure | All test infra, fixtures, build | 4,606 tests; monolith files; prod sources recompiled |
| 12 | Documentation + Comments | 63 docs, all headers, TODO audit | Excellent docs; 11 project TODOs; missing CONTRIBUTING/CHANGELOG |

---

## 14. C++23 Best Practices & gsl-lite Compliance Audit

**Methodology:** 10 additional agents audited every source file against C++23 best practices and gsl-lite (https://github.com/gsl-lite/gsl-lite) usage patterns. Each agent ran in an isolated worktree.

### 14.1 Executive Summary

The codebase is **clean C++17-era code that has not broadly adopted C++23 idioms**. The IPC layer (`legends_ipc/`) is the standout — exemplary `std::expected` usage throughout. The rest of the codebase (application shell, PAL, core embed API) lags significantly behind, relying on `bool` returns, raw pointer+size pairs, and zero `[[nodiscard]]` annotations.

**gsl-lite is linked but barely used.** Only 3 of ~40 source file families include `gsl.hpp`. The contracts infrastructure exists (`include/legends/contracts.hpp`) but the core embed API — 3,200 lines — uses zero gsl constructs.

### 14.2 Aggregate Metrics

| Metric | Count | Assessment |
|--------|-------|------------|
| `[[nodiscard]]` usage | **0 of 353** value-returning functions across all headers | **CRITICAL GAP** — 0% compliance |
| `std::expected` usage | **Good in IPC/proxy/engine_host**; zero in app/, pal/, legends/ | **SPLIT** — two tiers of modernity |
| `std::string_view` parameters | **0 of 75** read-only string params across all C++ headers | **CRITICAL GAP** — 0% compliance |
| `std::span` parameters | **115 in IPC** (excellent); **0 of 23** in PAL/app | **SPLIT** — 83% overall but 0% outside IPC |
| `gsl_Expects` usage | **12 in wire_format** + ~14 documented but unenforced in app | **LOW** — 26% of opportunities |
| `gsl_Ensures` usage | **0** across entire codebase | **ABSENT** |
| `gsl::not_null` usage | **0** | **ABSENT** — many non-owning raw pointers |
| `gsl::narrow`/`narrow_cast` | **0** vs **100+** raw `static_cast` narrowing conversions | **ABSENT** |
| `gsl::finally` | **0** — manual cleanup in 13+ sites | **ABSENT** |
| `constexpr` items | **151 of 166** data constants (91%) | **GOOD** on data; zero on pure functions |
| `std::ranges` usage | **0** across entire codebase | **ABSENT** — 30+ raw loops could benefit |
| Concepts usage | **0** | **N/A** — no template sites to constrain |
| Monadic chaining (`and_then`/`transform`) | **0** despite `std::expected` being used | **MISSED OPPORTUNITY** |
| Default member initializers | **~83%** of structs/classes | **GOOD** |
| Include guards | **100%** (mixed `#pragma once` / `#ifndef`) | **EXCELLENT** |
| `using namespace` in headers | **25 violations** in `include/legends/` forwarding headers | **MODERATE** concern |

### 14.3 Per-Layer Compliance Scores

| Layer | Score | Strengths | Weaknesses |
|-------|-------|-----------|------------|
| **IPC Layer** (`legends_ipc/`) | **7/10** | Exemplary `std::expected`, correct `std::span`, `gsl_Expects` on serialize, RAII move semantics | Missing `constexpr` on 16 wire helpers, missing `[[nodiscard]]`, no `gsl_Ensures` |
| **Engine Host** (`engine_host/`) | **6/10** | Consistent `std::expected`, `std::span` on dispatch | Zero gsl-lite, zero `[[nodiscard]]`, no monadic chaining |
| **Proxy** (`legends_proxy/`) | **5/10** | Uses `std::expected` for connections | Macro-based code gen, data race on `connected_`, no gsl |
| **Core Embed API** (`legends/`) | **3/10** | Good `constexpr` tables, `static_assert` on ABI structs, `std::format` in ffi.h | Zero gsl, zero expected, zero span, macro error handling, raw `delete` in 8 places |
| **App Shell** (`app/`) | **2/10** | `constexpr` layout constants, `std::move` on handlers | Zero `[[nodiscard]]`, zero expected, zero string_view, zero span, zero gsl (except 3 files) |
| **PAL Layer** (`pal/`) | **2/10** | Excellent `constexpr` enum helpers | Zero everything else — error codes, no nodiscard, no span, not even linked to gsl-lite |
| **SDL Backends** (`pal/sdl2/`, `pal/sdl3/`) | **2/10** | SDL3 is more modern than SDL2 | 30+ raw `static_cast` narrows, no RAII for SDL handles, no gsl |

### 14.4 Top 20 C++23/gsl-lite Improvements (by Impact)

| # | Action | Files | Effort | Impact |
|---|--------|-------|--------|--------|
| 1 | Add `[[nodiscard]]` to all value-returning functions | All headers (~200 sites) | S | Prevents silent error-discard bugs |
| 2 | Migrate PAL interfaces from `pal::Result` to `std::expected` | 7 PAL headers + all backends | L | Brings PAL in line with IPC layer |
| 3 | Replace `const std::string&` with `std::string_view` on read-only params | ~50 signatures across app/ | M | Eliminates unnecessary heap allocations |
| 4 | Replace raw `pointer+size` with `std::span` in app/pal interfaces | ~25 signatures | M | Prevents buffer overruns |
| 5 | Add `gsl_Expects` to replace manual `if (!ptr) return` checks | ~40 sites across all layers | S | Explicit contracts, fail-fast in debug |
| 6 | Replace `static_cast` narrowing with `gsl::narrow` | ~100 sites across SDL/app/IPC | M | Runtime-checked narrowing |
| 7 | Link gsl-lite to `legends_pal` (`target_link_libraries PRIVATE`) | CMakeLists.txt | S | Enables gsl usage in PAL implementations |
| 8 | Make 16 wire format helpers `constexpr` | `wire_format.h` | S | Compile-time serialization validation |
| 9 | Replace `std::stoi` + `catch(...)` with `std::from_chars` | `config_parser.cpp`, `cli_parser.cpp` | S | No exceptions for expected failures |
| 10 | Use `gsl::finally` for cleanup patterns | `legends_embed_api.cpp` (6 sites), `control_channel_win.cpp` (6 sites), `platform_dirs.cpp` (1 site) | S | Exception-safe resource cleanup |
| 11 | Wrap SDL handles in `unique_ptr` with custom deleters | All SDL backend files | M | RAII for SDL_Window, Renderer, Texture, AudioStream |
| 12 | Add `gsl::not_null` on non-owning pointer members | `ai_panel.h`, `menu_system.h`, `mapper_ui.h`, `save_browser.h`, `heartbeat.h`, `crash_handler.h` | S | Documents and enforces non-null invariants |
| 13 | Replace `std::transform` with `std::ranges::transform` | `mount_manager.cpp`, `midi_config.cpp`, `image_validator.cpp`, `menu_system.cpp` | S | Modern ranges idiom |
| 14 | Extract duplicated rendering helpers to `overlay_render.h` | `menu_system.cpp`, `ai_panel.cpp`, `mapper_ui.cpp`, `save_browser.cpp`, `perf_overlay.h` | S | Eliminates ~500 lines of duplication |
| 15 | Add `std::expected` to `ConfigParser::loadFile`, `CLIOptions::parse`, `SaveManager::saveToSlot/loadFromSlot` | 4 files | M | Error context instead of bare `bool` |
| 16 | Make lookup tables `constexpr` | `scancode_map.cpp`, `shader_presets.cpp`, `legends_embed_api.cpp` CRC table | S | Compile-time initialization guarantee |
| 17 | Add `gsl_Ensures` postconditions on factory methods | IPC `create()`/`open()`, PAL factories | S | Validates construction invariants |
| 18 | Replace macro error handling with gsl contracts | `legends_embed_api.cpp` `LEGENDS_REQUIRE`/`LEGENDS_ERROR` | M | Typed contracts vs. C macros |
| 19 | Use monadic chaining (`and_then`/`transform`) on existing `std::expected` | proxy_connection, engine_dispatcher | S | More declarative error handling |
| 20 | Add `static_assert(std::atomic<T>::is_always_lock_free)` for SHM atomics | `framebuffer_shm.h`, `audio_ring.h` | S | Validates lock-free design assumption |

### 14.5 Bugs Found During C++23 Audit

These were discovered as a side-effect of the modernization review:

| # | Bug | Location | Severity |
|---|-----|----------|----------|
| 1 | **`CoTaskMemFree` memory leak** — skipped when `WideCharToMultiByte` returns 0 | `platform_dirs.cpp:37-38` | HIGH |
| 2 | **Broken UTF-8→wstring** — `std::wstring(begin, end)` only works for ASCII | `file_logger.cpp:259` | HIGH |
| 3 | **UTF-8 truncation** — `resize(max_chars)` can split multi-byte sequences | `ai_screen_context.cpp:281` | MEDIUM |
| 4 | **SDL2 ring buffer single-writer violation** — `discard()` writes `read_pos_` from producer thread | `audio_sink_sdl2.cpp` `AudioRingBuffer::discard()` | HIGH |
| 5 | **`crash_handler.restart()` drops spawned process** — `EngineProcess` destroyed immediately | `crash_handler.cpp:35-38` | HIGH |
| 6 | **`connected_` data race** — plain `bool` read without mutex | `proxy_connection.h:62` | HIGH |
| 7 | **`setVsync` skips `created_` check** — inconsistent with other window methods | `window_headless.cpp:135` | LOW |
| 8 | **`setVolume` skips `open_` check** — inconsistent with other audio methods | `audio_sink_headless.cpp:140` | LOW |
| 9 | **Audio overflow** — `frames_to_write * channels` can overflow uint32_t | `audio_sink_headless.cpp:97` | MEDIUM |

### 14.6 Model Files (Best to Worst Compliance)

**Best:**
1. `include/legends_ipc/wire_format.h` — gsl_Expects, std::span, correct atomics (missing constexpr)
2. `src/legends_ipc/messages.cpp` — gsl_Expects on all serialize methods, std::expected returns
3. `src/engine_host/engine_dispatcher.h` — std::expected, std::span, clean separation
4. `src/app/mount_manager.h` — 6 gsl_Expects, std::optional, enum class

**Worst:**
1. `src/pal/` — not even linked to gsl-lite, zero modern patterns
2. `src/app/ai_panel.cpp` — large file, raw loops, raw pointers, no gsl, no nodiscard
3. `src/app/config_parser.cpp` — `std::stoi` with catch(...), no string_view, no expected
4. `src/app/perf_overlay.h` — dead code, zero contracts, inline implementation

### 14.7 Agent Assignment Matrix (C++23 Audit)

| Agent # | Focus Area | Files | Key Finding |
|---------|-----------|-------|-------------|
| 1 | App Core | application, action_bus, config_parser, cli_parser, menu_system | Zero C++23 adoption; `std::stoi` exceptions as control flow |
| 2 | App Features | save_manager, capture, input_mapper, ai_panel, mount_manager, video_capture | Only 2/7 files use gsl; raw `FILE*` RAII violation |
| 3 | Config & Utilities | 14 config/utility files | 3 bugs found; zero gsl/expected/nodiscard across all 14 |
| 4 | Legends Core API | legends_embed_api.cpp + 9 internal headers | Zero gsl despite contracts.hpp existing; macro error handling |
| 5 | IPC Layer | 22 IPC files | Exemplary std::expected; 16 wire helpers need constexpr |
| 6 | Proxy + Engine Host | 14 proxy/host files | Good expected usage; connected_ data race; restart() bug |
| 7 | PAL Interfaces + Headless | 13 PAL files | 3.8/10 score; not linked to gsl-lite at all |
| 8 | SDL2 + SDL3 Backends | 12 SDL files | 30+ narrowing casts; SDL2 ring buffer race; SDL3 more modern |
| 9 | Public Headers | 83 headers across include/ and src/app/*.h | 0/353 [[nodiscard]]; 0/75 string_view; 25 using-namespace violations; 91% constexpr data |
| 10 | Rendering & Misc | 16 renderer/mixer/mapper files | Zero nodiscard/expected/string_view; 500 lines duplicated rendering code |
