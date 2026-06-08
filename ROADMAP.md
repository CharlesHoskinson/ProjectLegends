# Project Legends: Interactive Binary Roadmap

**Format:** EARS (Easy Approach to Requirements Specification) + OpenSpec
**Version:** 4.2.0
**Date:** 2026-02-27
**Status:** In Progress — Phases -1, 0, 1, 4 COMPLETE; Phases 2, 3 PARTIAL
**Author:** Charles Hoskinson and Contributors

---

## Table of Contents

1. [Executive Summary](#1-executive-summary)
2. [Architecture Overview](#2-architecture-overview)
3. [Phase -1: Engine I/O Plumbing](#3-phase--1-engine-io-plumbing)
4. [Phase 0: Build Infrastructure](#4-phase-0-build-infrastructure)
5. [Phase 1: MVP — Display, Input, Audio](#5-phase-1-mvp--display-input-audio)
6. [Phase 2: Core Experience](#6-phase-2-core-experience)
7. [Phase 3: Enhanced Features](#7-phase-3-enhanced-features)
8. [Phase 4: Polish & Release](#8-phase-4-polish--release)
9. [Security Hardening](#9-security-hardening)
10. [Embedding API Completeness](#10-embedding-api-completeness)
11. [Operational Infrastructure](#11-operational-infrastructure)
12. [Quality Engineering](#12-quality-engineering)
13. [User Experience & Accessibility](#13-user-experience--accessibility)
14. [GPL v2 Process Isolation](#14-gpl-v2-process-isolation)
15. [Wasm Sandbox](#15-wasm-sandbox)
16. [Full EARS Requirements Catalogue](#16-full-ears-requirements-catalogue)
17. [Risk Register](#17-risk-register)
18. [Verification Matrix](#18-verification-matrix)
19. [Appendices](#19-appendices)

---

## 1. Executive Summary

### 1.1 What We Are Building

A **shipping SDL3 desktop binary** (`project_legends`) that wraps the existing
ProjectLegends embeddable x86 emulation framework into a complete, user-facing
DOS emulator — matching and eventually exceeding DOSBox-X's interactive feature
set.

### 1.2 Why

ProjectLegends already has:

- A **complete DOSBox-X engine** compiled as a static library (`aibox_core`)
- A **stable C ABI** (`legends_embed.h` — 22+ functions covering lifecycle,
  stepping, capture, input injection, save/load, and introspection)
- A **fully implemented PAL** (Platform Abstraction Layer) with SDL3 backend
  (6 source files: window, context, audio sink, host clock, input source,
  platform factory)

What is **missing** is:

1. **Engine I/O plumbing** — the bridge between the engine's internal
   framebuffer/audio and the Legends capture APIs currently uses synthetic test
   data, not real engine output (see [Phase -1](#3-phase--1-engine-io-plumbing))
2. **The application shell** — `main()` entry point, run loop wiring PAL to
   engine, and every user-facing feature (menus, config, key mapper, save-state
   UI, AI panel) needed to ship an interactive binary

### 1.3 Design Decisions (Confirmed)

| Decision | Choice | Rationale |
|----------|--------|-----------|
| GUI framework | Native SDL3 menus + custom fallback overlay | No external GUI dependency; works on all platforms |
| Menu abstraction | App-layer only (intentionally outside PAL) | PAL provides platform services; menus are application-level UI policy. No `IMenuHost` in PAL. |
| Platform targets | Windows, Linux, macOS from day one | SDL3 abstracts platform differences; CI catches regressions |
| AI integration | Integrated AI assistant panel (opt-in, non-blocking) | Core differentiator, but must not block core emulator shipping |
| Rendering path | Software context (RGB blit) for MVP; OpenGL shaders in Phase 3 | Simplest correct path first |
| Audio model | Push-based via `IAudioSink::pushSamples()` | Matches existing SDL3 `SDL_AudioStream` backend |
| Configuration | INI-style `.conf` files (DOSBox-X compatible) | User familiarity; existing ecosystem of config files |
| Presentation ownership | Context owns present (software path); Window owns present (OpenGL path) | See [Section 2.5](#25-presentation-ownership-contract) |
| Directory policy | XDG on Linux, `%APPDATA%` on Windows, `~/Library/Application Support` on macOS | See [Appendix D](#appendix-d-platform-directory-policy) |

### 1.4 Release Strategy

The release is split into two channels to decouple core emulator stability from
differentiator features:

| Channel | Scope | Ship Gate |
|---------|-------|-----------|
| **Release A: Core Emulator** | Phases -1, 0, 1, 2, 4 (packaging/testing subset) | Gates G1–G4 pass |
| **Release B: Differentiators** | Phase 3 (AI, shaders, MIDI, printing, TTF) | Release A shipped + Phase 3 reqs pass |

### 1.5 Release Gates

| Gate | Description | Acceptance |
|------|-------------|------------|
| **G1** | Real framebuffer correctness | `legends_capture_rgb()` produces byte-accurate output verified against golden snapshots (text mode + Mode 13h) |
| **G2** | Real audio correctness | Engine produces audible audio; spectral test validates known PC speaker tone within ±5% frequency tolerance |
| **G3** | Compatibility corpus pass | Tier 1 (CLI utilities) 100% pass, Tier 2 (mode-switch apps) 90% pass, Tier 3 (games) 80% pass |
| **G4** | Installer/package smoke | Clean-VM install + launch succeeds on Windows, Linux, macOS |
| **G5** | Security baseline | Threat model documented, all Critical REQ-SEC items implemented, no unresolved Critical/High findings |

### 1.6 Success Criteria

#### Core Shippable (Release A)

The core emulator is **shippable** when all of the following are true:

1. `cmake --build . --target project_legends` produces a working binary on
   Windows, Linux, and macOS
2. The binary launches and shows a real DOS prompt (not test-pattern) in a
   resizable window
3. Keyboard input types characters at the DOS prompt
4. Audio plays correctly (e.g., PC speaker beep verified via spectral test)
5. A menu bar provides access to machine settings, save/load, and capture
6. Save and load state works from the UI (multi-slot)
7. The key mapper allows rebinding host keys to guest scancodes
8. Gates G1–G5 all pass

#### Differentiated Shippable (Release B)

Adds to Release A:

9. The AI assistant panel is accessible and functional (opt-in)
10. At least one shader preset (CRT) renders correctly via OpenGL path

---

## 2. Architecture Overview

### 2.1 Composition Diagram

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        project_legends BINARY                               │
│                                                                             │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                     Application Shell (NEW)                           │  │
│  │                                                                       │  │
│  │  main.cpp ──► Application ──► RunLoop                                 │  │
│  │                   │                │                                   │  │
│  │            ┌──────┴──────┐   ┌─────┴──────────────────────┐           │  │
│  │            │  App Modules │   │  PAL Services (owned)      │           │  │
│  │            │             │   │                              │           │  │
│  │            │ ConfigParser│   │ IWindow      ← createWindow  │          │  │
│  │            │ MenuSystem  │   │ IContext      ← createContext │          │  │
│  │            │ InputMapper │   │ IAudioSink    ← createAudioSink│        │  │
│  │            │ SaveManager │   │ IHostClock    ← createHostClock│        │  │
│  │            │ Capture     │   │ IInputSource  ← createInputSource│     │  │
│  │            │ AIPanel     │   │                              │           │  │
│  │            │ CLIParser   │   └──────────────────────────────┘           │  │
│  │            │ ActionBus   │                                             │  │
│  │            └─────────────┘                                             │  │
│  └───────────────────────────────────┬───────────────────────────────────┘  │
│                                      │ calls                                │
│                                      ▼                                      │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                  Stable C ABI  (legends_embed.h)                       │  │
│  │                                                                       │  │
│  │  legends_create / legends_destroy / legends_step_ms                    │  │
│  │  legends_capture_rgb / legends_capture_text                            │  │
│  │  legends_key_event / legends_mouse_event / legends_text_input          │  │
│  │  legends_save_state / legends_load_state                               │  │
│  │  legends_is_frame_dirty / legends_get_cursor                           │  │
│  └───────────────────────────────────┬───────────────────────────────────┘  │
│                                      │                                      │
│  ┌──────────────────┐  ┌─────────────┴─────────────┐                       │
│  │  legends_pal     │  │      legends_core          │                       │
│  │  (SDL3 backend)  │  │  (handle registry,         │                       │
│  │                  │  │   machine context,          │                       │
│  │  6 source files  │  │   API bridge)               │                       │
│  └──────────────────┘  └─────────────┬──────────────┘                       │
│                                      │                                      │
│                          ┌───────────┴───────────┐                          │
│                          │     aibox_core         │                          │
│                          │  (DOSBox-X engine)     │                          │
│                          └───────────────────────┘                          │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 2.2 The Run Loop (Critical Missing Piece)

The run loop is the heart of the interactive binary. It lives in
`Application::run()` and orchestrates all PAL services with the engine API:

```
┌──────────────────────────────────────────────────────────────┐
│                    Application::run()                         │
│                                                              │
│  while (!quit_) {                                            │
│      // ─── 1. Input ───────────────────────────────────── │
│      uint32_t n = input_source_->poll(events, MAX_EVENTS);   │
│      for (uint32_t i = 0; i < n; ++i) {                      │
│          if (events[i].type == InputEventType::WindowClose)   │
│              quit_ = true;                                    │
│          else                                                │
│              action_bus_.dispatch(events[i]);                 │
│      }                                                       │
│                                                              │
│      // ─── 2. Translate & inject ──────────────────────── │
│      //  SDL scancodes → AT Set 1 via InputMapper             │
│      //  legends_key_event(handle_, scancode, is_down)        │
│      //  legends_mouse_event(handle_, dx, dy, buttons)        │
│                                                              │
│      // ─── 3. Step engine ─────────────────────────────── │
│      legends_step_result_t result;                            │
│      legends_step_ms(handle_, frame_ms, &result);             │
│                                                              │
│      // ─── 4. Capture frame (only if dirty) ───────────── │
│      int dirty = 0;                                          │
│      legends_is_frame_dirty(handle_, &dirty);                 │
│      if (dirty) {                                            │
│          legends_capture_rgb(handle_, fb, fb_size,            │
│                              &actual, &w, &h);                │
│          // Handle resolution change (destroy/recreate ctx)   │
│          if (w != ctx_w || h != ctx_h)                        │
│              recreateContext(w, h);                            │
│          SoftwareContext sctx;                                │
│          context_->lockSurface(sctx);                         │
│          convertAndCopy(fb, sctx);  // RGB24 → surface fmt    │
│          context_->unlockSurface(); // ← presents (soft path) │
│      }                                                       │
│      // NOTE: Do NOT call window_->present() for software     │
│      // path — context_->unlockSurface() already presents.    │
│                                                              │
│      // ─── 5. Audio ──────────────────────────────────── │
│      audio_sink_->pushSamples(engine_audio_buf, frames);      │
│                                                              │
│      // ─── 6. Throttle ───────────────────────────────── │
│      uint64_t elapsed = clock_->getTicksUs() - frame_start;  │
│      if (elapsed < target_frame_us)                           │
│          clock_->sleepUs(target_frame_us - elapsed);          │
│  }                                                           │
└──────────────────────────────────────────────────────────────┘
```

### 2.3 Action Bus

All user-initiated actions (menu selections, hotkeys, CLI commands) route
through a single `ActionBus` to prevent duplicated behavior and drift:

```cpp
enum class Action {
    Quit, Pause, Resume, Reset, ToggleFullscreen,
    SaveState, LoadState, Screenshot, StartCapture, StopCapture,
    OpenMapper, OpenAIPanel, CyclesUp, CyclesDown,
    VolumeUp, VolumeDown, ToggleMute, ReleaseMouseCapture,
    // ...
};

class ActionBus {
public:
    void dispatch(Action action, int param = 0);
    void registerHandler(Action action, std::function<void(int)> handler);
};
```

Menu items, hotkeys, and CLI flags all emit `Action` values. The `Application`
class registers handlers for each action. This ensures a single source of truth
for every user-facing behavior.

### 2.4 New Files to Create

| File | Purpose |
|------|---------|
| `src/main.cpp` | Entry point — parses CLI, initializes PAL, creates `Application`, calls `run()` |
| `src/app/application.h` | `Application` class — owns PAL objects + engine handle, contains the run loop |
| `src/app/application.cpp` | `Application` implementation |
| `src/app/action_bus.h` | Centralized action dispatch (menu, hotkey, CLI → handler) |
| `src/app/action_bus.cpp` | Action bus implementation |
| `src/app/config_parser.h` | INI-style `.conf` file parser (DOSBox-X compatible format) |
| `src/app/config_parser.cpp` | Config parser implementation |
| `src/app/menu_system.h` | Native SDL3 menus with custom fallback overlay (app-layer, not PAL) |
| `src/app/menu_system.cpp` | Menu system implementation |
| `src/app/input_mapper.h` | Key/joystick remapping (SDL scancode → AT Set 1) |
| `src/app/input_mapper.cpp` | Input mapper implementation |
| `src/app/save_manager.h` | Multi-slot save state UI |
| `src/app/save_manager.cpp` | Save manager implementation |
| `src/app/capture.h` | Screenshot (PNG) and video capture (raw frames) |
| `src/app/capture.cpp` | Capture implementation |
| `src/app/ai_panel.h` | Integrated AI assistant panel (opt-in) |
| `src/app/ai_panel.cpp` | AI panel implementation |
| `src/app/cli_parser.h` | Command-line argument handling |
| `src/app/cli_parser.cpp` | CLI parser implementation |
| `src/app/platform_dirs.h` | XDG/AppData/macOS directory resolution (see Appendix D) |
| `src/app/platform_dirs.cpp` | Platform directory implementation |

### 2.5 Presentation Ownership Contract

The current SDL3 backend has a subtle coupling: `context_->unlockSurface()`
already calls `SDL_RenderPresent()` internally
(`src/pal/sdl3/context_sdl3.cpp:159-162`), while `window_->present()` is
effectively a no-op for the software path
(`src/pal/sdl3/window_sdl3.cpp:187-195`).

To prevent double-present bugs and regressions when the OpenGL path lands:

| Rendering Path | Who Presents | How |
|---------------|-------------|-----|
| **Software** | `IContext` (via `unlockSurface()`) | `unlockSurface()` calls `SDL_RenderPresent()` internally. The run loop must NOT also call `window_->present()`. |
| **OpenGL** | `IContext` (via `swapBuffers()`) | `swapBuffers()` calls `SDL_GL_SwapWindow()`. `window_->present()` remains a no-op. |

**Rule:** The run loop never calls `window_->present()` directly. All
presentation goes through `IContext`. This is enforced by integration tests
(see REQ-PLUMB-005).

### 2.6 Interface Delta — Expected API Changes

The review identified that several "existing assets" require changes or
extensions before the app shell can use them. This section is the single
source of truth for those deltas.

| Layer | File | Change Needed | Blocking Req |
|-------|------|---------------|-------------|
| Engine | `engine/src/misc/dosbox_library.cpp:260` | Set `sound_enabled = true` for interactive mode (currently hardcoded `false`) | REQ-PLUMB-003 |
| Engine | `engine/include/dosbox/dosbox_context.h` | Expose audio sample pull/capture API for app shell consumption | REQ-PLUMB-003 |
| Legends Core | `src/legends/legends_embed_api.cpp:930-931` | Replace `init_test_pattern()` with real engine VRAM sync | REQ-PLUMB-001 |
| Legends Core | `src/legends/legends_embed_api.cpp:1299-1335` | Replace synthetic glyph fill with real VGA font ROM rendering | REQ-PLUMB-002 |
| Legends Core | `src/legends/legends_embed_api.cpp:1536-1544` | Sync actual framebuffer bytes from engine, not just mode metadata | REQ-PLUMB-001 |
| PAL | `include/pal/window.h:17` | Change default `WindowConfig::title` from `"DOSBox-X"` to `"Project Legends"` | REQ-BUILD-002 |
| PAL | `include/pal/context.h` | No resize API — resolution changes require `destroy()` + `createSoftware()`. Document this as the canonical sequence. | REQ-VIDEO-002 |

### 2.7 State Ownership Map

Clarifies which layer owns the source of truth for each data domain at each
point in the run loop:

| Data Domain | Owner (Truth) | Consumer | Transfer Mechanism |
|-------------|--------------|----------|-------------------|
| **Framebuffer pixels** | Engine (`aibox_core`) | App shell via `legends_capture_rgb()` | Two-call copy pattern |
| **Text-mode cells** | Engine (`aibox_core`) | App shell via `legends_capture_text()` | Two-call copy pattern |
| **Audio samples** | Engine (`aibox_core`) | App shell → `IAudioSink::pushSamples()` | Per-frame pull + push |
| **Input events** | Host (SDL3 via `IInputSource`) | Engine via `legends_key_event()` / `legends_mouse_event()` | Poll → translate → inject |
| **Emulated time** | Engine (via `legends_step_ms()`) | App shell reads via `legends_get_emu_time()` | Step returns result |
| **Host wall-clock** | PAL (`IHostClock`) | App shell for throttling only | `getTicksUs()` / `sleepUs()` |
| **Window/surface** | PAL (`IWindow` + `IContext`) | App shell writes pixels via lock/unlock | `lockSurface()` / `unlockSurface()` |
| **Save state blobs** | Engine (via `legends_save_state()`) | App shell writes to disk | Two-call copy + file I/O |

### 2.8 Files to Modify

| File | Change |
|------|--------|
| `CMakeLists.txt` (lines 613-650) | Add `PAL_BACKEND_SDL3` executable target alongside existing SDL2 target |
| `CMakeLists.txt` | Add `src/app/*.cpp` to the executable's source list |
| `engine/src/misc/dosbox_library.cpp` | Add interactive mode flag to enable `sound_enabled` |
| `src/legends/legends_embed_api.cpp` | Wire real framebuffer sync (Phase -1) |
| `include/pal/window.h` | Update default `WindowConfig::title` to `"Project Legends"` |

---

## 3. Phase -1: Engine I/O Plumbing — COMPLETE

> **Implementation status:** All 5 requirements implemented and tested.

**Goal:** Wire real engine output (framebuffer pixels + audio samples) through
the Legends API so that downstream consumers get actual DOS display and sound,
not synthetic test data.

**Rationale:** The current `legends_capture_rgb()` implementation uses a test
pattern (`init_test_pattern()` at `legends_embed_api.cpp:930`) and synthetic
glyph rendering (lines 1299-1335). The display metadata sync (lines 1536-1544)
copies mode/dimensions but not actual pixel bytes from the engine. Similarly,
the engine library creates its context with `sound_enabled = false`
(`dosbox_library.cpp:260`), meaning no audio is produced even if the app shell
calls `pushSamples()`. Every feature in Phases 1-4 that depends on visual
fidelity or audio output is built on this foundation.

### 3.1 Requirements

#### REQ-PLUMB-001: Engine Framebuffer Synchronization

> **While** the engine is running in interactive mode,
> **the system shall** synchronize actual VGA/SVGA framebuffer bytes from the
> engine's internal VRAM into the Legends `FrameState` structure after each
> `legends_step_ms()` call, so that `legends_capture_rgb()` returns the real
> rendered output — not a test pattern.

**Acceptance:**
- Gate G1 golden snapshot test: capture after booting to DOS prompt matches
  known-good reference image (pixel-level comparison with tolerance for timing
  jitter).
- `init_test_pattern()` call is removed or guarded behind a `--test-pattern`
  debug flag.

**Current code references:**
- `src/legends/legends_embed_api.cpp:930-931` — `init_test_pattern()`
- `src/legends/legends_embed_api.cpp:1536-1544` — metadata-only sync
- `engine/include/dosbox/dosbox_context.h` — engine display provider hooks

#### REQ-PLUMB-002: Real Text-Mode Font Rendering

> **While** the engine is in text mode,
> **the system shall** render text-mode cells using the VGA font ROM (8x16
> glyphs from the engine's BIOS data) rather than the synthetic checkerboard
> pattern currently in `legends_capture_rgb()`.

**Acceptance:**
- Characters rendered via `legends_capture_rgb()` in text mode are visually
  correct: "A" looks like the letter A, cursor blinks, colors match VGA palette.
- Golden snapshot comparison: 80x25 text-mode screen with known content matches
  reference within 1% pixel difference.

**Current code reference:**
- `src/legends/legends_embed_api.cpp:1299-1335` — synthetic glyph fill
  (`is_lit = (ch != ' ' && ch != 0) && ((px + py) % 2 == 0)`)

#### REQ-PLUMB-003: Engine Audio Path Activation

> **Where** the engine is created for interactive mode (not headless/embedding),
> **the system shall** set `sound_enabled = true` in the engine context
> configuration, initialize the audio subsystem (Sound Blaster, OPL, PC
> speaker), and provide an API for the app shell to pull rendered audio samples
> per frame.

**Acceptance:**
- Gate G2 spectral test: PC speaker beep at known frequency (e.g., 1000 Hz)
  captured from engine output matches expected frequency within ±5%.
- `audio_sink_->getQueuedFrames() > 0` after stepping with a program that
  produces sound.

**Current code reference:**
- `engine/src/misc/dosbox_library.cpp:260` — `c.sound_enabled = false;`

#### REQ-PLUMB-004: Audio Sample Transfer Interface

> **The system shall** define one explicit source-of-truth audio path from
> engine to app shell:
> 1. After `legends_step_ms()`, engine audio buffer is filled with interleaved
>    S16LE PCM samples
> 2. App shell calls a capture/pull function to obtain the samples
> 3. App shell pushes samples to `IAudioSink::pushSamples()`
>
> The audio transfer format shall be 44100 Hz stereo S16LE by default. If the
> engine produces a different format, the Legends bridge layer resamples before
> exposing to the app shell.

**Acceptance:** Audio data flows end-to-end: engine → legends bridge → app
shell → PAL audio sink → host speakers.

#### REQ-PLUMB-005: Presentation Contract Enforcement

> **The system shall** include an integration test that verifies the
> presentation ownership contract:
> 1. Create a software context, lock/unlock surface, verify exactly one
>    `SDL_RenderPresent` call occurs (via mock or counter)
> 2. Verify `window_->present()` does not trigger a second present

**Acceptance:** Test passes in CI. Run loop does not double-present.

---

## 4. Phase 0: Build Infrastructure — COMPLETE

> **Implementation status:** All 5 core requirements implemented. CI, packaging skeleton, and application class skeleton all operational.

**Goal:** `cmake --build .` produces an SDL3 executable that opens a window and
exits cleanly. Packaging skeleton is established early.

### 4.1 Requirements

#### REQ-BUILD-001: SDL3 Executable Target

> **Where** `PAL_BACKEND_SDL3` is enabled,
> **the system shall** define a CMake executable target `project_legends` that
> links against `legends_core`, `legends_pal`, and SDL3.

**Acceptance:** `cmake -DPAL_BACKEND_SDL3=ON` configures without error and
`cmake --build . --target project_legends` produces a binary.

**Implementation note:** The current `CMakeLists.txt` (lines 613-650) only
defines the executable under `if(PAL_BACKEND_SDL2)`. A parallel
`if(PAL_BACKEND_SDL3)` block is needed. The SDL3 target must NOT link
`SDL2main`, `mingw32`, or `SDL2` — instead it links `SDL3::SDL3`.

#### REQ-BUILD-002: Minimal main.cpp

> **The system shall** provide `src/main.cpp` containing a `main()` function that:
> 1. Calls `pal::Platform::initialize(pal::Backend::SDL3)`
> 2. Creates a window via `pal::Platform::createWindow()`
> 3. Calls `window->create(config)` with default 640x480 dimensions and title
>    "Project Legends" (note: `WindowConfig::title` default in
>    `include/pal/window.h:17` is currently `"DOSBox-X"` and must be overridden
>    or patched)
> 4. Enters a minimal event loop that exits on `WindowClose`
> 5. Calls `pal::Platform::shutdown()` before returning 0

**Acceptance:** Binary opens a 640x480 window titled "Project Legends", closes
on window close event, exits with code 0.

#### REQ-BUILD-003: Cross-Platform CI

> **The system shall** compile and link the SDL3 executable target on Windows
> (MSVC), Linux (GCC 13+), and macOS (AppleClang 15+) in CI.

**Acceptance:** CI pipeline produces green builds on all three platforms.

#### REQ-BUILD-004: Application Class Skeleton

> **The system shall** provide `src/app/application.h` and
> `src/app/application.cpp` defining a class `Application` that:
> 1. Owns `unique_ptr` instances of all 5 PAL services (`IWindow`, `IContext`,
>    `IAudioSink`, `IHostClock`, `IInputSource`)
> 2. Owns a `legends_handle` engine instance
> 3. Exposes `bool init(int argc, char** argv)` and `int run()`
> 4. `main.cpp` delegates to `Application::init()` then `Application::run()`

**Acceptance:** Compiles, opens a window, exits on close — same behavior as
REQ-BUILD-002 but routed through `Application`.

#### REQ-BUILD-005: Packaging Skeleton

> **The system shall** establish packaging infrastructure early (Phase 0) that
> is iterated throughout development:
> 1. CPack configuration in CMakeLists.txt for Windows (NSIS), Linux (AppImage
>    via `linuxdeploy`), and macOS (DragNDrop bundle)
> 2. CI job that produces platform artifacts on tagged builds
> 3. Smoke test: artifact installs and launches on a clean VM or container

**Acceptance:** `cmake --build . --target package` produces a platform-specific
artifact. CI produces artifacts on tag push.

**Rationale:** Building packaging only after large feature buildup (Phase 4) is
high-risk. Establishing the skeleton early and iterating catches issues
incrementally.

---

## 5. Phase 1: MVP — Display, Input, Audio — COMPLETE

> **Implementation status:** All 13 core requirements implemented in `src/app/application.cpp` and supporting modules.

**Goal:** A working DOS emulator — the user sees a real DOS prompt, can type
commands, and hears audio output.

**Prerequisites:** Phase -1 gates G1 (framebuffer) and G2 (audio) must pass
before Phase 1 acceptance is declared.

### 5.1 Requirements

#### REQ-CORE-001: Engine Initialization

> **When** `Application::init()` is called,
> **the system shall** create an engine instance via `legends_create()` using a
> `legends_config_t` populated from CLI arguments and/or a `.conf` file.
>
> **Where** the `--profile` argument specifies a preset, the system shall apply
> one of:
> - `interactive` (default) — real-time pacing, `deterministic = 0`
> - `deterministic` — fixed pacing, `deterministic = 1`, reproducible hashes
> - `benchmark` — uncapped speed, `deterministic = 1`, performance metrics

**Acceptance:** `legends_create()` returns `LEGENDS_OK`. Engine handle is valid.

**Interface reference:**
```c
legends_config_t config = LEGENDS_CONFIG_INIT;
config.config_path = conf_file;  // from CLI or NULL
config.deterministic = (profile == "deterministic" || profile == "benchmark");
legends_error_t err = legends_create(&config, &handle_);
```

#### REQ-CORE-002: Run Loop Stepping

> **While** the application is running,
> **the system shall** call `legends_step_ms(handle_, frame_ms, &result)` once
> per frame, where `frame_ms` is the emulated time per frame (default: 16 ms
> for ~60 FPS).

**Acceptance:** `result.cycles_executed > 0` on each call. Emulated time
advances monotonically.

#### REQ-CORE-003: Clean Shutdown

> **When** the user closes the window or the quit signal is received,
> **the system shall** call `legends_destroy(handle_)` followed by
> `pal::Platform::shutdown()` and exit with code 0.

**Acceptance:** No resource leaks detected by AddressSanitizer. No crash on
exit. `legends_destroy()` returns `LEGENDS_OK`.

#### REQ-VIDEO-001: Framebuffer Capture and Display

> **While** the application is running,
> **the system shall** on each frame:
> 1. Call `legends_is_frame_dirty(handle_, &dirty)`
> 2. If dirty, call `legends_capture_rgb(handle_, buffer, size, &actual, &w, &h)`
> 3. If resolution changed since last frame, destroy and recreate the software
>    context at the new dimensions (since `IContext` has no `resize()` method —
>    the canonical sequence is `context_->destroy()` then
>    `context_->createSoftware(w, h, fmt)`)
> 4. Lock the software context via `context_->lockSurface(sctx)`
> 5. Convert RGB24 → surface pixel format (see `SoftwareContext::format`) and
>    copy into the surface buffer
> 6. Unlock the surface via `context_->unlockSurface()` — this presents
>    (software path owns presentation)

**Acceptance:** Real DOS prompt is visible and readable in the window. Mode
changes (text mode → graphics mode) render correctly. Gate G1 must have passed.

**Interface reference:**
```cpp
pal::SoftwareContext sctx;
context_->lockSurface(sctx);
// sctx.format tells us the target pixel format (likely RGBA8888 or BGRA8888)
// Convert RGB24 source → sctx.format target, respecting sctx.pitch
convertAndCopy(capture_buffer, sctx);
context_->unlockSurface();  // ← presents for software path
// Do NOT call window_->present() — see Section 2.5
```

#### REQ-VIDEO-002: Dynamic Resolution Handling

> **When** the emulated display mode changes resolution (e.g., 80x25 text →
> 320x200 Mode 13h),
> **the system shall** detect the new dimensions from `legends_capture_rgb()`
> output parameters (`width_out`, `height_out`) and recreate the software
> context at the new dimensions via `context_->destroy()` followed by
> `context_->createSoftware(new_w, new_h, fmt)`.

**Acceptance:** Switching video modes in DOS (e.g., `MODE CO80`) updates the
window content without crash or corruption.

**Implementation note:** `IContext` has no `resize()` method
(`include/pal/context.h:43-55`). The destroy/recreate sequence is the canonical
approach. To avoid recreate storms, cache the last known dimensions and only
recreate when they actually change.

#### REQ-VIDEO-003: Window Resize and Aspect Ratio

> **When** the user resizes the window,
> **the system shall** scale the emulated framebuffer to fit, maintaining the
> original aspect ratio with letterboxing or pillarboxing.

**Acceptance:** Resizing the window does not stretch or distort the DOS display.

#### REQ-INPUT-001: Keyboard Input — SDL Scancode to AT Set 1

> **When** the PAL `IInputSource` reports a `KeyDown` or `KeyUp` event,
> **the system shall** translate the SDL scancode (`event.key.scancode`) to an
> AT Set 1 scancode and inject it via `legends_key_event(handle_, scancode,
> is_down)` or `legends_key_event_ext(handle_, scancode, is_down)` for
> E0-prefixed keys.

**Acceptance:** Typing "DIR" + Enter at the DOS prompt executes the DIR command
and shows output.

**Implementation note:** SDL3 scancodes follow USB HID usage codes. A static
lookup table maps SDL scancodes to AT Set 1 scancodes. Extended keys (arrows,
Insert, Delete, Home, End, Page Up/Down) use `legends_key_event_ext()`.

#### REQ-INPUT-002: Mouse Input

> **When** the PAL `IInputSource` reports mouse motion or button events,
> **the system shall** translate them to relative deltas and inject via
> `legends_mouse_event(handle_, delta_x, delta_y, buttons)`.

**Acceptance:** Mouse-driven DOS programs (e.g., DOS Edit, Norton Commander)
respond to mouse movement and clicks.

**Interface reference:**
```c
// buttons bitmask: bit 0 = left, bit 1 = right, bit 2 = middle
legends_mouse_event(handle_, dx, dy, buttons);
```

#### REQ-INPUT-003: Mouse Capture Toggle

> **When** the user clicks inside the emulator window (and mouse is not
> captured),
> **the system shall** capture the mouse via
> `input_source_->setMouseCapture(true)` and
> `input_source_->setRelativeMouseMode(true)`.

> **When** the user presses the release hotkey (default: Ctrl+F10),
> **the system shall** release the mouse capture and show the host cursor.

> **When** the user presses middle mouse button as an alternative release
> gesture, **the system shall** also release the mouse capture.

**Acceptance:** Mouse is captured on click, released on Ctrl+F10 or middle
mouse button. Cursor visibility toggles appropriately.

#### REQ-AUDIO-001: Audio Output

> **While** the application is running,
> **the system shall** open the audio sink via `audio_sink_->open(config)` with
> 44100 Hz, stereo, 50 ms buffer and push emulation-generated audio samples via
> `audio_sink_->pushSamples(samples, frame_count)` each frame.

**Acceptance:** PC speaker beeps, Sound Blaster output, and AdLib/OPL music
produce audible output at correct pitch and tempo. Gate G2 must have passed.

**Interface reference:**
```cpp
pal::AudioConfig audio_config;
audio_config.sample_rate = 44100;
audio_config.channels = 2;
audio_config.buffer_ms = 50;
audio_sink_->open(audio_config);

// Per frame (after legends_step_ms):
// Pull audio from engine bridge → push to PAL sink
audio_sink_->pushSamples(engine_audio_buffer, frame_count);
```

#### REQ-AUDIO-002: Volume Control

> **The system shall** expose volume control via `audio_sink_->setVolume(level)`
> where `level` is 0.0 (mute) to 1.0 (full).

**Acceptance:** Volume can be adjusted from a menu or hotkey. Mute silences all
output.

#### REQ-THROTTLE-001: Frame Pacing

> **While** the application is running in interactive profile,
> **the system shall** throttle the run loop to approximately 60 FPS using
> `IHostClock::getTicksUs()` for measurement and `IHostClock::sleepUs()` for
> waiting, with a spin-wait hybrid for the final portion to mitigate OS timer
> granularity.

**Acceptance:** DOS programs run at correct real-time speed. CPU usage is
reasonable (not 100% of a core at idle). Frame time variance < 3 ms (p95).

**Interface reference:**
```cpp
uint64_t frame_start = clock_->getTicksUs();
// ... step, capture, present, audio ...
uint64_t elapsed = clock_->getTicksUs() - frame_start;
constexpr uint64_t target_us = 16667;  // ~60 FPS
if (elapsed < target_us) {
    uint64_t remaining = target_us - elapsed;
    if (remaining > 2000)  // sleep for bulk, spin for tail
        clock_->sleepUs(remaining - 1500);
    while (clock_->getTicksUs() - frame_start < target_us) {}
}
```

#### REQ-CONFIG-001: Config File Loading

> **When** a `.conf` file path is provided (via CLI `--conf path` or default
> search paths),
> **the system shall** parse the INI-style config file and apply settings to
> `legends_config_t` before calling `legends_create()`.

**Acceptance:** Settings from `.conf` file (memory size, CPU type, machine type,
cycles) are reflected in the running emulator.

#### REQ-CONFIG-002: Default Config Search

> **Where** no explicit `--conf` path is provided,
> **the system shall** search for configuration files in the following order:
> 1. `./dosbox-x.conf` (current directory)
> 2. `./dosbox.conf`
> 3. `<XDG_CONFIG_HOME>/projectlegends/default.conf` (Linux)
> 4. `~/Library/Preferences/ProjectLegends/default.conf` (macOS)
> 5. `%APPDATA%\ProjectLegends\default.conf` (Windows)
> 6. Built-in defaults if no file found

**Acceptance:** Placing a `dosbox-x.conf` in the working directory applies its
settings automatically.

#### REQ-CLI-001: Command-Line Arguments

> **The system shall** accept the following command-line arguments:
>
> | Argument | Description |
> |----------|-------------|
> | `--conf <path>` | Path to `.conf` configuration file |
> | `--fullscreen` | Start in fullscreen mode |
> | `--cycles <n>` | Override CPU cycles per ms |
> | `--machine <type>` | Override machine type (vga, ega, cga, hercules, tandy) |
> | `--memsize <kb>` | Override conventional memory in KB |
> | `--profile <name>` | Execution profile: `interactive`, `deterministic`, `benchmark` |
> | `--version` | Print version and exit |
> | `--help` | Print usage and exit |
> | `--log` | Enable logging to file |
> | `[program]` | DOS program to auto-execute on startup |

**Acceptance:** `project_legends --version` prints version info and exits.
`project_legends --conf my.conf GAME.EXE` loads config and auto-runs the
program.

---

## 6. Phase 2: Core Experience — COMPLETE

> **Implementation status:** 18 of 18 requirements implemented.
> **Implemented:** Overlay menu, enhanced menu bar, pause on menu, save/load (9 slots), save slot browser, save directory, key mapper visual UI, mapper persistence, default scancode table, screenshot, video capture (ZMBV/AVI), capture directory, pause/resume, machine reset, clipboard paste, host directory mounting, block device image mounting.

**Goal:** Feature parity with DOSBox-X's essential interactive features — menus,
save states, key mapper, and screen capture.

### 6.1 Requirements

#### REQ-MENU-001: Native SDL3 Menu Bar

> **Where** the host platform supports native menus (macOS global menu bar,
> Windows/Linux title bar menu),
> **the system shall** create a native menu bar using SDL3's menu API with the
> following top-level entries:
>
> | Menu | Items |
> |------|-------|
> | **Main** | Reset, Pause/Resume, Exit |
> | **CPU** | Cycles (turbo/normal/custom), CPU type |
> | **Video** | Fullscreen toggle, Aspect correction, Scaler |
> | **Sound** | Volume, Mute toggle, Device selection |
> | **Input** | Key mapper, Mouse capture, Joystick config |
> | **Save** | Save state (slots 1-9), Load state (slots 1-9) |
> | **Capture** | Screenshot, Start/Stop video capture |
> | **Tools** | AI Assistant, Debugger |
> | **Help** | About, Keyboard shortcuts |
>
> All menu items emit `Action` values through the `ActionBus`.

**Acceptance:** Menu bar is visible and responsive on all three platforms.
Selecting an item triggers the corresponding action.

**Design note:** Menus are intentionally in the application layer, not in PAL.
PAL provides platform services (window, input, audio); menu UI policy belongs in
`src/app/menu_system.h`. No `IMenuHost` interface in PAL.

#### REQ-MENU-002: Fallback Overlay Menu

> **Where** native menus are not available or are unreliable (e.g., SDL3 menu
> API may not be supported on all X11/Wayland configurations),
> **the system shall** render a custom overlay menu using SDL3 rendering
> primitives, activated by pressing F12 or right-clicking the title bar area.
> The overlay uses the same `ActionBus` dispatch as native menus.

**Acceptance:** Overlay menu appears on F12, is navigable with keyboard/mouse,
and dismisses on Escape or selection.

#### REQ-MENU-003: Pause on Menu Open

> **When** the menu is opened (native or overlay),
> **the system shall** pause emulation stepping until the menu is closed.

**Acceptance:** Emulated time does not advance while a menu is open.

#### REQ-SAVE-001: Save State to File

> **When** the user triggers Save State (menu, Save State dialog, or hotkey
> Ctrl+Shift+F1..F9 for slots 1-9),
> **the system shall**:
> 1. Call `legends_save_state(handle_, NULL, 0, &required_size)` to query size
> 2. Allocate a buffer of `required_size` bytes
> 3. Call `legends_save_state(handle_, buffer, required_size, &actual_size)` to
>    capture state
> 4. Write the buffer to `<save_dir>/slot_<N>.sav`
> 5. Capture a thumbnail via `legends_capture_rgb()` and save as PNG alongside

**Acceptance:** Save file appears on disk. File size matches `actual_size`.
Thumbnail PNG is created.

#### REQ-SAVE-002: Load State from File

> **When** the user triggers Load State (menu, Load State dialog, or hotkey
> Ctrl+Alt+F1..F9 for slots 1-9),
> **the system shall**:
> 1. Read `<save_dir>/slot_<N>.sav` into memory
> 2. Call `legends_load_state(handle_, buffer, file_size)`
> 3. On success, resume emulation from the restored state
> 4. On failure (`LEGENDS_ERR_VERSION_MISMATCH`), show an error dialog

**Acceptance:** Loading a previously saved state restores the exact emulator
state. Typing "DIR" before save and after load shows the same directory listing.

#### REQ-SAVE-003: Save Slot UI

> **The system shall** display a save/load dialog showing all 9 slots with:
> - Slot number (1-9)
> - Thumbnail image (if save exists)
> - Timestamp of last save
> - Empty/occupied indicator

**Acceptance:** Dialog is navigable with keyboard and mouse. Occupied slots show
thumbnails.

#### REQ-SAVE-004: Save Directory

> **The system shall** store save states in the platform data directory (see
> [Appendix D](#appendix-d-platform-directory-policy)):
> - Windows: `%APPDATA%\ProjectLegends\saves\`
> - Linux: `$XDG_DATA_HOME/projectlegends/saves/`
>   (default `~/.local/share/projectlegends/saves/`)
> - macOS: `~/Library/Application Support/ProjectLegends/saves/`

**Acceptance:** Save files appear in the correct platform directory.

#### REQ-MAPPER-001: Key Mapper

> **When** the user opens the key mapper (menu or hotkey Ctrl+F1),
> **the system shall** display an interactive UI showing:
> 1. A visual keyboard layout with all mapped keys
> 2. The current binding for each host key → guest scancode
> 3. A "press new key" prompt for remapping

**Acceptance:** Remapping a key (e.g., swapping Z and Y for QWERTZ) takes
effect immediately in the emulator.

#### REQ-MAPPER-002: Mapper Persistence

> **The system shall** save and load key mappings to/from a
> `mapper.txt` file in the platform configuration directory.

**Acceptance:** Custom mappings persist across application restarts.

#### REQ-MAPPER-003: Default Scancode Table

> **The system shall** provide a default mapping from SDL3 scancodes (USB HID
> usage codes) to AT Set 1 scancodes covering:
> - All letter keys (A-Z)
> - Number row (0-9)
> - Function keys (F1-F12)
> - Modifier keys (Shift, Ctrl, Alt, Caps Lock, Num Lock, Scroll Lock)
> - Navigation keys (arrows, Home, End, Page Up/Down, Insert, Delete)
> - Numpad keys (0-9, +, -, *, /, Enter, .)
> - Punctuation and symbols
> - Escape, Tab, Backspace, Enter, Space

**Acceptance:** All standard US keyboard keys produce the correct DOS scancode.

#### REQ-CAPTURE-001: Screenshot Capture

> **When** the user triggers screenshot (menu or hotkey Ctrl+F5),
> **the system shall** capture the current framebuffer via
> `legends_capture_rgb()` and save it as a PNG file in the capture directory.

**Acceptance:** PNG file is created with correct dimensions and pixel data.

#### REQ-CAPTURE-002: Capture Directory

> **The system shall** store captures in the platform data directory (see
> [Appendix D](#appendix-d-platform-directory-policy)):
> - Windows: `%APPDATA%\ProjectLegends\capture\`
> - Linux: `$XDG_DATA_HOME/projectlegends/capture/`
>   (default `~/.local/share/projectlegends/capture/`)
> - macOS: `~/Library/Application Support/ProjectLegends/capture/`
>
> Files are named `capture_YYYYMMDD_HHMMSS_NNN.png` (with sequence number for
> sub-second captures).

**Acceptance:** Screenshot files appear with correct timestamped names.

#### REQ-PAUSE-001: Pause/Resume

> **When** the user presses the pause hotkey (Alt+Pause) or selects
> Main → Pause,
> **the system shall** stop calling `legends_step_ms()` and display a "PAUSED"
> indicator in the window title.

> **When** the user presses the pause hotkey again or selects Main → Resume,
> **the system shall** resume stepping and remove the indicator.

**Acceptance:** Emulation freezes on pause and resumes exactly where it left off.

#### REQ-RESET-001: Machine Reset

> **When** the user selects Main → Reset or presses Ctrl+Alt+Delete,
> **the system shall** call `legends_reset(handle_)` and resume from a fresh
> boot state.

**Acceptance:** DOS prompt reappears as if the machine was power-cycled.

#### REQ-MOUNT-001: Host Directory Mounting

> **When** the user configures a drive mount via the `.conf` file, CLI
> (`--mount C: /path/to/dir`), or the menu system (Main → Mount Drive),
> **the system shall** expose the host filesystem directory as an emulated DOS
> drive letter, mapping file I/O operations through the engine to the host OS.

**Acceptance:** `MOUNT C /home/user/dos` (or `.conf` equivalent) makes the
directory accessible as `C:` in the DOS prompt. `DIR C:` lists the host
directory contents. File reads and writes round-trip correctly.

#### REQ-MOUNT-002: Block Device Image Mounting

> **Where** the user mounts a `.iso`, `.cue/.bin`, or `.img` file via the menu
> or `.conf` configuration,
> **the system shall** mount the file as a block device, automatically enabling
> CD-ROM extensions (MSCDEX) for optical media and FAT filesystem translation
> for floppy/HDD images.

**Acceptance:** Mounting a `.iso` file makes it accessible as a CD-ROM drive.
`DIR D:` lists the ISO contents. Floppy `.img` files mount as `A:` with correct
FAT12/FAT16 access.

#### REQ-INPUT-004: Clipboard Keystroke Injection

> **When** the user triggers the paste hotkey (Ctrl+Shift+V or Shift+Insert) or
> selects Input → Paste from Clipboard,
> **the system shall** read text from the host OS clipboard and inject it into
> the emulated environment as a sequence of AT Set 1 scancodes via
> `legends_text_input(handle_, utf8_text)`.

**Acceptance:** Copying "DIR C:" on the host and pasting into the DOS prompt
executes the command. Special characters (backslash, quotes) are translated
correctly.

**Interface reference:**
```c
// legends_text_input handles UTF-8 → scancode translation including shift states
legends_text_input(handle_, clipboard_utf8);
```

#### REQ-CAPTURE-003: Video Capture Streaming

> **When** the user triggers "Start video capture" via the menu
> (Capture → Start Video) or hotkey (Ctrl+Shift+F5),
> **the system shall** begin streaming framebuffer updates (via
> `legends_capture_rgb()`) and synchronized audio samples to an encoded media
> file in the capture directory.

> **When** the user triggers "Stop video capture" via the menu or hotkey,
> **the system shall** finalize and close the media file.

**Acceptance:** Starting capture, running a DOS program for 10 seconds, and
stopping capture produces a playable video file. Audio and video are
synchronized within ±50 ms.

**Implementation note:** Encoding format should be AVI with ZMBV (lossless,
DOSBox-X compatible) for maximum compatibility. Optional MP4/H.264 output if
FFmpeg libraries are available at runtime.

---

## 7. Phase 3: Enhanced Features — PARTIAL

> **Implementation status:** 7 of 14 requirements implemented, 4 stubs (config UI exists but engine wiring missing), 3 missing.
> **Implemented:** Fullscreen toggle, joystick/gamepad, OpenGL shader path, shader presets (CRT/Scanlines/Sharp/Smooth), AI panel, AI screen context, AI configuration, TTF rendering.
> **Stubs:** IPX networking, 3dfx Glide, PC-98, MIDI routing (config UI loads from INI, but engine API functions are TODO stubs).
> **Missing:** Printer emulation (LPT1 not wired to engine), advanced MIDI synthesis (FluidSynth/MUNT).

**Goal:** Advanced features that differentiate ProjectLegends — shader
rendering, AI assistant, advanced hardware emulation, networking, printing,
MIDI synthesis, and TTF support. These ship as **Release B** and are opt-in;
they must not block Release A.

### 7.1 Requirements

#### REQ-SHADER-001: OpenGL Shader Rendering Path

> **Where** the user selects an OpenGL rendering mode,
> **the system shall** create an OpenGL 3.3 core profile context via
> `context_->createOpenGL(3, 3, true)` and render the emulated framebuffer
> through a shader pipeline supporting:
> - CRT curvature simulation
> - Scanline effects
> - Color temperature adjustment
> - Sharpening / smoothing filters

**Acceptance:** Selecting a CRT shader produces visible curvature and scanline
effects. Rendering is at least 60 FPS on a mid-range GPU.

**Interface reference:**
```cpp
context_->createOpenGL(3, 3, true);
context_->makeCurrent();
auto glGetProcAddress = context_->getProcAddress;
// Load shader, create FBO, render textured quad
context_->swapBuffers();  // ← presents for OpenGL path
// Do NOT call window_->present() — see Section 2.5
```

#### REQ-SHADER-002: Shader Selection

> **The system shall** provide a menu for selecting from built-in shader presets
> (None, CRT, Scanlines, Sharp, Smooth) and loading custom `.glsl` files.

**Acceptance:** Switching shaders takes effect on the next frame.

#### REQ-AI-001: AI Assistant Panel

> **The system shall** provide an integrated AI assistant panel accessible via
> menu (Tools → AI Assistant) or hotkey (Ctrl+F12) that:
> 1. Renders as a resizable side panel or floating overlay
> 2. Accepts text input from the user
> 3. Sends queries to a configurable AI backend (API endpoint + key)
>    **asynchronously** on a worker thread — never blocks the main run loop
> 4. Displays streaming responses with markdown rendering
> 5. Can read the current screen state via `legends_capture_text()` for context

**Acceptance:** Opening the AI panel shows a chat-style interface. Typing a
question returns a response. The AI can "see" the current DOS screen when asked.
Emulation does not freeze while waiting for AI response.

**AI guardrails:**
- AI is opt-in: disabled by default, enabled via config or first-use dialog
- Privacy mode available: `ai.privacy_mode=true` disables all network calls,
  shows local-only context display
- Prompt/context budget: configurable `ai.max_context_chars` to prevent
  cost spikes from large screen captures

#### REQ-AI-002: AI Screen Context

> **When** the AI assistant processes a query with screen context enabled,
> **the system shall** call `legends_capture_text(handle_, cells, count,
> &count_out, &info)` and include the text-mode screen contents (decoded from
> CP437) in the AI context.

**Acceptance:** Asking the AI "what's on screen?" returns an accurate
description of the current DOS display.

**Interface reference:**
```c
legends_text_info_t info;
size_t count_out;
legends_capture_text(handle_, NULL, 0, &count_out, &info);  // query size
std::vector<legends_text_cell_t> cells(count_out);
legends_capture_text(handle_, cells.data(), count_out, &count_out, &info);
// info.columns, info.rows, info.cursor_x, info.cursor_y
// cells[i].character = CP437 code, cells[i].attribute = VGA color
```

#### REQ-AI-003: AI Configuration

> **The system shall** allow configuring the AI backend via the `.conf` file:
> ```ini
> [ai]
> enabled=false
> endpoint=https://api.anthropic.com/v1/messages
> model=claude-sonnet-4-20250514
> api_key_env=ANTHROPIC_API_KEY
> max_tokens=4096
> max_context_chars=8000
> privacy_mode=false
> ```

**Acceptance:** Setting a valid API key and endpoint enables AI responses.
Missing or invalid configuration shows a clear error in the panel.
`enabled=false` (default) means the AI panel shows a setup prompt on first open.

#### REQ-PRINT-001: Printer Emulation

> **The system shall** emulate a parallel port printer (LPT1) that captures
> output to:
> 1. A text file (raw bytes)
> 2. A rendered PDF (if ESC/P or PCL commands are detected)

**Acceptance:** `PRINT README.TXT` from DOS produces a text file in the capture
directory.

#### REQ-MIDI-001: MIDI Output

> **Where** the host system has a MIDI output device,
> **the system shall** route emulated MPU-401 MIDI output to the host MIDI
> device or a built-in software synthesizer.

**Acceptance:** Games with MIDI music (e.g., configured for General MIDI)
produce musical output.

#### REQ-TTF-001: TrueType Font Rendering

> **Where** the emulator is in text mode,
> **the system shall** optionally render text using a host TrueType font instead
> of the emulated VGA font, for improved readability on high-DPI displays.

**Acceptance:** Enabling TTF mode renders the DOS prompt in a crisp, scalable
font. Character spacing and cursor position remain correct.

#### REQ-FULLSCREEN-001: Fullscreen Toggle

> **When** the user presses Alt+Enter or selects Video → Fullscreen,
> **the system shall** call `window_->setFullscreen(true)` and scale the
> emulated display to fill the screen.

> **When** the user presses Alt+Enter again,
> **the system shall** call `window_->setFullscreen(false)` to return to
> windowed mode.

**Acceptance:** Fullscreen toggle works on all three platforms without losing
display content.

#### REQ-JOYSTICK-001: Joystick/Gamepad Support

> **When** a joystick or gamepad is connected,
> **the system shall** translate `JoystickAxis` and `JoystickButton` events from
> `IInputSource` into emulated joystick signals for DOS programs.

**Acceptance:** A DOS game configured for joystick responds to gamepad input.

#### REQ-NET-001: IPX Network Emulation

> **Where** IPX networking is enabled in the configuration (`[ipx]`
> `ipx=true`),
> **the system shall** bridge emulated IPX packets over host UDP sockets to
> enable local network or internet multiplayer in compatible DOS games.

**Acceptance:** Two instances of Project Legends on the same LAN (or via
internet relay) can establish an IPX connection and play a multiplayer DOS game
(e.g., DOOM network game, Warcraft II IPX).

#### REQ-HW-001: 3dfx Voodoo / Glide Emulation

> **Where** 3dfx hardware acceleration is requested by a guest application
> (e.g., Windows 9x games calling Glide API),
> **the system shall** intercept Glide API calls and translate them to the
> host's OpenGL rendering backend via the existing `IContext::createOpenGL()`
> path to provide hardware-accelerated 3D graphics.

**Acceptance:** A Windows 95 guest running a Glide-based game (e.g., Tomb
Raider, Quake II) renders 3D scenes correctly with hardware acceleration
visible.

#### REQ-HW-002: NEC PC-98 Architecture Support

> **Where** the machine type is configured as `pc98`,
> **the system shall** emulate the distinct NEC PC-98 memory map, text VRAM
> layout, GDC (Graphic Display Controller), and specific audio hardware
> (YM2203/YM2608 OPNA) required to boot and run Japanese PC-98 software.

**Acceptance:** A known PC-98 program (e.g., Touhou Project or a simple PC-98
DOS test) boots and displays correct Japanese text and graphics.

#### REQ-AUDIO-003: Advanced MIDI Synthesis (FluidSynth/MUNT)

> **Where** the user configures a SoundFont (`.sf2`) file or selects MT-32
> emulation mode in the `.conf` file,
> **the system shall** route MIDI output through an integrated software
> synthesizer:
> 1. **FluidSynth** for General MIDI / SoundFont playback
> 2. **MUNT** for Roland MT-32 emulation
>
> The synthesizer renders PCM audio samples which are pushed to the PAL audio
> sink alongside other engine audio.

**Acceptance:** A game configured for General MIDI with a SoundFont produces
high-quality orchestral audio. A game configured for MT-32 produces authentic
Roland MT-32 sound via MUNT.

**Configuration:**
```ini
[midi]
mididevice=fluidsynth
fluid.soundfont=/path/to/GeneralUser.sf2

# OR for MT-32:
mididevice=mt32
mt32.romdir=/path/to/mt32-roms/
```

---

## 8. Phase 4: Polish & Release — COMPLETE

> **Implementation status:** All 16 core requirements implemented across testing (12 REQs), packaging (4 REQs), logging/errors/operations (4 REQs).
> 98 unit test files, 28 integration tests, 5 fuzz targets, 2 benchmark suites, 6 CI workflows.

**Goal:** Production-quality testing, documentation, and installer
finalization for public release.

### 8.1 Requirements

#### REQ-TEST-001: Unit Test Coverage

> **The system shall** maintain unit test coverage for all `src/app/` modules
> with particular focus on:
> - `ConfigParser`: Round-trip parsing of all value types
> - `InputMapper`: Correct scancode translation for all mapped keys
> - `SaveManager`: Save/load round-trip integrity
> - `CLIParser`: All argument combinations
> - `ActionBus`: Action dispatch correctness
> - `PlatformDirs`: Correct paths on each platform

**Acceptance:** `ctest` passes with all tests green. Coverage report shows
>80% line coverage for `src/app/`.

#### REQ-TEST-002: Integration Test — Boot to Prompt

> **The system shall** include an automated integration test that:
> 1. Launches the binary headlessly (or with virtual display)
> 2. Steps until a DOS prompt appears (detected via `legends_capture_text()`)
> 3. Types "VER" + Enter
> 4. Verifies the version string appears in text capture

**Acceptance:** Integration test passes in CI on all three platforms.

#### REQ-TEST-003: Determinism Verification

> **The system shall** include an integration test that:
> 1. Creates an engine instance with `deterministic = 1`
> 2. Steps N cycles and captures state hash via `legends_get_state_hash()`
> 3. Destroys and recreates the instance with identical config
> 4. Steps N cycles and captures state hash again
> 5. Asserts both hashes are identical

**Acceptance:** Determinism test passes. Alternatively, uses the built-in
`legends_verify_determinism(handle_, N, &is_deterministic)` convenience
function.

#### REQ-TEST-004: Golden Visual Tests

> **The system shall** include golden snapshot tests for visual correctness:
> 1. Text mode: boot to DOS prompt, capture, compare against reference PNG
> 2. Graphics mode: Mode 13h color bars test program, compare against reference
> 3. Palette transition: VGA palette animation, compare selected frames

**Acceptance:** Golden snapshot comparison passes with <1% pixel difference
threshold.

#### REQ-TEST-005: Audio Validation Tests

> **The system shall** include audio validation tests:
> 1. Known-frequency PC speaker tone: verify spectral peak within ±5%
> 2. Buffer underflow test: verify `getDroppedFrames()` stays at 0 under normal
>    load
> 3. Mute test: verify silence when `setVolume(0.0)` is active

**Acceptance:** All audio tests pass in CI (spectral analysis via FFT on
captured buffer).

#### REQ-TEST-006: Replay Determinism Test

> **The system shall** include a replay test that:
> 1. Records a scripted input timeline (keystrokes with cycle timestamps)
> 2. Plays it back in deterministic mode
> 3. Verifies final state hash matches a known-good value

**Acceptance:** Replay test passes in CI on all platforms.

#### REQ-TEST-007: Cross-Platform UI Smoke Test

> **The system shall** include a scripted UI smoke test that:
> 1. Launches the binary
> 2. Toggles fullscreen (Alt+Enter)
> 3. Opens overlay menu (F12), navigates, closes (Escape)
> 4. Captures a screenshot (Ctrl+F5)
> 5. Quits cleanly

**Acceptance:** Smoke test script passes on all platforms. Screenshot file
exists after capture step.

#### REQ-TEST-008: Soak Testing (Endurance)

> **The system shall** include a soak test that:
> 1. Boots into a graphically and auditorily demanding program (e.g., DOOM
>    rolling demo or Second Reality) in headless mode
> 2. Runs continuously for 12-24 hours
> 3. Monitors memory consumption (RSS) and audio buffer health

**Acceptance:** Memory consumption remains within 5% of the baseline measured
after hour 1. `audio_sink_->getDroppedFrames()` remains at zero for the
duration. No crashes or hangs.

#### REQ-TEST-009: Performance Regression Benchmarking

> **The system shall** include an automated performance benchmark that:
> 1. Uses `--profile benchmark` (uncapped speed, deterministic mode)
> 2. Runs a known computationally heavy DOS synthetic benchmark (e.g., Landmark
>    System Speed Test or custom Dhrystone loop) for 10 seconds
> 3. Records emulated CPU instructions-per-second (IPS)
> 4. Compares against a stored `main` branch baseline

**Acceptance:** Emulated IPS does not drop by more than 5% compared to the
`main` branch baseline on the same CI runner hardware. Results are logged and
tracked across commits.

#### REQ-TEST-010: Fuzz Testing (Input, Config, Network)

> **The system shall** include fuzz testing targets using `libFuzzer` or
> equivalent:
> 1. **Config parser**: Mutated `.conf` file strings fed to `ConfigParser`
> 2. **Input injection**: Randomized high-frequency scancode arrays and mouse
>    deltas fed to `legends_key_event()` and `legends_mouse_event()`
> 3. **Save state loader**: Mutated `.sav` file bytes fed to
>    `legends_load_state()`
> 4. *(For REQ-NET-001)*: Malformed UDP packets sent to the IPX listener port

**Acceptance:** The emulator does not segfault, assert, or exhibit undefined
behavior under any fuzzed input. Bad config is rejected gracefully. Malformed
save states return `LEGENDS_ERR_INVALID_STATE` or similar. Bad packets are
silently dropped.

#### REQ-TEST-011: Save State Forward-Compatibility

> **The system shall** maintain a repository of versioned `.sav` files
> representing various emulator states (DOS prompt, mid-game, Windows 95
> desktop) from each major release version.
>
> CI shall automatically attempt to load each archived save on the latest build.

**Acceptance:** Archived saves either load successfully (backward compatible) or
fail gracefully with `LEGENDS_ERR_VERSION_MISMATCH` and a user-facing error
dialog (per REQ-ERROR-001). Hard crashes on version-mismatched saves are test
failures.

#### REQ-TEST-012: Deterministic Rendering Validation (Shaders/3dfx)

> **Where** OpenGL shaders or 3dfx Glide translation are active,
> **the system shall** include a rendering validation test that:
> 1. Renders a specific test scene to a headless Framebuffer Object (FBO)
> 2. Reads pixels back from the FBO
> 3. Compares against a golden reference using structural similarity index
>    (SSIM)

**Acceptance:** SSIM > 99% against the golden reference, accounting for minor
floating-point differences between AMD/NVIDIA/Intel GPU drivers.

#### REQ-PACKAGE-001: Windows Installer

> **The system shall** produce a Windows installer (MSI or NSIS) containing:
> - `project_legends.exe`
> - `SDL3.dll`
> - Default configuration files
> - Start menu shortcuts

**Acceptance:** Double-clicking the installer on a clean Windows machine
installs and runs the application (Gate G4).

#### REQ-PACKAGE-002: Linux AppImage

> **The system shall** produce a Linux AppImage that runs on major distributions
> (Ubuntu 22.04+, Fedora 38+, Arch Linux) without requiring system SDL3.

**Acceptance:** `./ProjectLegends-x86_64.AppImage` launches on a clean Ubuntu
22.04 VM (Gate G4).

#### REQ-PACKAGE-003: macOS Bundle

> **The system shall** produce a macOS `.app` bundle (and optionally a `.dmg`
> disk image) that:
> - Is signed with a valid Developer ID (or ad-hoc for testing)
> - Includes SDL3 as a bundled framework
> - Registers the correct `Info.plist` metadata

**Acceptance:** Double-clicking the `.app` on macOS launches the application
without Gatekeeper warnings (when signed) (Gate G4).

#### REQ-PACKAGE-004: Portable Mode

> **Where** a file named `portable.txt` exists next to the executable,
> **the system shall** store all configuration, saves, and captures in the
> executable's directory instead of platform-specific paths.

**Acceptance:** Creating `portable.txt` next to the executable causes all data
to be written locally.

#### REQ-LOG-001: Structured Logging

> **The system shall** log application events (startup, config loaded, engine
> errors, PAL errors) via `legends_set_log_callback()` and route messages to:
> 1. `stderr` (always)
> 2. A log file in the platform log directory (opt-in via `--log` flag):
>    - Windows: `%APPDATA%\ProjectLegends\logs\`
>    - Linux: `$XDG_STATE_HOME/projectlegends/logs/`
>      (default `~/.local/state/projectlegends/logs/`)
>    - macOS: `~/Library/Logs/ProjectLegends/`

**Acceptance:** Running with `--log` produces a readable log file. Engine errors
appear in the log with level prefixes.

**Interface reference:**
```c
legends_set_log_callback(handle_, [](int level, const char* msg, void* ud) {
    fprintf(stderr, "[%s] %s\n", level_names[level], msg);
}, nullptr);
```

#### REQ-ERROR-001: User-Facing Error Reporting

> **When** an engine API call returns an error code,
> **the system shall** call `legends_get_last_error(handle_, buf, size, &len)`
> to retrieve a human-readable message and display it to the user via a dialog
> or status bar.

**Acceptance:** Attempting to load a corrupted save file shows a meaningful
error message rather than a crash.

---

## 9. Security Hardening — PARTIAL

> **Implementation status:** 17 of 22 requirements implemented, of which 7 are partial (scaffolded with stubs or basic validation only, not fully exercised against real engine I/O): AI TLS verification (REQ-SEC-005), AI markdown sanitization (REQ-SEC-008), prompt injection separation (REQ-SEC-018), image validation (REQ-SEC-016), canonical paths (REQ-SEC-023), readonly mounts (REQ-SEC-024), sensitive path warning (REQ-SEC-025). Fully implemented: log file permissions (REQ-SEC-040), API key prohibition (REQ-SEC-006), config field length limits (REQ-SEC-014), save state CRC (REQ-SEC-010/011), CWD config warning (REQ-SEC-013), dependency scanning (REQ-SEC-028), threat model (REQ-SEC-031), code signing runbook (REQ-SEC-035), SHA-256 checksums (REQ-SEC-036), dependency pinning (REQ-SEC-027). Missing: code signing CI automation (REQ-OPS-008), and 5 Release B items (REQ-SEC-001, REQ-SEC-002, REQ-SEC-038, REQ-SEC-039, REQ-OPS-024).

**Source:** Security engineering persona review (v3.0.0)
**Severity:** HIGH — The roadmap previously contained no dedicated security section,
no threat model, and no security-specific requirements.

### 9.1 Threat Model Requirement

#### REQ-SEC-031: Formal Threat Model

> **The system shall** document and maintain a threat model defining trust
> boundaries between: (a) the host OS and the emulator process, (b) the emulator
> process and the emulated guest environment, (c) the emulator and the network,
> and (d) the emulator and the AI backend. This threat model shall be maintained
> alongside the roadmap.

**Priority:** Must | **Phase:** 0 | **Release:** A

### 9.2 Host Filesystem Isolation (Critical)

#### REQ-SEC-023: Path Confinement for Mounts

> **When** file I/O operations are performed within a mounted directory
> (REQ-MOUNT-001),
> **the system shall** resolve all file paths to their canonical (real) path and
> verify they remain within the mount root. Symlinks, junctions, and `..\`
> traversals that escape the mount root shall be rejected with an error.

**Priority:** Must | **Phase:** 2 | **Release:** A

#### REQ-SEC-024: Read-Only Mount Option

> **Where** the user specifies `readonly` for a mount (via CLI `--mount C:
> /path -readonly` or `.conf` `mount_readonly=true`),
> **the system shall** reject all write operations from the guest for that drive
> with a DOS "Access denied" error.

**Priority:** Must | **Phase:** 2 | **Release:** A

#### REQ-SEC-025: Sensitive Directory Warning

> **When** the user attempts to mount a system directory (e.g., `C:\Windows`,
> `/etc`, `/usr`, or the user's home directory root),
> **the system shall** display a warning recommending a subdirectory instead.

**Priority:** Should | **Phase:** 2 | **Release:** A

### 9.3 Save State Integrity

#### REQ-SEC-010: Save State Header Validation

> **When** loading a save state file,
> **the system shall** validate the `SaveStateHeader` magic bytes, version, and
> an embedded CRC-32 checksum before processing any state data. Files failing
> validation shall be rejected with `LEGENDS_ERR_INVALID_STATE`.

**Priority:** Must | **Phase:** 2 | **Release:** A

#### REQ-SEC-011: Save State Size Limit

> **The system shall** enforce a maximum save state file size of 256 MB. Files
> exceeding this limit shall be rejected before being read into memory.

**Priority:** Must | **Phase:** 2 | **Release:** A

### 9.4 Config File Security

#### REQ-SEC-013: CWD Config File Warning

> **When** loading a `.conf` file from the current working directory (as opposed
> to the platform config directory),
> **the system shall** display a warning informing the user that the file may
> modify emulator behavior including network and AI settings. CWD config loading
> shall be disableable via a platform-level config flag.

**Priority:** Should | **Phase:** 1 | **Release:** A

#### REQ-SEC-014: Config Parser Field Limits

> **The system shall** enforce maximum lengths for config section names (256
> chars), key names (256 chars), and values (4096 chars). The parser shall not
> support `include` directives or recursive file loading.

**Priority:** Should | **Phase:** 1 | **Release:** A

### 9.5 AI Panel Security

#### REQ-SEC-005: TLS Certificate Verification

> **The system shall** enforce TLS certificate verification on all AI backend
> HTTP connections. Self-signed certificates shall only be accepted when
> explicitly configured (`ai.tls_verify=false`) with a logged warning.

**Priority:** Must | **Phase:** 3 | **Release:** B

#### REQ-SEC-006: API Key Storage Protection

> **The system shall** accept AI API keys only via environment variable
> indirection (`api_key_env=VARIABLE_NAME`). If a user writes a raw key
> (`api_key=sk-...`), the parser shall emit a warning and refuse to load it.

**Priority:** Must | **Phase:** 3 | **Release:** B

#### REQ-SEC-018: Prompt Injection Separation

> **The system shall** delineate screen context from user queries in AI prompts
> using a structured format (e.g., XML tags or JSON fields) with system
> instructions directing the AI model to treat screen content as untrusted data.

**Priority:** Must | **Phase:** 3 | **Release:** B

#### REQ-SEC-008: AI Response Sanitization

> **The system shall** sanitize AI markdown responses to prevent rendering of
> HTML tags, JavaScript, `file://` URIs, or other dangerous content.

**Priority:** Should | **Phase:** 3 | **Release:** B

### 9.6 Network Security

#### REQ-SEC-001: IPX Localhost Binding

> **Where** IPX networking is enabled,
> **the system shall** bind the UDP listener to `127.0.0.1` by default. Binding
> to `0.0.0.0` shall require explicit `ipx.listen_address` config and display
> a UI warning about external network exposure.

**Priority:** Must | **Phase:** 3 | **Release:** B

#### REQ-SEC-002: IPX Rate Limiting

> **The system shall** enforce a maximum packet size (1500 bytes MTU) and a
> per-source rate limit (100 packets/second) on the IPX UDP listener.

**Priority:** Should | **Phase:** 3 | **Release:** B

### 9.7 Supply Chain

#### REQ-SEC-027: Dependency Version Pinning

> **The system shall** pin all third-party dependencies (SDL3, FluidSynth, MUNT)
> to specific versions in CMakeLists.txt or a dependency manifest. Version
> updates shall be explicit, reviewed commits.

**Priority:** Must | **Phase:** 0 | **Release:** A

#### REQ-SEC-028: Dependency Vulnerability Scanning

> **The system shall** include automated dependency vulnerability scanning in CI
> (e.g., `osv-scanner` or Dependabot) that fails the build on known critical
> or high-severity CVEs.

**Priority:** Should | **Phase:** 0 | **Release:** A

### 9.8 Code Signing & Distribution

#### REQ-SEC-035: Cross-Platform Code Signing

> **The system shall** sign release binaries: Windows Authenticode, macOS
> Developer ID + notarization (extends REQ-PACKAGE-003), and Linux GPG-signed
> release manifests.

**Priority:** Must | **Phase:** 4 | **Release:** A

#### REQ-SEC-036: Checksum Publication

> **Each release shall** publish a `SHA256SUMS.txt` file alongside artifacts,
> with optional detached GPG signature.

**Priority:** Should | **Phase:** 4 | **Release:** A

### 9.9 Additional Security Requirements

#### REQ-SEC-016: Image Parser Validation

> **The system shall** validate all filesystem metadata in mounted images
> (partition tables, FAT chains, ISO 9660 descriptors). Directory traversal
> depth shall be limited to 64 levels. FAT chain cycle detection shall prevent
> infinite loops.

**Priority:** Must | **Phase:** 2 | **Release:** A

#### REQ-SEC-038: Shader File Validation

> **The system shall** validate custom `.glsl` shader files before compilation:
> maximum 64 KB file size, compilation errors caught and reported without crash.

**Priority:** Should | **Phase:** 3 | **Release:** B

#### REQ-SEC-039: SoundFont/ROM File Limits

> **The system shall** enforce file size limits on `.sf2` (256 MB) and MT-32 ROM
> (1 MB) loading. Parsing errors shall be caught gracefully.

**Priority:** Should | **Phase:** 3 | **Release:** B

#### REQ-SEC-040: Log File Security

> **The system shall** create log files with restrictive permissions (0600 on
> Unix, non-inherited ACL on Windows). Log rotation shall cap files at 10 MB
> with 5 rotated files maximum.

**Priority:** Should | **Phase:** 4 | **Release:** A

---

## 10. Embedding API Completeness — PARTIAL

> **Implementation status:** 10 of 11 API requirements implemented. Implemented: feature parity (REQ-API-001), audio capture (REQ-API-002/003), mount/unmount API (REQ-API-004), event callback registration (REQ-API-006), capability query (REQ-API-011), multi-instance docs (REQ-API-007), cross-thread safety docs (REQ-API-009), step_result extensibility (REQ-API-013), DLL export macro (REQ-API-014). Missing: runtime drive swap (REQ-API-005).

**Source:** Embedded SDK developer persona review (v3.0.0)
**Assessment:** The C API (`legends_embed.h`) is well-designed but the roadmap is
written almost entirely from the interactive binary perspective. The embedding
use case — arguably the project's most unique differentiator — needs dedicated
requirements.

### 10.1 API Parity

#### REQ-API-001: Embedding Feature Parity Guarantee

> **The system shall** ensure that every emulator-state-mutating operation
> available through the Application Shell (mounting, configuration changes,
> audio mode, reset) is also accessible through `legends_embed.h` C API
> functions. App-shell-only UI features (menus, dialogs, AI panel rendering)
> are exempt.

**Priority:** Must | **Phase:** 1 | **Release:** A

### 10.2 Audio Capture (Critical Gap)

#### REQ-API-002: Audio Capture C API

> **The system shall** provide a `legends_capture_audio()` function in
> `legends_embed.h` that follows the same two-call pattern as
> `legends_capture_rgb()`, returning interleaved S16LE PCM samples accumulated
> since the last capture call, along with sample rate and channel count metadata.
>
> ```c
> legends_error_t legends_capture_audio(
>     legends_handle handle,
>     int16_t* buffer,          // NULL to query size
>     size_t buffer_frames,     // capacity in frames
>     size_t* frames_out,       // actual/required frame count
>     uint32_t* sample_rate_out,
>     uint8_t* channels_out
> );
> ```

**Priority:** Must | **Phase:** -1 (alongside REQ-PLUMB-004) | **Release:** A

#### REQ-API-003: Audio Readiness Query

> **The system shall** provide a `legends_is_audio_ready()` function analogous
> to `legends_is_frame_dirty()` for video.

**Priority:** Should | **Phase:** -1 | **Release:** A

### 10.3 Mounting API

#### REQ-API-004: Drive Mount C API

> **The system shall** provide `legends_mount_drive()` and
> `legends_unmount_drive()` functions in `legends_embed.h`:
>
> ```c
> legends_error_t legends_mount_drive(
>     legends_handle handle,
>     char drive_letter,       // 'A' through 'Z'
>     const char* host_path,   // host directory or image file path
>     uint8_t mount_type       // 0=directory, 1=floppy_img, 2=hdd_img, 3=iso
> );
>
> legends_error_t legends_unmount_drive(
>     legends_handle handle,
>     char drive_letter
> );
> ```

**Priority:** Must | **Phase:** 2 | **Release:** A

#### REQ-API-005: Runtime Drive Swap

> **The system shall** allow `legends_mount_drive()` and
> `legends_unmount_drive()` to be called while the engine is running (between
> `legends_step_ms()` calls), enabling runtime media changes.

**Priority:** Should | **Phase:** 2 | **Release:** A

### 10.4 Event Callbacks

#### REQ-API-006: Engine Event Callback Registration

> **The system shall** provide an optional callback registration API for engine
> events (mode change, audio ready, breakpoint, halt, disk access). Callbacks
> fire synchronously during `legends_step_ms()` on the calling thread.

**Priority:** Should | **Phase:** 2 | **Release:** A

### 10.5 Thread Safety & Documentation

#### REQ-API-009: Cross-Thread Capture Safety Documentation

> **The system shall** document in `legends_embed.h` the threading contract for
> capture functions: whether `legends_capture_rgb()`, `legends_capture_text()`,
> and `legends_capture_audio()` are safe to call from a non-owner thread when
> no step call is in progress.

**Priority:** Must | **Phase:** 1 | **Release:** A

### 10.6 ABI Extensibility

#### REQ-API-013: Step Result Extensibility

> **The system shall** add reserved fields to `legends_step_result_t` (or define
> a v2 struct) to accommodate future data such as audio frames generated,
> breakpoint address, or mode-change indicators.

**Priority:** Must | **Phase:** 1 | **Release:** A

#### REQ-API-011: Capability Query API

> **The system shall** provide a `legends_has_capability()` function allowing
> embedders to query feature support at runtime (audio capture, drive mount,
> event callbacks) without relying solely on version comparisons.

**Priority:** Should | **Phase:** 1 | **Release:** A

#### REQ-API-014: DLL Export Annotations

> **The system shall** define a `LEGENDS_API` macro in `legends_embed.h` that
> expands to `__declspec(dllexport/dllimport)` on Windows and
> `__attribute__((visibility("default")))` on ELF, applied to all public API
> functions.

**Priority:** Should | **Phase:** 0 | **Release:** A

### 10.7 Multi-Instance Guidance

#### REQ-API-007: Multi-Instance Embedding Documentation

> **The system shall** document the recommended pattern for running multiple
> concurrent emulation instances (one process per instance) with guidance on
> IPC mechanisms and example code.

**Priority:** Should | **Phase:** 4 | **Release:** A

---

## 11. Operational Infrastructure — MOSTLY COMPLETE

> **Implementation status:** 14 of 16 operational requirements implemented. Missing: Windows Authenticode signing (REQ-OPS-008), dynamic LGPL linking (REQ-OPS-024).

**Source:** DevOps/Release engineering persona review (v3.0.0)
**Assessment:** The roadmap is strong on functional requirements but has significant
gaps in build infrastructure, release automation, and operational concerns.

### 11.1 Dependency Management

#### REQ-OPS-001: SDL3 Version Pinning

> **The system shall** pin SDL3 to a specific release tag or commit SHA (via
> CMake `FetchContent` with `GIT_TAG` or vcpkg version overlay). The pinned
> version shall be documented in `DEPENDENCIES.md`.

**Priority:** Must | **Phase:** 0 | **Release:** A

#### REQ-OPS-002: Hermetic CI Builds

> **The system shall** build SDL3 from source (or binary cache) in CI on all
> three platforms using the pinned version, not relying on host-installed SDL3.

**Priority:** Must | **Phase:** 0 | **Release:** A

#### REQ-OPS-003: Centralized Dependency Manifest

> **A single** `cmake/dependencies.cmake` file shall centralize all third-party
> dependency versions (SDL3, FluidSynth, MUNT, libpng, zstd).

**Priority:** Should | **Phase:** 0 | **Release:** A

### 11.2 CI Tiering

#### REQ-OPS-004: Tiered CI Pipeline

> **The system shall** define explicit CI tiers:
> 1. **Per-PR:** Build + unit tests + boot-to-prompt on 3 platforms (~15 min)
> 2. **Merge-to-main:** Adds ASAN/TSAN, golden snapshots, audio tests, benchmarks
> 3. **Nightly:** Soak tests, fuzz exploration (4-8 hrs), full compatibility corpus
> 4. **Tag/release:** Packaging, signing, installer smoke tests

**Priority:** Must | **Phase:** 0 | **Release:** A

#### REQ-OPS-005: Build Caching

> **CI shall** cache SDL3 and `aibox_core` build artifacts (keyed on source
> hash) to keep per-PR builds under 15 minutes.

**Priority:** Should | **Phase:** 0 | **Release:** A

### 11.3 Artifact Management

#### REQ-OPS-007: Artifact Naming Convention

> **Release artifacts shall** be named
> `ProjectLegends-<semver>-<platform>-<arch>.<ext>`. Nightly artifacts shall
> include the short Git SHA.

**Priority:** Must | **Phase:** 4 | **Release:** A

#### REQ-OPS-008: Windows Code Signing

> **Windows binaries shall** be signed with an Authenticode code signing
> certificate. Unsigned Windows installers trigger SmartScreen warnings that
> block most users.

**Priority:** Must | **Phase:** 4 | **Release:** A

### 11.4 Release Process

#### REQ-OPS-019: Release Branch Model

> **The project shall** follow a release branch model: `release/X.Y` branches
> created from `main`, hotfixes cherry-picked, tagged as `vX.Y.Z`.

**Priority:** Must | **Phase:** 0 | **Release:** A

#### REQ-OPS-020: Semantic Versioning

> **Version numbers shall** follow Semantic Versioning 2.0.0
> (`MAJOR.MINOR.PATCH`), derived from Git tags via CMake `git describe`.

**Priority:** Must | **Phase:** 0 | **Release:** A

#### REQ-OPS-021: Tag Naming Convention

> **Tags shall** follow `vX.Y.Z` (release) or `vX.Y.Z-rc.N` / `vX.Y.Z-beta.N`
> (pre-release).

**Priority:** Should | **Phase:** 0 | **Release:** A

### 11.5 License Compliance

#### REQ-OPS-022: License Bundling

> **The distribution shall** include a `LICENSES/` directory with full license
> text for every bundled dependency, and a `NOTICE` file with SPDX identifiers.

**Priority:** Must | **Phase:** 4 | **Release:** A

#### REQ-OPS-023: GPL v2 Compliance Analysis

> **The licensing implications of statically linking `aibox_core` (DOSBox-X
> engine, GPL v2) shall** be formally analyzed and documented. If the binary is
> a derivative work, the project must be distributed under GPL v2-compatible
> terms with source availability.
>
> The process isolation architecture defined in **Section 14** and the technical
> design document (`docs/design/GPL2_PROCESS_ISOLATION_DESIGN.md`, TDD-LIC-001)
> provide the mitigation strategy: separating the GPL engine into its own process
> communicating via an MIT-licensed IPC protocol. See REQ-ISO-001 through
> REQ-ISO-016 for the detailed implementation requirements.

**Acceptance criteria:**
1. Legal analysis document exists and is reviewed.
2. Process isolation architecture is implemented per Section 14 requirements.
3. `COPYING`, `LICENSE`, and `NOTICE` files are present at repo root.
4. GPL object code is confined to the `legends_engine_host` binary.

**Priority:** Must (BLOCKER) | **Phase:** 0 | **Release:** A

#### REQ-OPS-024: LGPL Dynamic Linking

> **FluidSynth and MUNT shall** be dynamically linked on all platforms to
> comply with LGPL re-linking requirements.

**Priority:** Should | **Phase:** 3 | **Release:** B

### 11.6 Fuzz Testing Infrastructure

#### REQ-OPS-014: Two-Mode Fuzz Testing

> **Fuzz tests shall** run in two modes: (1) per-PR seed corpus regression
> (~2 min), and (2) nightly exploration (4-8 hours per target).

**Priority:** Must | **Phase:** 4 | **Release:** A

#### REQ-OPS-015: Fuzz Crash Corpus

> **Fuzz crash inputs shall** be stored in `test/fuzz/corpus/<target>/` checked
> into the repo. Nightly discoveries auto-committed to `fuzz-findings` branch.

**Priority:** Must | **Phase:** 4 | **Release:** A

### 11.7 Crash Reporting

#### REQ-OPS-028: Opt-In Crash Reporting

> **The application shall** include opt-in crash reporting that captures a
> minidump (Windows), crash log (macOS), or core dump summary (Linux) when an
> unhandled exception/signal is received. User prompted before transmission.

**Priority:** Should | **Phase:** 4 | **Release:** A

#### REQ-OPS-029: Crash Breadcrumb Log

> **The application shall** write last-100-events to a ring buffer file that
> persists across crashes. On next startup after crash, offer to send log.

**Priority:** Should | **Phase:** 4 | **Release:** A

### 11.8 Auto-Update

#### REQ-OPS-017: Update Check

> **The application shall** check for updates on startup (opt-in) using Sparkle
> (macOS), WinSparkle (Windows), or AppImageUpdate (Linux).

**Priority:** Should | **Phase:** 4 | **Release:** A

---

## 12. Quality Engineering — MOSTLY COMPLETE

> **Implementation status:** 19 of 19 quality requirements implemented (Release A), though several rely on scaffolded stubs pending real engine I/O plumbing. Deferred to external dependencies: macOS Retina testing (REQ-QA-016, needs hardware), Wayland CI (REQ-QA-017, needs compositor). Not yet validated end-to-end: pairwise configuration testing (REQ-QA-008, test matrix runs but boot-to-prompt depends on engine plumbing), cross-config save loading (REQ-QA-011, config fingerprint comparison stubbed), atomic save writes (REQ-QA-012, temp-file + rename implemented but not stress-tested under power loss).

**Source:** QA/Test engineering persona review (v3.0.0)
**Assessment:** Significant blind spots exist around OS state transitions, run loop
edge cases, configuration interactions, and platform-specific behavior.

### 12.1 OS State Transitions

#### REQ-QA-001: Suspend/Resume Handling

> **When** the host system resumes from suspend (laptop lid close, sleep),
> **the system shall** cap the per-frame elapsed time to a maximum of 100 ms,
> preventing massive engine step attempts or integer overflow in throttle math.
> Audio shall stabilize within 500 ms of resume.

**Priority:** Must | **Phase:** 1 | **Release:** A

#### REQ-QA-002: Display Hotplug

> **When** the host display topology changes (monitor unplugged/plugged, DPI
> scale change),
> **the system shall** handle the transition without crash. Rendering shall
> correct within 2 frames.

**Priority:** Should | **Phase:** 2 | **Release:** A

#### REQ-QA-003: Audio Device Change Mid-Session

> **When** the active audio device is removed,
> **the system shall** not crash and shall resume audio within 2 seconds when
> a new default device becomes available.

**Priority:** Should | **Phase:** 2 | **Release:** A

### 12.2 Run Loop Edge Cases

#### REQ-QA-005: Step Error Handling

> **When** `legends_step_ms()` returns a non-OK status,
> **the system shall** pause emulation, display the error (per REQ-ERROR-001),
> and not call capture or audio push for that frame. The user can resume, save
> state (for debugging), or quit.

**Priority:** Must | **Phase:** 1 | **Release:** A

#### REQ-QA-006: Dimension Change Debouncing

> **When** `legends_capture_rgb()` returns dimensions differing from the
> previous call,
> **the system shall** debounce by requiring 3 consecutive frames at the new
> resolution before recreating the context. Intermediate frames are dropped.

**Priority:** Must | **Phase:** 1 | **Release:** A

#### REQ-QA-007: Framebuffer Buffer Overrun Protection

> **The system shall** ensure `legends_capture_rgb()` never writes more than
> `fb_size` bytes, regardless of engine state changes between the size query
> and the actual capture.

**Priority:** Must | **Phase:** -1 | **Release:** A

### 12.3 Configuration Robustness

#### REQ-QA-008: Pairwise Configuration Testing

> **The system shall** use pairwise (all-pairs) testing to generate a test
> matrix covering 2-way interactions of CPU type, machine type, memory size,
> sound device, cycles, and video mode (~30-60 configs). Each config runs the
> boot-to-prompt integration test.

**Priority:** Must | **Phase:** 4 | **Release:** A

#### REQ-QA-009: Invalid Configuration Rejection

> **The system shall** run a validation pass after config parsing but before
> `legends_create()`, checking known-incompatible setting pairs. Invalid
> combinations produce user-visible warnings and fall back to safe defaults.

**Priority:** Must | **Phase:** 1 | **Release:** A

### 12.4 Save State Robustness

#### REQ-QA-011: Cross-Config Save Loading

> **When** loading a save state created with a different machine configuration,
> **the system shall** compare a config fingerprint (machine type, memory size,
> CPU type, sound device) and warn the user of mismatch. Loading must not crash.

**Priority:** Must | **Phase:** 2 | **Release:** A

#### REQ-QA-012: Atomic Save Writes

> **The system shall** write save states to a temporary file (`slot_N.sav.tmp`)
> and atomically rename to `slot_N.sav` only after successful write + fsync.
> Partial writes from power loss shall not corrupt existing saves.

**Priority:** Must | **Phase:** 2 | **Release:** A

### 12.5 Platform-Specific Quality

#### REQ-QA-015: Windows High-DPI Awareness

> **The Windows executable shall** include a DPI-aware manifest
> (`<dpiAware>true/pm</dpiAware>` or equivalent per-monitor awareness).
> Content renders at native resolution, not bitmap-scaled.

**Priority:** Must | **Phase:** 1 | **Release:** A

#### REQ-QA-016: macOS Retina Rendering

> **On macOS Retina displays**, the system shall correctly handle 2x drawable
> size. Golden snapshot tests shall normalize to logical resolution.

**Priority:** Should | **Phase:** 1 | **Release:** A

#### REQ-QA-017: Wayland Testing

> **Linux CI shall** include at least one native Wayland test run for UI smoke
> tests. Mouse capture shall be tested on both X11 and Wayland.

**Priority:** Should | **Phase:** 4 | **Release:** A

#### REQ-QA-018: Audio Backend Resilience

> **If** `audio_sink_->open()` fails,
> **the system shall** continue without audio and log a warning. Audio-dependent
> features become no-ops.

**Priority:** Must | **Phase:** 1 | **Release:** A

### 12.6 Thread Safety

#### REQ-QA-024: Thread Safety Contract

> **The roadmap shall** explicitly state the thread-safety contract for
> `legends_embed.h` API. If not thread-safe, the AI panel must queue capture
> requests to the main thread. A TSan CI build shall detect data races.

**Priority:** Must | **Phase:** 1 | **Release:** A

### 12.7 Test Reliability

#### REQ-QA-021: Frame Timing Test Tolerance

> **Frame timing verification shall** use widened tolerances for CI runners:
> ±250 ms for the 60-frame window, p95 variance < 8 ms. Timing tests should
> be "soft failures" (warnings, not build-breaking). Benchmark regression
> (REQ-TEST-009) remains a hard gate.

**Priority:** Must | **Phase:** 4 | **Release:** A

#### REQ-QA-019: Visual Regression with SSIM

> **Golden snapshot tests shall** use SSIM (structural similarity index) in
> addition to pixel-difference thresholds. Text-mode tests shall also compare
> via `legends_capture_text()` cell grids. Cursor blink shall be disabled for
> deterministic snapshots.

**Priority:** Must | **Phase:** 4 | **Release:** A

#### REQ-QA-020: Visual Diff Artifacts

> **On golden test failure**, CI shall produce expected/actual/diff-highlight
> images and upload them as CI artifacts.

**Priority:** Should | **Phase:** 4 | **Release:** A

### 12.8 Startup Failure Modes

#### REQ-QA-025: Graceful Startup Degradation

> **Each PAL service creation shall** be individually wrapped in error handling.
> Failure of non-essential services (audio) degrades gracefully. Failure of
> essential services (window, engine) produces user-visible error and clean exit.

**Priority:** Must | **Phase:** 1 | **Release:** A

---

## 13. User Experience & Accessibility — PARTIAL

> **Implementation status:** 2-3 of 11 requirements implemented. Implemented: host key concept (REQ-UX-003, hotkey dispatcher wired), keyboard menu navigation (REQ-UX-009, menu system supports keyboard). Partially implemented: autosave on crash (REQ-UX-010, crash breadcrumb exists but recovery-on-relaunch not wired). Scaffolded but not functional: DPI-aware scaling (REQ-UX-008, stub only), performance overlay (REQ-UX-005, stub only). Missing: first-run wizard (REQ-UX-001), drag-and-drop (REQ-UX-002), command palette (REQ-UX-004), GUI settings dialog (REQ-UX-006), per-game profiles (REQ-UX-007), hung guest detection (REQ-UX-011).

**Source:** End-user/DOS gamer persona review (v3.0.0)
**Assessment:** The roadmap focuses on engineering correctness but lacks attention to
first-run experience, discoverability, accessibility, and error recovery.

### 13.1 First-Run Experience

#### REQ-UX-001: First-Run Wizard

> **When** the application is launched for the first time (no config file found),
> **the system shall** display a guided first-run wizard allowing the user to:
> 1. Choose an execution profile (gaming, productivity, development)
> 2. Set data directories
> 3. Optionally import an existing DOSBox/DOSBox-X `.conf` file

**Priority:** Should | **Phase:** 2 | **Release:** A

#### REQ-UX-002: Drag-and-Drop Program Launch

> **When** a user drags a `.exe`, `.com`, `.bat`, or supported image file onto
> the application window,
> **the system shall** mount the containing directory and execute the program.

**Priority:** Should | **Phase:** 2 | **Release:** A

### 13.2 Host Key Concept

#### REQ-UX-003: Configurable Host Key Modifier

> **The system shall** support a configurable "host key" modifier (default:
> Right-Ctrl) that prefixes host-only hotkeys, preventing conflicts with guest
> programs. Example: HostKey+Delete = machine reset, bare Ctrl+Alt+Delete =
> sent to guest.

**Priority:** Should | **Phase:** 2 | **Release:** A

### 13.3 Discoverability

#### REQ-UX-004: In-App Command Palette

> **When** the user presses a designated hotkey (e.g., Ctrl+Shift+P),
> **the system shall** open a searchable command palette listing all available
> actions with their current hotkey bindings.

**Priority:** Could | **Phase:** 3 | **Release:** B

#### REQ-UX-005: Performance Overlay

> **When** enabled (via menu or hotkey),
> **the system shall** display a performance overlay showing current FPS,
> emulated cycles/ms, audio buffer fill level, and frame time.

**Priority:** Should | **Phase:** 2 | **Release:** A

### 13.4 Settings & Configuration UI

#### REQ-UX-006: GUI Settings Dialog

> **The system shall** provide a graphical settings dialog (accessible via
> Menu → Settings) covering machine type, CPU cycles, memory, sound device,
> display scaling, and key bindings — with live preview where applicable.

**Priority:** Should | **Phase:** 3 | **Release:** B

#### REQ-UX-007: Per-Game Configuration Profiles

> **The system shall** support per-game `.conf` overrides that are automatically
> loaded when a specific program is launched (matched by filename).

**Priority:** Could | **Phase:** 3 | **Release:** B

### 13.5 Accessibility

#### REQ-UX-008: DPI-Aware UI Scaling

> **All UI elements** (overlay menu, save dialog, AI panel, settings) shall
> render correctly at 100%, 150%, and 200% display scaling on all platforms.

**Priority:** Must | **Phase:** 2 | **Release:** A

#### REQ-UX-009: Keyboard-Only Navigation

> **All menus, dialogs, and panels shall** be fully navigable via keyboard
> (Tab, Arrow keys, Enter, Escape) without requiring mouse input.

**Priority:** Should | **Phase:** 2 | **Release:** A

### 13.6 Error Recovery

#### REQ-UX-010: Autosave on Crash

> **The system shall** perform an automatic save to a dedicated recovery slot
> before clean shutdown, and offer to restore on next launch after an unclean
> exit.

**Priority:** Should | **Phase:** 4 | **Release:** A

#### REQ-UX-011: Hung Guest Detection

> **When** the emulated CPU has not executed any new instructions for 5 seconds
> (potential infinite loop in guest code),
> **the system shall** display a non-intrusive notification offering the user
> options to reset, break into debugger, or continue waiting.

**Priority:** Could | **Phase:** 3 | **Release:** B

---

## 14. GPL v2 Process Isolation — MOSTLY COMPLETE

> **Implementation status:** 12-13 of 16 requirements implemented. License files (REQ-ISO-001, REQ-ISO-002), IPC message serialization library with wire format (REQ-ISO-003, REQ-ISO-004), engine host executable (REQ-ISO-005, REQ-ISO-006), shared memory framebuffer (REQ-ISO-007), shared memory audio ring buffer (REQ-ISO-008), control channel protocol (REQ-ISO-009), proxy library (REQ-ISO-010), compile-time backend switch (REQ-ISO-011), engine process spawning (REQ-ISO-012). Partial: crash recovery (REQ-ISO-013), heartbeat monitoring (REQ-ISO-014). Not started: license scanner CI (REQ-ISO-015), integration test suite for full IPC round-trip (REQ-ISO-016).

> **Design document:** `docs/design/GPL2_PROCESS_ISOLATION_DESIGN.md` (TDD-LIC-001)
>
> This section defines the requirements for isolating the GPL v2-licensed
> DOSBox-X engine (`aibox_core`) into a separate process, communicating with the
> proprietary-licensable application shell via an MIT-licensed IPC protocol.
> The architecture eliminates the "derivative work" linkage that currently forces
> the entire binary to be GPL v2 (see RISK-019, REQ-OPS-023).

### 14.1 License Files

#### REQ-ISO-001: GPL v2 License File

> **The repository shall** include a `COPYING` file at the project root
> containing the verbatim GNU General Public License v2 text, and a `LICENSE`
> file describing the multi-component license structure with SPDX identifiers.

**Acceptance criteria:**
1. `COPYING` contains the canonical FSF GPL v2 text (338 lines).
2. `LICENSE` lists per-directory SPDX identifiers and references `COPYING`.
3. Both files are installed alongside the binary by CMake.

**Priority:** Must | **Phase:** 0 | **Release:** A

#### REQ-ISO-002: NOTICE File with Copyright Attribution

> **The repository shall** include a `NOTICE` file at the project root listing
> all copyright holders (Charles Hoskinson, DOSBox Team, DOSBox-X Team),
> per-directory SPDX identifiers, and third-party dependency licenses.

**Acceptance criteria:**
1. `NOTICE` lists all copyright holders with years.
2. Every source directory has a corresponding SPDX identifier row.
3. All third-party dependencies (gsl-lite, GoogleTest, SDL2, SDL3) are listed
   with version, SPDX identifier, and upstream URL.

**Priority:** Must | **Phase:** 0 | **Release:** A

### 14.2 IPC Protocol

#### REQ-ISO-003: MIT-Licensed IPC Protocol Specification

> **The IPC protocol specification and header files in `include/legends_ipc/`
> shall** be released under the MIT license (SPDX: MIT), with no compile-time or
> link-time dependency on any GPL-licensed code.

**Acceptance criteria:**
1. `include/legends_ipc/` headers contain MIT SPDX header comments.
2. `legends_ipc` library compiles without any GPL object files on the link line.
3. License scanner CI job confirms MIT classification.

**Priority:** Must | **Phase:** 0 | **Release:** A

#### REQ-ISO-004: IPC Message Serialization Library

> **The project shall** provide a `legends_ipc` static library that serializes
> and deserializes all control messages (lifecycle, input, configuration) using a
> documented binary wire format with versioned message headers.

**Acceptance criteria:**
1. All message types have a `uint16_t msg_type` + `uint32_t payload_size` header.
2. Round-trip serialization unit tests pass for every message type.
3. Wire format is documented in `docs/design/GPL2_PROCESS_ISOLATION_DESIGN.md`.

**Priority:** Must | **Phase:** 0 | **Release:** A

### 14.3 Engine Host Process

#### REQ-ISO-005: Engine Host Executable

> **The project shall** produce a `legends_engine_host` executable that
> initializes the DOSBox-X engine, connects to the application shell via named
> pipe (control channel) and shared memory (framebuffer + audio), and runs the
> emulation loop.

**Acceptance criteria:**
1. `legends_engine_host` links `legends_core` + `legends_ipc` + `aibox_core`.
2. Executable accepts `--pipe <name>` and `--shm <name>` command-line arguments.
3. Integration test: engine host boots to DOS prompt and responds to IPC commands.

**Priority:** Must | **Phase:** 0 | **Release:** A

#### REQ-ISO-006: Engine Host GPL v2 Compliance

> **The `legends_engine_host` executable shall** be distributed under GPL v2
> terms, with the complete corresponding source code available per GPL v2
> Section 3.

**Acceptance criteria:**
1. `legends_engine_host` binary includes GPL v2 license notice on `--version`.
2. Source tarball generation is automated in CI.
3. `COPYING` is installed alongside the binary.

**Priority:** Must | **Phase:** 0 | **Release:** A

### 14.4 Shared Memory Framebuffer

#### REQ-ISO-007: Shared Memory Framebuffer

> **When** the engine host produces a new video frame, **the system shall**
> write the frame pixels into a shared memory region using a double-buffered
> scheme with atomic flip signaling, achieving zero-copy frame transfer.

**Acceptance criteria:**
1. Shared memory region sized for 2 × (max_width × max_height × 4) bytes.
2. Atomic `frame_index` counter incremented on each flip.
3. Frame latency < 1 ms measured from engine VSync to shell read.

**Priority:** Must | **Phase:** 1 | **Release:** A

### 14.5 Shared Memory Audio

#### REQ-ISO-008: Shared Memory Audio Ring Buffer

> **While** the engine is producing audio, **the system shall** write audio
> samples into a lock-free single-producer/single-consumer ring buffer in shared
> memory, with configurable buffer depth (default: 2048 frames at 44100 Hz).

**Acceptance criteria:**
1. Ring buffer uses atomic read/write indices (no mutexes).
2. Underrun detection: shell logs warning when ring buffer is empty for > 10 ms.
3. Overrun protection: oldest samples are dropped, not blocked.

**Priority:** Must | **Phase:** 1 | **Release:** A

### 14.6 Control Channel

#### REQ-ISO-009: Control Channel Protocol

> **The control channel shall** use a named pipe carrying length-prefixed binary
> messages for all non-bulk data: lifecycle commands (create, destroy, reset),
> input injection (key, mouse, text), configuration changes, and status queries.

**Acceptance criteria:**
1. Named pipe path follows platform convention (`\\.\pipe\legends_<pid>` on
   Windows, `/tmp/legends_<pid>.sock` on POSIX).
2. All messages are length-prefixed with the REQ-ISO-004 wire format.
3. Pipe supports bidirectional communication (request/response pairs).

**Priority:** Must | **Phase:** 1 | **Release:** A

### 14.7 Application Shell Proxy

#### REQ-ISO-010: Application Shell Proxy Library

> **The project shall** provide a `legends_proxy` static library that implements
> the `legends_embed.h` C API by forwarding calls over IPC to the engine host
> process, enabling the application shell to use the same API regardless of
> backend (monolithic or IPC-isolated).

**Acceptance criteria:**
1. `legends_proxy` implements every function in `legends_embed.h`.
2. `legends_proxy` links only `legends_ipc` (MIT) — no GPL dependencies.
3. Existing integration tests pass when linked against `legends_proxy` instead
   of `legends_core`.

**Priority:** Must | **Phase:** 1 | **Release:** A

#### REQ-ISO-011: Compile-Time Backend Switch

> **The build system shall** provide a `LEGENDS_USE_IPC` CMake option that
> switches the main executable between monolithic mode (linking `legends_core`
> directly) and IPC-isolated mode (linking `legends_proxy` + spawning
> `legends_engine_host`).

**Acceptance criteria:**
1. `cmake -DLEGENDS_USE_IPC=OFF` produces a single monolithic binary (status quo).
2. `cmake -DLEGENDS_USE_IPC=ON` produces `project_legends` + `legends_engine_host`.
3. CI matrix tests both configurations.

**Priority:** Must | **Phase:** 1 | **Release:** A

### 14.8 Process Lifecycle

#### REQ-ISO-012: Engine Process Spawning and Monitoring

> **When** the application shell starts, **the system shall** spawn the
> `legends_engine_host` process, establish IPC channels within 2 seconds, and
> monitor the child process for unexpected termination.

**Acceptance criteria:**
1. Spawn uses `CreateProcessW` (Windows) / `posix_spawn` (POSIX).
2. IPC handshake completes within 2 seconds or returns error.
3. Shell receives `SIGCHLD`/`WaitForSingleObject` notification on engine exit.

**Priority:** Must | **Phase:** 1 | **Release:** A

#### REQ-ISO-013: Engine Crash Detection and Recovery

> **If** the engine host process terminates unexpectedly (crash, kill, or IPC
> timeout > 5 seconds), **then the system shall** display an error dialog to the
> user, offer to restart the engine, and attempt to restore the last autosaved
> state.

**Acceptance criteria:**
1. Crash detected within 1 second of process termination.
2. Error dialog displays the engine exit code or signal.
3. Restart restores last autosave if available, otherwise starts fresh.

**Priority:** Should | **Phase:** 2 | **Release:** A

### 14.9 Performance

#### REQ-ISO-014: IPC Performance Budget Compliance

> **The IPC overhead (control channel + shared memory) shall** not exceed 5% of
> total frame time at 60 FPS (i.e., < 0.83 ms per frame), measured as the
> difference between monolithic and IPC-isolated mode on the reference benchmark.

**Acceptance criteria:**
1. Nightly benchmark measures IPC overhead on reference hardware.
2. p95 IPC latency < 0.83 ms per frame.
3. CI fails if overhead exceeds 5% for 3 consecutive nightly runs.

**Priority:** Must | **Phase:** 2 | **Release:** A

### 14.10 Platform Support and Verification

#### REQ-ISO-015: Cross-Platform IPC Implementation

> **The IPC implementation shall** support Windows (named pipes + shared memory
> via `CreateFileMapping`) and POSIX (Unix domain sockets + `shm_open`), with
> platform-specific code isolated behind a `legends_ipc` abstraction layer.

**Acceptance criteria:**
1. CI passes on Windows, Linux, and macOS.
2. Platform-specific code is confined to `src/legends_ipc/platform/`.
3. No `#ifdef _WIN32` in IPC protocol or serialization code.

**Priority:** Must | **Phase:** 1 | **Release:** A

#### REQ-ISO-016: GPL Object Code Isolation Verification

> **When** `LEGENDS_USE_IPC=ON`, **the CI pipeline shall** verify that the
> `project_legends` binary contains zero GPL-licensed object files by scanning
> the linker map file for any symbols from `aibox_core` or `legends_core`.

**Acceptance criteria:**
1. CI job parses linker map and fails if GPL symbols are present.
2. Only `legends_proxy` and `legends_ipc` (both MIT) appear in the link line.
3. `legends_engine_host` is verified to contain the GPL objects.

**Priority:** Must | **Phase:** 1 | **Release:** A

---

## 15. Wasm Sandbox — NOT STARTED

> **Implementation status:** 0 of 50 requirements implemented. Documentation only exists; no code written.

> **Requirements document:** `wasm.md`
>
> This section defines the requirements for running ProjectLegends in a
> Wasmtime-based WASI sandbox — a headless, capability-scoped runtime
> environment. The Wasm target enables deterministic emulation in sandboxed
> contexts (CI runners, cloud workers, embedding hosts) without GUI dependencies.
> GUI features remain outside initial Wasm scope unless a separate UI host
> architecture is approved (REQ-WASM-050).

### 15.1 Runtime and Toolchain

#### REQ-WASM-001: Wasmtime Primary Runtime

> **The project shall** support Wasmtime as the primary runtime for Wasm
> sandbox execution.

**Acceptance criteria:**
1. A Wasmtime host runner exists and can instantiate the ProjectLegends Wasm component.
2. Smoke test passes: create → step → capture → destroy lifecycle completes in Wasmtime.
3. Wasmtime version is pinned in repository-controlled toolchain files.

**Priority:** Must | **Phase:** 3 | **Release:** A

#### REQ-WASM-002: WASI Preview 2 Target ABI

> **The project shall** target WASI Preview 2 (Component Model) as the
> preferred ABI for Wasm builds.

**Acceptance criteria:**
1. Build produces a valid WASI Preview 2 component (`.wasm` artifact with component-model sections).
2. Component validates against `wasm-tools component validate`.
3. WIT interface is used for all host–guest communication.

**Priority:** Must | **Phase:** 3 | **Release:** A

#### REQ-WASM-003: WASI Preview 1 Fallback Build

> **Where** WASI Preview 2 toolchain support is incomplete for a target
> platform, **the project shall** keep an optional fallback build target for
> WASI Preview 1 during migration.

**Acceptance criteria:**
1. CMake preset or build script produces a WASI Preview 1 core module.
2. Fallback build is gated behind a build option (not default).
3. CI builds both Preview 1 and Preview 2 targets when fallback is enabled.

**Priority:** Should | **Phase:** 3 | **Release:** A

#### REQ-WASM-004: Wasm Tool Version Pinning

> **The project shall** pin Wasm-related tool versions (Wasmtime, wasm-tools,
> wit-bindgen, WASI SDK) in repository-controlled files.

**Acceptance criteria:**
1. A toolchain version manifest file (or CMake preset) lists exact versions for all Wasm tools.
2. CI installs tools from the pinned versions.
3. Version drift is detected by CI and fails the build.

**Priority:** Must | **Phase:** 3 | **Release:** A

#### REQ-WASM-005: Reproducible Wasm Build Path

> **The project shall** provide a reproducible build path (script or CMake
> preset) for Wasm artifacts.

**Acceptance criteria:**
1. A documented CMake preset or script produces Wasm artifacts from a clean checkout.
2. Two independent builds from the same commit produce byte-identical `.wasm` output (or documented exceptions).
3. Build instructions are tested in CI on at least one platform.

**Priority:** Must | **Phase:** 3 | **Release:** A

#### REQ-WASM-006: Host Prerequisite Documentation

> **The project shall** document host prerequisites for building and running
> Wasm targets on Windows, Linux, and macOS.

**Acceptance criteria:**
1. Documentation lists required tools, versions, and installation commands for each platform.
2. CI validates that documented steps produce a working build.
3. README or dedicated doc references the Wasm build instructions.

**Priority:** Must | **Phase:** 3 | **Release:** A

### 15.2 Component Interface — WIT

#### REQ-WASM-007: WIT Core Emulator Package

> **The project shall** define a WIT package (`wit/legends-emulator.wit`) for
> the stable "core emulator" surface.

**Acceptance criteria:**
1. `wit/` directory exists at the repository root with a versioned WIT package.
2. WIT package declares the `legends-emulator` world with all required interfaces.
3. Package validates with `wit-bindgen` or `wasm-tools`.

**Priority:** Must | **Phase:** 3 | **Release:** A

#### REQ-WASM-008: WIT Lifecycle Operations

> **The WIT surface shall** include lifecycle operations: `create`, `destroy`,
> and `reset`.

**Acceptance criteria:**
1. WIT interface declares `create`, `destroy`, and `reset` functions.
2. Functions map to the corresponding `legends_embed.h` C API calls.
3. Round-trip test: host calls create → reset → destroy without error.

**Priority:** Must | **Phase:** 3 | **Release:** A

#### REQ-WASM-009: WIT Stepping Operations

> **The WIT surface shall** include stepping operations: `step-ms` and
> `step-cycles`.

**Acceptance criteria:**
1. WIT interface declares `step-ms` and `step-cycles` functions with matching signatures.
2. `step-ms(100)` advances emulated time and returns cycle count.
3. Determinism: identical step sequences produce identical state hashes.

**Priority:** Must | **Phase:** 3 | **Release:** A

#### REQ-WASM-010: WIT Capture Operations

> **The WIT surface shall** include capture operations: `capture-text`,
> `capture-rgb`, and `is-frame-dirty`.

**Acceptance criteria:**
1. WIT interface declares all three capture functions.
2. `capture-text` returns a list of text cells matching `legends_capture_text()` output.
3. `capture-rgb` returns an RGB byte buffer matching `legends_capture_rgb()` output.

**Priority:** Must | **Phase:** 3 | **Release:** A

#### REQ-WASM-011: WIT Input Operations

> **The WIT surface shall** include input operations: `key-event`,
> `key-event-ext`, `text-input`, and `mouse-event`.

**Acceptance criteria:**
1. WIT interface declares all four input functions.
2. `text-input("DIR\n")` followed by step produces matching DOS output.
3. Input functions accept the same parameters as their C API counterparts.

**Priority:** Must | **Phase:** 3 | **Release:** A

#### REQ-WASM-012: WIT State Operations

> **The WIT surface shall** include state operations: `save-state`,
> `load-state`, and `get-state-hash`.

**Acceptance criteria:**
1. WIT interface declares all three state functions.
2. Save → load round-trip produces identical state hash.
3. State buffers are transported as `list<u8>` with bounded size.

**Priority:** Must | **Phase:** 3 | **Release:** A

#### REQ-WASM-013: WIT Error Type Mapping

> **Error and result types in the WIT interface shall** map deterministically
> from existing `LEGENDS_*` error codes.

**Acceptance criteria:**
1. WIT defines a `legends-error` variant type covering all `LEGENDS_ERR_*` codes.
2. Each WIT function returns `result<T, legends-error>`.
3. Error code round-trip test: trigger each error condition and verify correct variant.

**Priority:** Must | **Phase:** 3 | **Release:** A

#### REQ-WASM-014: WIT Variable-Size Output Transport

> **Any variable-size output in the WIT interface shall** use a deterministic
> and bounded transport pattern.

**Acceptance criteria:**
1. Capture and state functions use `list<u8>` or equivalent bounded type.
2. Maximum output sizes are documented in the WIT package.
3. Oversized output returns an error rather than truncating silently.

**Priority:** Must | **Phase:** 3 | **Release:** A

### 15.3 Sandbox and Capabilities

#### REQ-WASM-015: Default-Deny Capability Policy

> **Wasm execution shall** be deny-by-default for all host capabilities.

**Acceptance criteria:**
1. A capability policy file exists with a default-deny profile.
2. Wasmtime host runner applies the policy before instantiation.
3. Attempting an ungrantable operation (e.g., network) from guest code produces a trap.

**Priority:** Must | **Phase:** 3 | **Release:** A

#### REQ-WASM-016: Network Access Disabled by Default

> **Network access shall** be disabled by default for Wasm instances.

**Acceptance criteria:**
1. Default capability policy does not grant `wasi:sockets` or equivalent.
2. Guest code attempting socket operations receives a denied error.
3. Network access can be explicitly enabled via policy override for testing.

**Priority:** Must | **Phase:** 3 | **Release:** A

#### REQ-WASM-017: Environment Variable Allowlisting

> **Environment variable access shall** be allowlisted and explicit for Wasm
> instances.

**Acceptance criteria:**
1. Only variables listed in the capability policy are visible to the guest.
2. Unlisted environment variables return empty/absent.
3. Default policy exposes zero environment variables.

**Priority:** Should | **Phase:** 3 | **Release:** A

#### REQ-WASM-018: Preopened Directory Filesystem Access

> **Filesystem access shall** be limited to explicit preopened directories only.

**Acceptance criteria:**
1. Guest code can only access directories listed in the preopened configuration.
2. Attempting to access paths outside preopened directories returns a permission error.
3. Preopened directories are configured via the capability policy file.

**Priority:** Must | **Phase:** 3 | **Release:** A

#### REQ-WASM-019: Platform Directory Mapping

> **Preopened directory policy shall** map to existing ProjectLegends platform
> directories: config, data (saves, captures), logs/state, and cache.

**Acceptance criteria:**
1. Policy file maps guest paths to host platform directories per Appendix D.
2. Each directory category (config, data, logs, cache) has a dedicated guest mount point.
3. Mapping is documented and tested on Windows, Linux, and macOS.

**Priority:** Must | **Phase:** 3 | **Release:** A

#### REQ-WASM-020: Per-Directory Read/Write Mode

> **Where** fine-grained filesystem control is configured, **the project shall**
> support configurable read/write mode per preopened directory.

**Acceptance criteria:**
1. Policy file supports `readonly` and `readwrite` flags per directory.
2. Config directory defaults to read-only; data directory defaults to read-write.
3. Write attempt to a read-only directory returns a permission error.

**Priority:** Should | **Phase:** 3 | **Release:** A

#### REQ-WASM-021: Path Traversal and Symlink Blocking

> **If** a guest path contains traversal sequences (`../`) or follows symlinks
> outside the preopened root, **then the runtime shall** block the access and
> return a permission error.

**Acceptance criteria:**
1. Path traversal test: guest opens `../../etc/passwd` — access denied.
2. Symlink escape test: symlink inside preopened dir pointing outside — access denied.
3. Tests run on all three platforms in CI.

**Priority:** Must | **Phase:** 4 | **Release:** A

#### REQ-WASM-022: Explicit Clock Usage

> **While** deterministic mode is active, **the Wasm guest shall** not depend on
> wall-clock time; clock access shall be explicit and controlled by the host.

**Acceptance criteria:**
1. Deterministic mode does not grant `wasi:clocks/wall-clock`.
2. Guest uses only host-provided emulated time via the WIT interface.
3. Determinism test passes with identical hashes across runs.

**Priority:** Must | **Phase:** 3 | **Release:** A

### 15.4 Execution Model

#### REQ-WASM-023: Host-Authoritative Run Loop

> **The host shall** remain authoritative for the run loop and pacing when
> running Wasm instances.

**Acceptance criteria:**
1. Host calls `step-ms` or `step-cycles` to drive emulation — guest never self-advances.
2. Guest has no access to timers or scheduling primitives.
3. Run loop pacing is identical to native headless mode.

**Priority:** Must | **Phase:** 3 | **Release:** A

#### REQ-WASM-024: Serialized API Calls

> **API calls for a single emulator instance shall** be serialized in Wasm mode.

**Acceptance criteria:**
1. Concurrent calls from multiple host threads are prevented (single-threaded Wasm instance).
2. Attempting overlapping calls returns an error or is serialized by the host runner.
3. Thread safety model is documented.

**Priority:** Must | **Phase:** 3 | **Release:** A

#### REQ-WASM-025: Single-Instance Constraint in Wasm

> **Single-instance constraints shall** remain explicit in V1 Wasm mode unless
> the global constraint is revised.

**Acceptance criteria:**
1. Only one emulator instance per Wasm component instantiation.
2. Second `create` call returns an error.
3. Constraint is documented in the WIT package.

**Priority:** Must | **Phase:** 3 | **Release:** A

#### REQ-WASM-026: Deterministic State Hash Reproducibility

> **Deterministic mode shall** produce reproducible state hashes across repeated
> runs with identical inputs in Wasm mode.

**Acceptance criteria:**
1. Same config + input trace + step schedule → identical `get-state-hash` output.
2. Native headless and Wasm headless produce the same hash for the same inputs.
3. CI runs determinism comparison test on every build.

**Priority:** Must | **Phase:** 3 | **Release:** A

#### REQ-WASM-027: Guest Trap Structured Error Surfacing

> **If** the Wasm guest traps (unreachable, out-of-bounds, stack overflow),
> **then the host shall** surface the trap as a structured error without
> terminating the host process.

**Acceptance criteria:**
1. Guest trap produces a host-side error with trap type, message, and stack trace (if available).
2. Host process remains alive and can instantiate a new guest.
3. Trap error is logged via the structured logging system.

**Priority:** Must | **Phase:** 3 | **Release:** A

### 15.5 Resource Governance

#### REQ-WASM-028: Per-Instance Memory Limits

> **The host shall** configure memory limits per Wasm instance.

**Acceptance criteria:**
1. Maximum linear memory is configurable (default: 256 MB).
2. Guest exceeding the limit traps with an out-of-memory error.
3. Memory limit is enforced by Wasmtime's `Store` configuration.

**Priority:** Must | **Phase:** 4 | **Release:** A

#### REQ-WASM-029: Execution Budget Controls

> **The host shall** configure execution budget controls (fuel, epoch
> interruption, or timeout policy) per Wasm instance.

**Acceptance criteria:**
1. At least one budget mechanism (fuel or epoch) is configurable.
2. Exceeding the budget produces a structured error (not a host crash).
3. Budget is reset between step calls or configurable per-call.

**Priority:** Must | **Phase:** 4 | **Release:** A

#### REQ-WASM-030: Bounded Queue and Buffer Enforcement

> **The host shall** enforce bounded queue and buffer behavior for input, audio,
> and capture data paths in Wasm mode.

**Acceptance criteria:**
1. Input queue has a configurable maximum depth.
2. Capture buffers have documented maximum sizes.
3. Exceeding a bound returns an error or drops oldest entries (documented behavior).

**Priority:** Must | **Phase:** 4 | **Release:** A

#### REQ-WASM-031: Limit Exhaustion Behavior

> **When** a resource limit (memory, fuel, queue depth) is exhausted, **the host
> shall** provide explicit behavior: error, throttle, or stop — as configured.

**Acceptance criteria:**
1. Each resource limit has a documented exhaustion policy.
2. Default policy is to return a structured error.
3. CI tests trigger each limit and verify correct behavior.

**Priority:** Must | **Phase:** 4 | **Release:** A

### 15.6 Security

#### REQ-WASM-032: Wasm Artifact Integrity Verification

> **When** loading a Wasm artifact in release flows, **the host shall** verify
> its integrity via checksum before execution.

**Acceptance criteria:**
1. Release artifacts include a SHA-256 checksum manifest.
2. Host runner verifies checksum before instantiation.
3. Checksum mismatch aborts execution with a clear error message.

**Priority:** Must | **Phase:** 4 | **Release:** A

#### REQ-WASM-033: SBOM for Wasm Deliverables

> **The build pipeline shall** produce SBOM (Software Bill of Materials) data
> for Wasm deliverables.

**Acceptance criteria:**
1. CI generates an SBOM file (SPDX or CycloneDX format) for each Wasm release.
2. SBOM lists all compiled-in dependencies and their versions.
3. SBOM is published alongside release artifacts.

**Priority:** Should | **Phase:** 4 | **Release:** A

#### REQ-WASM-034: Unsafe Host Import Prohibition

> **Unsafe host imports shall** be prohibited by policy in production Wasm
> profiles.

**Acceptance criteria:**
1. Production capability policy does not grant any imports outside the defined WIT interface.
2. CI validates that the Wasm component imports only allowed interfaces.
3. Adding an unauthorized import fails the CI build.

**Priority:** Must | **Phase:** 4 | **Release:** A

#### REQ-WASM-035: AI Feature Network Capability Isolation

> **If** AI-related features are enabled in Wasm mode, **then the emulator
> component shall not** be implicitly granted network capability.

**Acceptance criteria:**
1. AI features route through a separate host-side service, not guest network access.
2. Emulator Wasm component has no `wasi:sockets` grant even when AI is enabled.
3. Test verifies network denial with AI feature flag on.

**Priority:** Must | **Phase:** 4 | **Release:** A

### 15.7 Observability

#### REQ-WASM-036: Structured Runtime Logging

> **The host shall** capture structured runtime logs including runtime version,
> component version, capability grants, and major lifecycle events.

**Acceptance criteria:**
1. Log entries are structured (JSON or key-value format).
2. Logs include Wasmtime version, component version, and granted capabilities.
3. Lifecycle events (create, destroy, trap, limit exhaustion) are logged.

**Priority:** Should | **Phase:** 4 | **Release:** A

#### REQ-WASM-037: Per-Run Metrics

> **The host shall** expose per-run metrics: startup time, step throughput,
> memory usage, and trap/error counts.

**Acceptance criteria:**
1. Metrics are collected and accessible via a host API or log output.
2. Startup time measures instantiation to first step completion.
3. Step throughput measures cycles per wall-clock second.

**Priority:** Should | **Phase:** 4 | **Release:** A

#### REQ-WASM-038: Determinism Verification Reports

> **Determinism verification reports shall** include hash values, seed
> configuration, and input metadata.

**Acceptance criteria:**
1. Report includes: config hash, input trace hash, final state hash, step count.
2. Report format is machine-readable (JSON).
3. CI determinism test produces and archives the report.

**Priority:** Must | **Phase:** 4 | **Release:** A

### 15.8 CI and Verification

#### REQ-WASM-039: Wasm CI Build Pipeline

> **CI shall** build Wasm artifacts on supported host platforms.

**Acceptance criteria:**
1. CI job builds Wasm component on at least Linux (primary) and one additional platform.
2. Build artifacts are published as CI artifacts.
3. Build failure blocks merge.

**Priority:** Must | **Phase:** 3 | **Release:** A

#### REQ-WASM-040: Native/Wasm Functional Parity Checks

> **CI shall** run functional parity checks between native headless and
> Wasmtime headless APIs.

**Acceptance criteria:**
1. Same test suite runs against both native and Wasm backends.
2. State hashes match for identical input traces.
3. Parity failures block merge.

**Priority:** Must | **Phase:** 4 | **Release:** A

#### REQ-WASM-041: Determinism Replay in Wasmtime

> **CI shall** run determinism replay checks in Wasmtime mode.

**Acceptance criteria:**
1. Record input trace in native mode, replay in Wasmtime mode.
2. Final state hash matches between native and Wasm replay.
3. Test runs on every merge to main.

**Priority:** Must | **Phase:** 4 | **Release:** A

#### REQ-WASM-042: Sandbox Policy Denial Tests

> **CI shall** run sandbox policy tests that assert denied capabilities are
> actually denied.

**Acceptance criteria:**
1. Test attempts network access — denied.
2. Test attempts filesystem access outside preopened dirs — denied.
3. Test attempts environment variable access for unlisted vars — returns empty.

**Priority:** Must | **Phase:** 4 | **Release:** A

#### REQ-WASM-043: WIT Interface Version Guard

> **When** WIT interfaces change, **CI shall** fail if the change lacks a
> version bump and changelog entry.

**Acceptance criteria:**
1. CI compares WIT files against the previous release tag.
2. If WIT content differs, CI checks for version bump in the WIT package.
3. Missing version bump or changelog entry fails the build.

**Priority:** Must | **Phase:** 4 | **Release:** A

### 15.9 Packaging and Distribution

#### REQ-WASM-044: Wasm Distribution Artifacts

> **Distribution shall** include the Wasm component/module artifact, host
> runner binary or integration instructions, and a checksum manifest.

**Acceptance criteria:**
1. Release package contains `.wasm` artifact, host runner (or instructions), and `checksums.sha256`.
2. Checksum manifest covers all distributed files.
3. CI produces the complete distribution package on release tags.

**Priority:** Must | **Phase:** 4 | **Release:** A

#### REQ-WASM-045: Dual Version Tracking

> **Versioning shall** be explicit for both runtime compatibility and WIT
> interface compatibility.

**Acceptance criteria:**
1. Release notes state both the project version and the WIT interface version.
2. WIT package version follows semantic versioning independently of the project version.
3. Breaking WIT changes require a major version bump.

**Priority:** Must | **Phase:** 4 | **Release:** A

#### REQ-WASM-046: Wasmtime Compatibility Range Documentation

> **Release notes shall** state the supported Wasmtime compatibility range.

**Acceptance criteria:**
1. Each release documents the minimum and maximum tested Wasmtime versions.
2. CI tests against the documented range boundaries.
3. Compatibility range is visible in README or release notes.

**Priority:** Should | **Phase:** 4 | **Release:** A

### 15.10 Rollout Plan

#### REQ-WASM-047: Phase 1 MVP Headless Runner

> **Phase 1 (MVP) shall** deliver a headless-only Wasmtime runner with core
> lifecycle, stepping, capture, and state APIs.

**Acceptance criteria:**
1. Host runner instantiates Wasm component and completes full API lifecycle.
2. All WIT lifecycle, stepping, capture, and state operations function correctly.
3. Determinism test passes in Wasm mode.

**Priority:** Must | **Phase:** 3 | **Release:** A

#### REQ-WASM-048: Phase 2 Capability Hardening Gate

> **Phase 2 shall** deliver capability hardening and CI parity gates before
> Wasm artifacts are included in release distributions.

**Acceptance criteria:**
1. All sandbox policy denial tests pass (REQ-WASM-042).
2. Native/Wasm functional parity checks pass (REQ-WASM-040).
3. Resource governance controls are implemented and tested (REQ-WASM-028 through REQ-WASM-031).

**Priority:** Must | **Phase:** 4 | **Release:** A

#### REQ-WASM-049: Phase 3 Advanced Wasm Features

> **Where** demand exists, **Phase 3 may** deliver optional advanced features:
> audio extraction, richer mount policy, and replay tooling in Wasm mode.

**Acceptance criteria:**
1. Audio capture via WIT interface produces valid PCM data.
2. Mount policy supports per-directory read/write/deny granularity.
3. Replay tooling can record and replay input traces in Wasm mode.

**Priority:** Could | **Phase:** 4 | **Release:** B

#### REQ-WASM-050: GUI Scope Exclusion

> **GUI features shall** remain outside initial Wasm scope unless a separate
> UI host architecture is approved.

**Acceptance criteria:**
1. Wasm build does not include or require any GUI/windowing dependencies.
2. WIT interface does not expose window, context, or display operations.
3. Documentation clearly states the headless-only scope.

**Priority:** Must | **Phase:** 3 | **Release:** A

---

## 16. Full EARS Requirements Catalogue

> **Summary (as of 2026-02-28):** 220 tracked requirements.
> **Done:** 136 | **Stub:** 4 | **Missing:** 80
> Breakdown: Phases -1/0/1/4 complete; Phase 2 partial (5 missing); Phase 3 partial (6 missing/stub); Security 6/22; Isolation 2/16; Wasm 0/50; UX 2/11.

This section consolidates all requirements in a flat, searchable table with
OpenSpec identifiers.

### 16.1 Notation

Requirements use EARS patterns:

| Pattern | Template |
|---------|----------|
| **Ubiquitous** | The system shall `<requirement>` |
| **Event-driven** | **When** `<trigger>`, the system shall `<response>` |
| **State-driven** | **While** `<state>`, the system shall `<requirement>` |
| **Optional** | **Where** `<feature>`, the system shall `<requirement>` |
| **Unwanted** | **If** `<condition>`, then the system shall `<mitigation>` |

### 16.2 Requirements Table

| ID | Category | EARS Pattern | Summary | Phase | Priority | Release | Status |
|----|----------|-------------|---------|-------|----------|---------|--------|
| REQ-PLUMB-001 | Plumbing | State-driven | Engine framebuffer sync (real VRAM, not test pattern) | -1 | Must | A | **Done** |
| REQ-PLUMB-002 | Plumbing | State-driven | Real text-mode font rendering (VGA ROM glyphs) | -1 | Must | A | **Done** |
| REQ-PLUMB-003 | Plumbing | Optional | Engine audio path activation (sound_enabled=true) | -1 | Must | A | **Done** |
| REQ-PLUMB-004 | Plumbing | Ubiquitous | Audio sample transfer interface (engine→app→PAL) | -1 | Must | A | **Done** |
| REQ-PLUMB-005 | Plumbing | Ubiquitous | Presentation contract enforcement test | -1 | Must | A | **Done** |
| REQ-BUILD-001 | Build | Optional | SDL3 executable CMake target | 0 | Must | A | **Done** |
| REQ-BUILD-002 | Build | Ubiquitous | Minimal main.cpp with window + event loop | 0 | Must | A | **Done** |
| REQ-BUILD-003 | Build | Ubiquitous | Cross-platform CI (Win/Linux/macOS) | 0 | Must | A | **Done** |
| REQ-BUILD-004 | Build | Ubiquitous | Application class skeleton | 0 | Must | A | **Done** |
| REQ-BUILD-005 | Build | Ubiquitous | Packaging skeleton (CPack + CI artifacts) | 0 | Must | A | **Done** |
| REQ-CORE-001 | Core | Event-driven | Engine initialization via legends_create() with profile presets | 1 | Must | A | **Done** |
| REQ-CORE-002 | Core | State-driven | Run loop stepping at ~60 FPS | 1 | Must | A | **Done** |
| REQ-CORE-003 | Core | Event-driven | Clean shutdown (destroy + Platform::shutdown) | 1 | Must | A | **Done** |
| REQ-VIDEO-001 | Video | State-driven | Framebuffer capture and display (RGB blit with format conversion) | 1 | Must | A | **Done** |
| REQ-VIDEO-002 | Video | Event-driven | Dynamic resolution handling (destroy/recreate context) | 1 | Must | A | **Done** |
| REQ-VIDEO-003 | Video | Event-driven | Window resize with aspect ratio preservation | 1 | Should | A | **Done** |
| REQ-INPUT-001 | Input | Event-driven | Keyboard SDL→AT Set 1 translation + injection | 1 | Must | A | **Done** |
| REQ-INPUT-002 | Input | Event-driven | Mouse input translation + injection | 1 | Must | A | **Done** |
| REQ-INPUT-003 | Input | Event-driven | Mouse capture toggle (Ctrl+F10 / middle mouse) | 1 | Must | A | **Done** |
| REQ-AUDIO-001 | Audio | State-driven | Audio output via push model | 1 | Must | A | **Done** |
| REQ-AUDIO-002 | Audio | Ubiquitous | Volume control | 1 | Should | A | **Done** |
| REQ-THROTTLE-001 | Core | State-driven | Frame pacing with spin-wait hybrid (~60 FPS) | 1 | Must | A | **Done** |
| REQ-CONFIG-001 | Config | Event-driven | .conf file loading | 1 | Must | A | **Done** |
| REQ-CONFIG-002 | Config | Optional | Default config file search paths (XDG-aware) | 1 | Should | A | **Done** |
| REQ-CLI-001 | CLI | Ubiquitous | Command-line argument parsing (with --profile) | 1 | Must | A | **Done** |
| REQ-MENU-001 | Menu | Optional | Enhanced menu bar with dropdowns (app-layer, via ActionBus) | 2 | Must | A | **Done** |
| REQ-MENU-002 | Menu | Optional | Fallback overlay menu (via ActionBus) | 2 | Must | A | **Done** |
| REQ-MENU-003 | Menu | Event-driven | Pause emulation on menu open | 2 | Should | A | **Done** |
| REQ-SAVE-001 | Save | Event-driven | Save state to file (9 slots, Ctrl+Shift+F1..F9) | 2 | Must | A | **Done** |
| REQ-SAVE-002 | Save | Event-driven | Load state from file (9 slots, Ctrl+Alt+F1..F9) | 2 | Must | A | **Done** |
| REQ-SAVE-003 | Save | Ubiquitous | Save slot UI with thumbnails (9 slots) | 2 | Should | A | **Done** |
| REQ-SAVE-004 | Save | Ubiquitous | Platform-appropriate save directory (XDG data) | 2 | Must | A | **Done** |
| REQ-MAPPER-001 | Input | Event-driven | Interactive key mapper UI | 2 | Must | A | **Done** |
| REQ-MAPPER-002 | Input | Ubiquitous | Mapper persistence (mapper.txt in config dir) | 2 | Must | A | **Done** |
| REQ-MAPPER-003 | Input | Ubiquitous | Default SDL3→AT Set 1 scancode table | 2 | Must | A | **Done** |
| REQ-CAPTURE-001 | Capture | Event-driven | Screenshot to PNG | 2 | Must | A | **Done** |
| REQ-CAPTURE-002 | Capture | Ubiquitous | Capture directory (XDG data, platform paths) | 2 | Must | A | **Done** |
| REQ-PAUSE-001 | Core | Event-driven | Pause/resume emulation | 2 | Must | A | **Done** |
| REQ-RESET-001 | Core | Event-driven | Machine reset (legends_reset) | 2 | Must | A | **Done** |
| REQ-MOUNT-001 | Mounting | Event-driven | Host directory mounting (drive letter) | 2 | Must | A | **Done** |
| REQ-MOUNT-002 | Mounting | Optional | Block device image mounting (.iso, .img, .cue/.bin) | 2 | Must | A | **Done** |
| REQ-INPUT-004 | Input | Event-driven | Clipboard paste (host→guest keystroke injection) | 2 | Should | A | **Done** |
| REQ-CAPTURE-003 | Capture | Event-driven | Video capture streaming (AVI/ZMBV + audio) | 2 | Should | A | **Done** |
| REQ-SHADER-001 | Video | Optional | OpenGL shader rendering path | 3 | Should | B | **Done** |
| REQ-SHADER-002 | Video | Ubiquitous | Shader preset selection | 3 | Should | B | **Done** |
| REQ-AI-001 | AI | Ubiquitous | AI assistant panel (opt-in, async, non-blocking) | 3 | Must | B | **Done** |
| REQ-AI-002 | AI | Event-driven | AI screen context (text capture) | 3 | Must | B | **Done** |
| REQ-AI-003 | AI | Ubiquitous | AI backend configuration (with privacy mode) | 3 | Must | B | **Done** |
| REQ-PRINT-001 | Peripheral | Ubiquitous | Printer emulation (LPT1 to file) | 3 | Could | B | Missing |
| REQ-MIDI-001 | Audio | Optional | MIDI output routing | 3 | Could | B | Stub |
| REQ-TTF-001 | Video | Optional | TrueType font rendering in text mode | 3 | Could | B | **Done** |
| REQ-FULLSCREEN-001 | Video | Event-driven | Fullscreen toggle (Alt+Enter) | 3 | Must | B | **Done** |
| REQ-JOYSTICK-001 | Input | Event-driven | Joystick/gamepad support | 3 | Should | B | **Done** |
| REQ-NET-001 | Network | Optional | IPX network emulation over UDP | 3 | Could | B | Stub |
| REQ-HW-001 | Hardware | Optional | 3dfx Voodoo / Glide → OpenGL translation | 3 | Could | B | Stub |
| REQ-HW-002 | Hardware | Optional | NEC PC-98 architecture support | 3 | Could | B | Stub |
| REQ-AUDIO-003 | Audio | Optional | Advanced MIDI synthesis (FluidSynth / MUNT MT-32) | 3 | Should | B | Missing |
| REQ-TEST-001 | Testing | Ubiquitous | Unit test coverage (>80% for src/app/) | 4 | Must | A | **Done** |
| REQ-TEST-002 | Testing | Ubiquitous | Integration test — boot to prompt | 4 | Must | A | **Done** |
| REQ-TEST-003 | Testing | Ubiquitous | Determinism verification test | 4 | Must | A | **Done** |
| REQ-TEST-004 | Testing | Ubiquitous | Golden visual snapshot tests | 4 | Must | A | **Done** |
| REQ-TEST-005 | Testing | Ubiquitous | Audio validation (spectral + buffer) tests | 4 | Must | A | **Done** |
| REQ-TEST-006 | Testing | Ubiquitous | Replay determinism test | 4 | Should | A | **Done** |
| REQ-TEST-007 | Testing | Ubiquitous | Cross-platform UI smoke test (scripted) | 4 | Should | A | **Done** |
| REQ-TEST-008 | Testing | Ubiquitous | Soak testing (12-24hr endurance, memory + audio) | 4 | Should | A | **Done** |
| REQ-TEST-009 | Testing | Ubiquitous | Performance regression benchmarking (IPS baseline) | 4 | Must | A | **Done** |
| REQ-TEST-010 | Testing | Ubiquitous | Fuzz testing (config, input, save state, network) | 4 | Should | A | **Done** |
| REQ-TEST-011 | Testing | Ubiquitous | Save state forward-compatibility matrix | 4 | Must | A | **Done** |
| REQ-TEST-012 | Testing | Optional | Deterministic rendering validation (SSIM for shaders/3dfx) | 4 | Should | B | **Done** |
| REQ-PACKAGE-001 | Package | Ubiquitous | Windows installer (MSI/NSIS) | 4 | Must | A | **Done** |
| REQ-PACKAGE-002 | Package | Ubiquitous | Linux AppImage | 4 | Must | A | **Done** |
| REQ-PACKAGE-003 | Package | Ubiquitous | macOS .app bundle | 4 | Must | A | **Done** |
| REQ-PACKAGE-004 | Package | Optional | Portable mode (portable.txt) | 4 | Should | A | **Done** |
| REQ-LOG-001 | Logging | Ubiquitous | Structured logging (stderr + file, XDG state) | 4 | Must | A | **Done** |
| REQ-ERROR-001 | Error | Event-driven | User-facing error reporting | 4 | Must | A | **Done** |
| **Security** | | | | | | | |
| REQ-SEC-001 | Security | Optional | IPX listener binds to localhost by default | 3 | Must | B | Missing |
| REQ-SEC-002 | Security | Ubiquitous | IPX packet size and rate limits | 3 | Should | B | Missing |
| REQ-SEC-005 | Security | Ubiquitous | TLS certificate verification for AI connections | 3 | Must | B | **Done** |
| REQ-SEC-006 | Security | Unwanted | Prohibit raw API keys in config files | 3 | Must | B | **Done** |
| REQ-SEC-008 | Security | Ubiquitous | AI response markdown sanitization | 3 | Should | B | **Done** |
| REQ-SEC-010 | Security | Event-driven | Save state header + CRC-32 validation | 2 | Must | A | **Done** |
| REQ-SEC-011 | Security | Unwanted | Save state maximum file size (256 MB) | 2 | Must | A | **Done** |
| REQ-SEC-013 | Security | Event-driven | CWD config file warning | 1 | Should | A | **Done** |
| REQ-SEC-014 | Security | Ubiquitous | Config parser field length limits | 1 | Should | A | **Done** |
| REQ-SEC-016 | Security | Ubiquitous | Image parser validation (FAT cycle, depth limit) | 2 | Must | A | **Done** |
| REQ-SEC-018 | Security | Ubiquitous | Prompt injection separation in AI context | 3 | Must | B | **Done** |
| REQ-SEC-023 | Security | Ubiquitous | Canonical path resolution for mounts | 2 | Must | A | **Done** |
| REQ-SEC-024 | Security | Optional | Read-only mount option | 2 | Must | A | **Done** |
| REQ-SEC-025 | Security | Event-driven | Sensitive directory mount warning | 2 | Should | A | **Done** |
| REQ-SEC-027 | Security | Ubiquitous | Third-party dependency version pinning | 0 | Must | A | **Done** |
| REQ-SEC-028 | Security | Ubiquitous | Automated dependency vulnerability scanning | 0 | Should | A | **Done** |
| REQ-SEC-031 | Security | Ubiquitous | Formal threat model document | 0 | Must | A | **Done** |
| REQ-SEC-035 | Security | Ubiquitous | Cross-platform code signing (Authenticode, notarize, GPG) | 4 | Must | A | **Done** (runbook) |
| REQ-SEC-036 | Security | Ubiquitous | SHA-256 checksum publication with releases | 4 | Should | A | **Done** |
| REQ-SEC-038 | Security | Unwanted | Custom shader file validation (64 KB max) | 3 | Should | B | Missing |
| REQ-SEC-039 | Security | Unwanted | SoundFont/ROM file size limits | 3 | Should | B | Missing |
| REQ-SEC-040 | Security | Ubiquitous | Restrictive log file permissions + rotation | 4 | Should | A | **Done** |
| **Embedding API** | | | | | | | |
| REQ-API-001 | API | Ubiquitous | Embedding feature parity guarantee | 1 | Must | A | **Done** |
| REQ-API-002 | API | Ubiquitous | `legends_capture_audio()` — audio capture C API | -1 | Must | A | **Done** |
| REQ-API-003 | API | Ubiquitous | `legends_is_audio_ready()` — audio readiness query | -1 | Should | A | **Done** |
| REQ-API-004 | API | Ubiquitous | `legends_mount_drive()` / `legends_unmount_drive()` | 2 | Must | A | **Done** |
| REQ-API-005 | API | Ubiquitous | Runtime drive swap (mount/unmount between steps) | 2 | Should | A | Missing |
| REQ-API-006 | API | Optional | Engine event callback registration | 2 | Should | A | **Done** |
| REQ-API-007 | API | Ubiquitous | Multi-instance embedding guidance documentation | 4 | Should | A | **Done** |
| REQ-API-009 | API | Ubiquitous | Cross-thread capture safety documentation | 1 | Must | A | **Done** |
| REQ-API-011 | API | Ubiquitous | `legends_has_capability()` runtime feature query | 1 | Should | A | **Done** |
| REQ-API-013 | API | Ubiquitous | `legends_step_result_t` extensibility (reserved fields) | 1 | Must | A | **Done** |
| REQ-API-014 | API | Ubiquitous | `LEGENDS_API` DLL export macro | 0 | Should | A | **Done** |
| **Operational Infrastructure** | | | | | | | |
| REQ-OPS-001 | Operations | Ubiquitous | SDL3 version pinning (tag/SHA) | 0 | Must | A | **Done** |
| REQ-OPS-002 | Operations | Ubiquitous | Hermetic CI builds (SDL3 from source/cache) | 0 | Must | A | **Done** |
| REQ-OPS-003 | Operations | Ubiquitous | Centralized dependency version manifest | 0 | Should | A | **Done** |
| REQ-OPS-004 | Operations | Ubiquitous | Tiered CI pipeline (per-PR/merge/nightly/release) | 0 | Must | A | **Done** |
| REQ-OPS-005 | Operations | Ubiquitous | Build caching (SDL3 + aibox_core) | 0 | Should | A | **Done** |
| REQ-OPS-007 | Operations | Ubiquitous | Artifact naming convention (semver+platform+arch) | 4 | Must | A | **Done** |
| REQ-OPS-008 | Operations | Ubiquitous | Windows Authenticode code signing | 4 | Must | A | Missing |
| REQ-OPS-014 | Operations | Ubiquitous | Two-mode fuzz testing (per-PR regression + nightly) | 4 | Must | A | **Done** |
| REQ-OPS-015 | Operations | Ubiquitous | Fuzz crash corpus checked into repo | 4 | Must | A | **Done** |
| REQ-OPS-017 | Operations | Optional | Opt-in update check (Sparkle/WinSparkle) | 4 | Should | A | **Done** |
| REQ-OPS-019 | Operations | Ubiquitous | Release branch model with hotfix flow | 0 | Must | A | **Done** |
| REQ-OPS-020 | Operations | Ubiquitous | Semantic versioning derived from Git tags | 0 | Must | A | **Done** |
| REQ-OPS-022 | Operations | Ubiquitous | LICENSES/ directory + NOTICE with SPDX | 4 | Must | A | **Done** |
| REQ-OPS-023 | Operations | Ubiquitous | GPL v2 compliance analysis for aibox_core | 0 | Must | A | **Done** |
| REQ-OPS-024 | Operations | Ubiquitous | Dynamic linking for LGPL deps (FluidSynth/MUNT) | 3 | Should | B | Missing |
| REQ-OPS-028 | Operations | Optional | Opt-in crash reporting (Breakpad/Sentry) | 4 | Should | A | **Done** |
| REQ-OPS-029 | Operations | Ubiquitous | Crash breadcrumb ring buffer log | 4 | Should | A | **Done** |
| **GPL v2 Process Isolation** | | | | | | | |
| REQ-ISO-001 | Isolation | Ubiquitous | GPL v2 license file (COPYING + LICENSE) | 0 | Must | A | **Done** |
| REQ-ISO-002 | Isolation | Ubiquitous | NOTICE file with copyright attribution | 0 | Must | A | **Done** |
| REQ-ISO-003 | Isolation | Ubiquitous | MIT-licensed IPC protocol specification | 0 | Must | A | Missing |
| REQ-ISO-004 | Isolation | Ubiquitous | IPC message serialization library | 0 | Must | A | Missing |
| REQ-ISO-005 | Isolation | Ubiquitous | Engine host executable | 0 | Must | A | Missing |
| REQ-ISO-006 | Isolation | Ubiquitous | Engine host GPL v2 compliance | 0 | Must | A | Missing |
| REQ-ISO-007 | Isolation | Event-driven | Shared memory framebuffer (double-buffered) | 1 | Must | A | Missing |
| REQ-ISO-008 | Isolation | State-driven | Shared memory audio ring buffer (lock-free) | 1 | Must | A | Missing |
| REQ-ISO-009 | Isolation | Ubiquitous | Control channel protocol (named pipe) | 1 | Must | A | Missing |
| REQ-ISO-010 | Isolation | Ubiquitous | Application shell proxy library | 1 | Must | A | Missing |
| REQ-ISO-011 | Isolation | Ubiquitous | Compile-time backend switch (LEGENDS_USE_IPC) | 1 | Must | A | Missing |
| REQ-ISO-012 | Isolation | Event-driven | Engine process spawning and monitoring | 1 | Must | A | Missing |
| REQ-ISO-013 | Isolation | Unwanted | Engine crash detection and recovery | 2 | Should | A | Missing |
| REQ-ISO-014 | Isolation | Ubiquitous | IPC performance budget compliance (<5%) | 2 | Must | A | Missing |
| REQ-ISO-015 | Isolation | Ubiquitous | Cross-platform IPC implementation | 1 | Must | A | Missing |
| REQ-ISO-016 | Isolation | Event-driven | GPL object code isolation verification | 1 | Must | A | Missing |
| **Wasm Sandbox** | | | | | | | |
| REQ-WASM-001 | Wasm | Ubiquitous | Wasmtime primary runtime | 3 | Must | A | Missing |
| REQ-WASM-002 | Wasm | Ubiquitous | WASI Preview 2 target ABI | 3 | Must | A | Missing |
| REQ-WASM-003 | Wasm | Optional | WASI Preview 1 fallback build | 3 | Should | A | Missing |
| REQ-WASM-004 | Wasm | Ubiquitous | Wasm tool version pinning | 3 | Must | A | Missing |
| REQ-WASM-005 | Wasm | Ubiquitous | Reproducible Wasm build path | 3 | Must | A | Missing |
| REQ-WASM-006 | Wasm | Ubiquitous | Host prerequisite documentation | 3 | Must | A | Missing |
| REQ-WASM-007 | Wasm | Ubiquitous | WIT core emulator package | 3 | Must | A | Missing |
| REQ-WASM-008 | Wasm | Ubiquitous | WIT lifecycle operations | 3 | Must | A | Missing |
| REQ-WASM-009 | Wasm | Ubiquitous | WIT stepping operations | 3 | Must | A | Missing |
| REQ-WASM-010 | Wasm | Ubiquitous | WIT capture operations | 3 | Must | A | Missing |
| REQ-WASM-011 | Wasm | Ubiquitous | WIT input operations | 3 | Must | A | Missing |
| REQ-WASM-012 | Wasm | Ubiquitous | WIT state operations | 3 | Must | A | Missing |
| REQ-WASM-013 | Wasm | Ubiquitous | WIT error type mapping | 3 | Must | A | Missing |
| REQ-WASM-014 | Wasm | Ubiquitous | WIT variable-size output transport | 3 | Must | A | Missing |
| REQ-WASM-015 | Wasm | Ubiquitous | Default-deny capability policy | 3 | Must | A | Missing |
| REQ-WASM-016 | Wasm | Ubiquitous | Network access disabled by default | 3 | Must | A | Missing |
| REQ-WASM-017 | Wasm | Ubiquitous | Environment variable allowlisting | 3 | Should | A | Missing |
| REQ-WASM-018 | Wasm | Ubiquitous | Preopened directory filesystem access | 3 | Must | A | Missing |
| REQ-WASM-019 | Wasm | Ubiquitous | Platform directory mapping | 3 | Must | A | Missing |
| REQ-WASM-020 | Wasm | Optional | Per-directory read/write mode | 3 | Should | A | Missing |
| REQ-WASM-021 | Wasm | Unwanted | Path traversal and symlink blocking | 4 | Must | A | Missing |
| REQ-WASM-022 | Wasm | State-driven | Explicit clock usage | 3 | Must | A | Missing |
| REQ-WASM-023 | Wasm | Ubiquitous | Host-authoritative run loop | 3 | Must | A | Missing |
| REQ-WASM-024 | Wasm | Ubiquitous | Serialized API calls | 3 | Must | A | Missing |
| REQ-WASM-025 | Wasm | Ubiquitous | Single-instance constraint in Wasm | 3 | Must | A | Missing |
| REQ-WASM-026 | Wasm | Ubiquitous | Deterministic state hash reproducibility | 3 | Must | A | Missing |
| REQ-WASM-027 | Wasm | Unwanted | Guest trap structured error surfacing | 3 | Must | A | Missing |
| REQ-WASM-028 | Wasm | Ubiquitous | Per-instance memory limits | 4 | Must | A | Missing |
| REQ-WASM-029 | Wasm | Ubiquitous | Execution budget controls | 4 | Must | A | Missing |
| REQ-WASM-030 | Wasm | Ubiquitous | Bounded queue and buffer enforcement | 4 | Must | A | Missing |
| REQ-WASM-031 | Wasm | Event-driven | Limit exhaustion behavior | 4 | Must | A | Missing |
| REQ-WASM-032 | Wasm | Event-driven | Wasm artifact integrity verification | 4 | Must | A | Missing |
| REQ-WASM-033 | Wasm | Ubiquitous | SBOM for Wasm deliverables | 4 | Should | A | Missing |
| REQ-WASM-034 | Wasm | Ubiquitous | Unsafe host import prohibition | 4 | Must | A | Missing |
| REQ-WASM-035 | Wasm | Unwanted | AI feature network capability isolation | 4 | Must | A | Missing |
| REQ-WASM-036 | Wasm | Ubiquitous | Structured runtime logging | 4 | Should | A | Missing |
| REQ-WASM-037 | Wasm | Ubiquitous | Per-run metrics | 4 | Should | A | Missing |
| REQ-WASM-038 | Wasm | Ubiquitous | Determinism verification reports | 4 | Must | A | Missing |
| REQ-WASM-039 | Wasm | Ubiquitous | Wasm CI build pipeline | 3 | Must | A | Missing |
| REQ-WASM-040 | Wasm | Ubiquitous | Native/Wasm functional parity checks | 4 | Must | A | Missing |
| REQ-WASM-041 | Wasm | Ubiquitous | Determinism replay in Wasmtime | 4 | Must | A | Missing |
| REQ-WASM-042 | Wasm | Ubiquitous | Sandbox policy denial tests | 4 | Must | A | Missing |
| REQ-WASM-043 | Wasm | Event-driven | WIT interface version guard | 4 | Must | A | Missing |
| REQ-WASM-044 | Wasm | Ubiquitous | Wasm distribution artifacts | 4 | Must | A | Missing |
| REQ-WASM-045 | Wasm | Ubiquitous | Dual version tracking | 4 | Must | A | Missing |
| REQ-WASM-046 | Wasm | Ubiquitous | Wasmtime compatibility range documentation | 4 | Should | A | Missing |
| REQ-WASM-047 | Wasm | Ubiquitous | Phase 1 MVP headless runner | 3 | Must | A | Missing |
| REQ-WASM-048 | Wasm | Ubiquitous | Phase 2 capability hardening gate | 4 | Must | A | Missing |
| REQ-WASM-049 | Wasm | Optional | Phase 3 advanced Wasm features | 4 | Could | B | Missing |
| REQ-WASM-050 | Wasm | Ubiquitous | GUI scope exclusion | 3 | Must | A | Missing |
| **Quality Engineering** | | | | | | | |
| REQ-QA-001 | Quality | Event-driven | Suspend/resume handling (elapsed time cap) | 1 | Must | A | **Done** |
| REQ-QA-002 | Quality | Event-driven | Display hotplug resilience | 2 | Should | A | **Done** |
| REQ-QA-003 | Quality | Event-driven | Audio device change mid-session | 2 | Should | A | **Done** |
| REQ-QA-005 | Quality | Event-driven | Step error handling in run loop | 1 | Must | A | **Done** |
| REQ-QA-006 | Quality | Event-driven | Dimension change debouncing (3-frame) | 1 | Must | A | **Done** |
| REQ-QA-007 | Quality | Ubiquitous | Framebuffer buffer overrun protection | -1 | Must | A | **Done** |
| REQ-QA-008 | Quality | Ubiquitous | Pairwise configuration testing (~30-60 configs) | 4 | Must | A | **Done** |
| REQ-QA-009 | Quality | Ubiquitous | Invalid configuration rejection + warning | 1 | Must | A | **Done** |
| REQ-QA-011 | Quality | Event-driven | Cross-config save loading (fingerprint check) | 2 | Must | A | **Done** |
| REQ-QA-012 | Quality | Ubiquitous | Atomic save writes (tmp + rename) | 2 | Must | A | **Done** |
| REQ-QA-015 | Quality | Ubiquitous | Windows high-DPI manifest | 1 | Must | A | **Done** |
| REQ-QA-016 | Quality | Ubiquitous | macOS Retina rendering correctness | 1 | Should | A | Missing |
| REQ-QA-017 | Quality | Ubiquitous | Wayland CI test coverage | 4 | Should | A | Missing |
| REQ-QA-018 | Quality | Unwanted | Audio backend failure graceful degradation | 1 | Must | A | **Done** |
| REQ-QA-019 | Quality | Ubiquitous | Visual regression with SSIM + text grid compare | 4 | Must | A | **Done** |
| REQ-QA-020 | Quality | Ubiquitous | Visual diff artifacts in CI on failure | 4 | Should | A | **Done** |
| REQ-QA-021 | Quality | Ubiquitous | Widened frame timing tolerance for CI (±250 ms) | 4 | Must | A | **Done** |
| REQ-QA-024 | Quality | Ubiquitous | Thread safety contract + TSan CI build | 1 | Must | A | **Done** |
| REQ-QA-025 | Quality | Unwanted | Graceful startup degradation per subsystem | 1 | Must | A | **Done** |
| **User Experience** | | | | | | | |
| REQ-UX-001 | UX | Event-driven | First-run wizard (profile + dirs + import) | 2 | Should | A | Missing |
| REQ-UX-002 | UX | Event-driven | Drag-and-drop program launch | 2 | Should | A | Missing |
| REQ-UX-003 | UX | Ubiquitous | Configurable host key modifier (Right-Ctrl) | 2 | Should | A | **Done** |
| REQ-UX-004 | UX | Event-driven | In-app command palette (Ctrl+Shift+P) | 3 | Could | B | Missing |
| REQ-UX-005 | UX | Optional | Performance overlay (FPS, cycles, buffer) | 2 | Should | A | **Done** |
| REQ-UX-006 | UX | Ubiquitous | GUI settings dialog | 3 | Should | B | Missing |
| REQ-UX-008 | UX | Ubiquitous | DPI-aware UI scaling (100/150/200%) | 2 | Must | A | **Done** |
| REQ-UX-009 | UX | Ubiquitous | Keyboard-only menu/dialog navigation | 2 | Should | A | **Done** |
| REQ-UX-010 | UX | Event-driven | Autosave on crash + recovery offer | 4 | Should | A | **Done** |
| REQ-UX-011 | UX | Event-driven | Hung guest detection (5s notification) | 3 | Could | B | Missing |

### 16.3 Priority Legend (MoSCoW)

| Priority | Meaning |
|----------|---------|
| **Must** | Required for the phase to be considered complete |
| **Should** | Expected but can be deferred to the next phase |
| **Could** | Desirable, included if time permits |

### 16.4 Status Legend

| Status | Meaning |
|--------|---------|
| **Done** | Fully implemented and tested |
| Partial | Implementation exists but incomplete (e.g., backend works, UI missing) |
| Stub | Config/UI scaffolding exists but engine wiring is TODO |
| Missing | Not yet implemented |

---

## 17. Risk Register

| ID | Risk | Likelihood | Impact | Mitigation |
|----|------|-----------|--------|------------|
| RISK-001 | **SDL3 menu API unavailable on Linux** — SDL3 may not support native menus on X11/Wayland | High | Medium | REQ-MENU-002 (fallback overlay) is a Must requirement. Design the `MenuSystem` interface so native and overlay implementations are interchangeable. Both route through `ActionBus`. |
| RISK-002 | **Engine audio buffer format mismatch** — The engine may produce audio at different sample rates or formats than the PAL sink expects | Medium | High | REQ-PLUMB-004 defines format negotiation. If engine produces non-44100 Hz or mono, the Legends bridge resamples before exposing to app shell. |
| RISK-003 | **Scancode translation table gaps** — Some obscure key combinations or international keyboards may not have correct AT Set 1 mappings | Medium | Medium | Start with a complete US layout table (REQ-MAPPER-003). Use the key mapper (REQ-MAPPER-001) as the escape hatch. Log unmapped scancodes for iterative improvement. |
| RISK-004 | **RGB24→surface format conversion overhead** — `legends_capture_rgb()` outputs RGB24, but the SDL3 surface may be BGRA8888 or RGBA8888, requiring per-pixel conversion | Medium | Medium | Detect the surface's `PixelFormat` from `SoftwareContext::format` and use an optimized conversion path (SIMD or SDL conversion functions). Consider requesting RGBA8888 from the context to minimize conversion. |
| RISK-005 | **Single-instance constraint complicates testing** — `legends_create()` enforces one instance per process, making parallel test execution impossible | Low | Medium | Use `legends_force_destroy()` in test teardown. Run integration tests sequentially. Structure unit tests to mock the C ABI boundary. |
| RISK-006 | **Frame pacing jitter** — `IHostClock::sleepUs()` may oversleep on some platforms (especially Windows, where timer resolution is ~15 ms by default) | High | Medium | Use `timeBeginPeriod(1)` on Windows to improve timer resolution. REQ-THROTTLE-001 specifies spin-wait hybrid. Track and log frame timing statistics. |
| RISK-007 | **macOS Gatekeeper rejection** — Unsigned or incorrectly signed binaries trigger Gatekeeper warnings | Medium | High | Set up Apple Developer ID signing in CI early (REQ-BUILD-005). For development builds, provide instructions for `xattr -cr` workaround. |
| RISK-008 | **AI API latency blocks run loop** — Synchronous HTTP requests to the AI backend would freeze the emulator | Low | High | REQ-AI-001 mandates asynchronous queries on a worker thread. AI panel displays a spinner while waiting. Never block the main run loop on network I/O. |
| RISK-009 | **DOSBox-X engine not producing audio in library mode** — The engine's audio subsystem is currently disabled (`sound_enabled = false`) | High | High | REQ-PLUMB-003 explicitly addresses this. The engine library must set `sound_enabled = true` for interactive mode. Investigate `AIBOX_HEADLESS` compile flag. Test audio output as first Phase -1 deliverable. |
| RISK-010 | **Save state size exceeds expectations** — Full machine state with VGA framebuffer may be several megabytes | Low | Low | Use the two-call pattern already defined in the API to query size first. Consider optional compression (zstd) for save files on disk. |
| RISK-011 | **Framebuffer not wired to real engine VRAM** — Current `legends_capture_rgb()` returns synthetic test pattern, not actual DOS display output | High | Critical | REQ-PLUMB-001 and REQ-PLUMB-002 are Phase -1 Must requirements. Gate G1 blocks Phase 1 acceptance. Golden snapshot tests verify byte-level correctness. |
| RISK-012 | **Context recreate storms on rapid mode switches** — Some DOS programs switch video modes frequently, causing expensive destroy/recreate cycles for `IContext` | Medium | Medium | Cache last-known dimensions in `Application` and only recreate when width/height actually change (REQ-VIDEO-002 implementation note). Consider debounce if needed. |
| RISK-013 | **3dfx/Glide translation accuracy across GPU vendors** — Floating-point differences between AMD/NVIDIA/Intel OpenGL drivers may produce visually different output from the same Glide calls | Medium | Medium | REQ-TEST-012 validates via SSIM > 99%. Use headless FBO rendering for deterministic comparison. Accept minor per-driver variance. |
| RISK-014 | **FluidSynth/MUNT library licensing and bundling** — FluidSynth (LGPL) and MUNT (GPL/LGPL) have license implications for static linking and distribution | Medium | High | Link FluidSynth and MUNT dynamically. Ship as optional runtime dependencies on Linux. Bundle on Windows/macOS where dynamic loading is standard. Clearly document license compliance in NOTICE file. |
| RISK-015 | **IPX network security exposure** — Bridging emulated IPX packets over real UDP opens a network attack surface (malformed packets, amplification) | Medium | High | Bind IPX listener to localhost by default. Require explicit `ipx.listen_address` config for remote play. REQ-TEST-010 fuzz tests malformed packets. Rate-limit incoming packet processing. |
| RISK-016 | **Video encoding performance impact** — Real-time AVI/ZMBV encoding during capture may cause frame drops or audio desync | Medium | Medium | Use ZMBV (fast lossless delta encoding, minimal CPU overhead). Encode on a background thread with frame queue. If queue exceeds threshold, drop frames and log warning rather than blocking the run loop. |
| RISK-017 | **Save state forward-compatibility breakage** — Engine state format changes across versions may silently corrupt loaded states rather than failing cleanly | Low | High | REQ-TEST-011 maintains versioned save file archive. The save format's magic + version fields (already in `SaveStateHeader`) must be checked. Any format change increments the version and old saves fail with `LEGENDS_ERR_VERSION_MISMATCH`. |
| RISK-018 | **Host filesystem compromise via mount** — REQ-MOUNT-001 creates a direct bridge from guest x86 code to host filesystem with no containment | High | Critical | REQ-SEC-023 (canonical path resolution), REQ-SEC-024 (read-only mount), REQ-SEC-025 (sensitive dir warning). Symlink/junction traversal must be blocked. |
| RISK-019 | **GPL v2 licensing implications** — DOSBox-X engine (`aibox_core`) is GPL v2. Statically linking makes the entire binary subject to GPL v2 | High | Critical | Mitigated by Section 14 (GPL v2 Process Isolation): the engine runs in a separate `legends_engine_host` process communicating via MIT-licensed IPC (REQ-ISO-001 through REQ-ISO-016). See `docs/design/GPL2_PROCESS_ISOLATION_DESIGN.md` (TDD-LIC-001). Residual risk tracked as RISK-028. REQ-OPS-023 requires formal legal analysis before public release. |
| RISK-020 | **AI panel thread safety data race** — AI worker thread calling `legends_capture_text()` while main loop calls `legends_step_ms()` is a data race | High | High | REQ-QA-024 requires explicit threading contract. If API is not thread-safe, AI panel must queue captures to main thread. TSan build in CI. |
| RISK-021 | **Windows SmartScreen blocking** — Unsigned Windows executables trigger SmartScreen warnings that block most users | High | High | REQ-OPS-008 / REQ-SEC-035 require Authenticode code signing. EV certificate eliminates warnings immediately. Budget ~$300-600/year. |
| RISK-022 | **Suspend/resume run loop corruption** — Laptop lid close causes massive elapsed-time spike, leading to huge step attempt or integer overflow in throttle | High | Medium | REQ-QA-001 caps per-frame elapsed time at 100 ms. Audio stabilizes within 500 ms. |
| RISK-023 | **Missing audio capture API blocks embedders** — `legends_embed.h` has zero audio functions; embedders cannot get sound | High | High | REQ-API-002 adds `legends_capture_audio()` with same two-call pattern as video. Must ship in Phase -1. |
| RISK-024 | **CI time explosion without tiering** — Running all tests on every PR is prohibitively expensive; running only nightly misses regressions | Medium | High | REQ-OPS-004 defines 4 tiers (per-PR/merge/nightly/release). REQ-OPS-005 adds build caching for <15 min per-PR target. |
| RISK-025 | **Save file corruption from power loss** — Writing directly to `slot_N.sav` can corrupt data if process killed mid-write | Medium | High | REQ-QA-012 requires atomic writes (tmp file + fsync + rename). Standard practice, cheap to implement. |
| RISK-026 | **IPC overhead exceeds performance budget** — Named pipe + shared memory synchronization may add > 5% per-frame latency, violating REQ-ISO-014 | Medium | High | Nightly benchmarks compare monolithic vs IPC mode. Shared memory framebuffer (REQ-ISO-007) avoids pipe for bulk data. If budget exceeded, switch control channel to Unix domain sockets or reduce message frequency. |
| RISK-027 | **Shared memory leak on abnormal termination** — If engine host crashes, shared memory segments and named pipes may persist as orphaned OS resources | Medium | Medium | Application shell registers cleanup handler (`atexit`, signal handler). Named pipes use `O_CLOEXEC`/`FILE_FLAG_FIRST_PIPE_INSTANCE`. Shared memory names include PID for unique identification and stale detection. |
| RISK-028 | **GPL "derivative work" challenge despite process isolation** — A legal challenge could argue that the IPC protocol creates a derivative work relationship even with process separation | Medium | Critical | MIT-licensed IPC protocol (REQ-ISO-003) uses a documented, generic wire format. No GPL headers are included by the shell. Legal precedent (FSF FAQ, LGPLv2 preamble) supports process-boundary separation. Formal legal review required before public release per REQ-OPS-023. |
| RISK-029 | **Wasm execution performance significantly slower than native headless** — Wasm overhead (bounds checking, indirect calls, no SIMD in WASI P2) may make emulation too slow for real-time use cases | High | High | Benchmark Wasm vs native headless early in Phase 3 (REQ-WASM-040). Set performance acceptance thresholds (e.g., >50% of native IPS). Optimize hot paths with `wasm-opt`. Consider Wasmtime's Cranelift tier-2 optimizations. Accept headless-only (no frame pacing requirement) reduces the bar. |
| RISK-030 | **WASI Preview 2 specification instability during transition** — WASI Preview 2 and the Component Model are evolving; breaking changes may require rework | Medium | High | Pin Wasmtime and wasm-tools versions (REQ-WASM-004). Keep WASI Preview 1 fallback (REQ-WASM-003). Monitor WASI subgroup proposals. Budget one migration cycle per year. |
| RISK-031 | **Wasm memory limit insufficient for complex DOS programs** — Default 256 MB linear memory may be insufficient for programs requiring large conventional + extended memory configurations | Medium | Medium | Make memory limit configurable (REQ-WASM-028). Test with representative DOS programs from compatibility corpus. Document minimum memory requirements per program class. Wasmtime supports up to 4 GB linear memory if needed. |
| RISK-032 | **WIT interface compatibility breaks between Wasmtime releases** — Component Model binary format or WIT semantics may change across Wasmtime versions | Medium | High | Pin Wasmtime version (REQ-WASM-004). Document supported Wasmtime range (REQ-WASM-046). CI tests against range boundaries (REQ-WASM-043). Version the WIT package independently (REQ-WASM-045) so consumers can detect incompatibility. |

---

## 18. Verification Matrix

This matrix maps each requirement to its verification method and expected
test artifact. New entries from Sections 9-13 are appended at the end.

| Requirement | Method | Test / Artifact | Automated |
|-------------|--------|-----------------|-----------|
| REQ-PLUMB-001 | Test | Golden snapshot: DOS prompt capture matches reference PNG | Yes (integration) |
| REQ-PLUMB-002 | Test | Golden snapshot: text-mode glyphs match VGA font reference | Yes (integration) |
| REQ-PLUMB-003 | Test | Spectral test: PC speaker 1000 Hz tone within ±5% | Yes (integration) |
| REQ-PLUMB-004 | Test | Audio flows end-to-end: engine → bridge → sink, `getQueuedFrames() > 0` | Yes (integration) |
| REQ-PLUMB-005 | Test | Mock-counted present calls: exactly 1 per unlock cycle | Yes (unit) |
| REQ-BUILD-001 | Build | `cmake -DPAL_BACKEND_SDL3=ON && cmake --build .` succeeds | Yes (CI) |
| REQ-BUILD-002 | Test | Binary opens window titled "Project Legends", exits on close (exit code 0) | Yes (CI + headless) |
| REQ-BUILD-003 | Build | CI green on Windows, Linux, macOS | Yes (CI) |
| REQ-BUILD-004 | Test | `Application::init()` + `Application::run()` compile and run | Yes (CI) |
| REQ-BUILD-005 | Build | `cmake --build . --target package` produces artifact; CI publishes on tag | Yes (CI) |
| REQ-CORE-001 | Test | `legends_create()` returns `LEGENDS_OK`, handle non-null; profile presets applied | Yes (unit) |
| REQ-CORE-002 | Test | `legends_step_ms()` returns `LEGENDS_OK`, `cycles_executed > 0` | Yes (unit) |
| REQ-CORE-003 | Test | ASAN clean exit, `legends_destroy()` returns `LEGENDS_OK` | Yes (CI + ASAN) |
| REQ-VIDEO-001 | Test | `legends_capture_rgb()` returns real content matching golden snapshot (Gate G1) | Yes (integration) |
| REQ-VIDEO-002 | Test | Mode switch (text→graphics) triggers context recreate, produces valid new dimensions | Yes (integration) |
| REQ-VIDEO-003 | Test | Scripted resize + screenshot capture; verify aspect ratio preserved in output PNG | Yes (integration) |
| REQ-INPUT-001 | Test | Inject "DIR\n" via scancodes, verify text output contains "DIR" | Yes (integration) |
| REQ-INPUT-002 | Test | Inject mouse event, verify cursor position changes in captured text | Yes (integration) |
| REQ-INPUT-003 | Test | Scripted: send click → verify capture, send Ctrl+F10 → verify release | Yes (integration) |
| REQ-AUDIO-001 | Test | `audio_sink_->pushSamples()` returns `Success`; `getQueuedFrames() > 0` after sound program | Yes (integration) |
| REQ-AUDIO-002 | Test | `setVolume(0.0)` → verify silence in captured buffer; `setVolume(1.0)` → verify signal | Yes (unit) |
| REQ-THROTTLE-001 | Test | Measure host time for 60 frames; expect ~1000 ms ± 100 ms; p95 frame variance < 3 ms | Yes (integration) |
| REQ-CONFIG-001 | Test | Parse sample `.conf` file, verify `legends_config_t` fields | Yes (unit) |
| REQ-CONFIG-002 | Test | Place `dosbox-x.conf` in cwd, verify it is loaded | Yes (integration) |
| REQ-CLI-001 | Test | `--version` exits 0, `--help` exits 0, `--conf` loads file, `--profile` selects preset | Yes (unit) |
| REQ-MENU-001 | Test | Scripted: open menu → verify action dispatched via ActionBus mock | Yes (unit + integration) |
| REQ-MENU-002 | Test | Scripted: F12 → verify overlay rendered → Escape → verify dismissed | Yes (integration) |
| REQ-MENU-003 | Test | Open menu, verify `legends_get_emu_time()` does not advance | Yes (integration) |
| REQ-SAVE-001 | Test | Save to slot, verify file exists, verify size matches | Yes (integration) |
| REQ-SAVE-002 | Test | Save → modify state → load → verify state matches original | Yes (integration) |
| REQ-SAVE-003 | Test | Scripted: open save dialog → verify 9 slots listed → verify thumbnails for occupied | Yes (integration) |
| REQ-SAVE-004 | Test | Verify save path matches platform convention per Appendix D | Yes (unit) |
| REQ-MAPPER-001 | Test | Scripted: open mapper → remap key → verify new scancode injected | Yes (integration) |
| REQ-MAPPER-002 | Test | Save mapper, reload, verify mappings preserved | Yes (unit) |
| REQ-MAPPER-003 | Test | Verify all 104 keys in default table produce correct scancodes | Yes (unit) |
| REQ-CAPTURE-001 | Test | Trigger capture, verify PNG file exists with correct dimensions | Yes (integration) |
| REQ-CAPTURE-002 | Test | Verify capture path matches platform convention per Appendix D | Yes (unit) |
| REQ-PAUSE-001 | Test | Pause, step time unchanged; resume, time advances | Yes (integration) |
| REQ-RESET-001 | Test | Reset, verify boot sequence occurs (text capture shows prompt) | Yes (integration) |
| REQ-MOUNT-001 | Test | Mount host directory, `DIR` lists host files, file read returns correct content | Yes (integration) |
| REQ-MOUNT-002 | Test | Mount `.iso`, `DIR` lists ISO contents; mount `.img`, verify FAT access | Yes (integration) |
| REQ-INPUT-004 | Test | Set clipboard text, trigger paste, verify text appears in captured DOS output | Yes (integration) |
| REQ-CAPTURE-003 | Test | Start capture, run 5 seconds, stop; verify file exists, playable, audio synced ±50 ms | Yes (integration) |
| REQ-SHADER-001 | Test | Enable CRT shader, capture screenshot, verify pixel differences from unshaded | Yes (integration) |
| REQ-SHADER-002 | Test | Switch between presets, verify each produces distinct output | Yes (integration) |
| REQ-AI-001 | Test | Open AI panel with mock backend, send query, verify response rendered (non-blocking) | Yes (unit + mock) |
| REQ-AI-002 | Test | Query with screen context, verify text capture included in request payload | Yes (unit + mock) |
| REQ-AI-003 | Test | Parse AI config section from `.conf`, verify fields; `enabled=false` → panel shows setup | Yes (unit) |
| REQ-PRINT-001 | Test | `PRINT` from DOS, verify text file appears in capture dir | Yes (integration) |
| REQ-MIDI-001 | Test | MIDI output event log: verify note-on/note-off sequence | Yes (integration + mock) |
| REQ-TTF-001 | Test | Enable TTF mode, golden snapshot compare against reference | Yes (integration) |
| REQ-FULLSCREEN-001 | Test | Scripted: Alt+Enter → verify fullscreen state → Alt+Enter → verify windowed | Yes (integration) |
| REQ-JOYSTICK-001 | Test | Inject synthetic joystick events, verify DOS game input registers | Yes (integration + mock) |
| REQ-NET-001 | Test | Two headless instances establish IPX connection, exchange packets | Yes (integration) |
| REQ-HW-001 | Test | Glide test program renders to FBO, SSIM > 99% against golden reference | Yes (integration) |
| REQ-HW-002 | Test | PC-98 test program boots, text VRAM displays correct Japanese characters | Yes (integration) |
| REQ-AUDIO-003 | Test | FluidSynth: known MIDI sequence → PCM spectral match; MUNT: MT-32 ROM loads, plays | Yes (integration) |
| REQ-TEST-001 | CI | `ctest` passes, coverage report >80% | Yes (CI) |
| REQ-TEST-002 | CI | Boot-to-prompt integration test passes | Yes (CI) |
| REQ-TEST-003 | CI | Determinism hash match test passes | Yes (CI) |
| REQ-TEST-004 | CI | Golden visual snapshot tests pass (<1% pixel diff) | Yes (CI) |
| REQ-TEST-005 | CI | Audio spectral + buffer tests pass | Yes (CI) |
| REQ-TEST-006 | CI | Replay determinism test passes | Yes (CI) |
| REQ-TEST-007 | CI | Scripted UI smoke test passes on all platforms | Yes (CI) |
| REQ-TEST-008 | CI | 12hr soak: RSS within 5% of baseline, `getDroppedFrames() == 0` | Yes (CI, nightly) |
| REQ-TEST-009 | CI | Benchmark IPS within 5% of `main` branch baseline | Yes (CI) |
| REQ-TEST-010 | CI | Fuzz targets run 10 min without crash (libFuzzer or equivalent) | Yes (CI) |
| REQ-TEST-011 | CI | Archived `.sav` files load or fail gracefully (no crash) | Yes (CI) |
| REQ-TEST-012 | CI | Shader/3dfx FBO render: SSIM > 99% against golden reference | Yes (CI) |
| REQ-PACKAGE-001 | CI | Windows installer artifact produced, installs on clean VM (Gate G4) | Yes (CI) |
| REQ-PACKAGE-002 | CI | AppImage artifact produced, runs on Ubuntu 22.04 (Gate G4) | Yes (CI) |
| REQ-PACKAGE-003 | CI | macOS .app bundle artifact produced (Gate G4) | Yes (CI) |
| REQ-PACKAGE-004 | Test | Create `portable.txt`, verify local data storage | Yes (integration) |
| REQ-LOG-001 | Test | Run with `--log`, verify log file created in XDG state dir with entries | Yes (integration) |
| REQ-ERROR-001 | Test | Load corrupted save, verify error message displayed (not crash) | Yes (integration) |
| **Security** | | | |
| REQ-SEC-023 | Test | Mount dir with symlinks pointing outside root, verify access denied | Yes (integration) |
| REQ-SEC-024 | Test | Mount with readonly, attempt guest write, verify DOS "Access denied" | Yes (integration) |
| REQ-SEC-010 | Test | Load save with corrupted CRC, verify `LEGENDS_ERR_INVALID_STATE` | Yes (unit) |
| REQ-SEC-011 | Test | Attempt to load 300 MB save file, verify rejection before read | Yes (unit) |
| REQ-SEC-013 | Test | Launch from dir with `.conf`, verify warning displayed | Yes (integration) |
| REQ-SEC-016 | Test | Mount crafted `.img` with FAT cycle, verify no infinite loop | Yes (fuzz) |
| REQ-SEC-027 | Build | Verify `DEPENDENCIES.md` or manifest lists pinned versions | Yes (CI) |
| REQ-SEC-031 | Review | Threat model document exists and covers 4 trust boundaries | Manual (review) |
| REQ-SEC-035 | Build | Windows binary has valid Authenticode signature; macOS notarized | Yes (CI) |
| REQ-SEC-005 | Test | AI call with invalid TLS cert fails with clear error | Yes (unit + mock) |
| REQ-SEC-006 | Test | Config with raw `api_key=sk-...` produces warning, rejected | Yes (unit) |
| REQ-SEC-018 | Test | AI request with screen context uses structured separation format | Yes (unit + mock) |
| **Embedding API** | | | |
| REQ-API-002 | Test | `legends_capture_audio()` returns S16LE samples after step | Yes (integration) |
| REQ-API-004 | Test | `legends_mount_drive('C', path, 0)` → `DIR` lists host files | Yes (integration) |
| REQ-API-009 | Review | `legends_embed.h` documents threading contract for capture calls | Manual (review) |
| REQ-API-013 | Build | `legends_step_result_t` has `_reserved` fields, compiles clean | Yes (build) |
| REQ-API-014 | Build | `LEGENDS_API` macro defined, functions annotated | Yes (build) |
| REQ-API-011 | Test | `legends_has_capability(CAP_AUDIO_CAPTURE, &out)` returns 1 | Yes (unit) |
| **Operational Infrastructure** | | | |
| REQ-OPS-001 | Build | SDL3 pinned to specific tag/SHA in build config | Yes (CI) |
| REQ-OPS-004 | CI | 4-tier pipeline config exists with documented trigger rules | Yes (CI) |
| REQ-OPS-008 | Build | Windows artifact signed (verify via `signtool verify`) | Yes (CI) |
| REQ-OPS-019 | Process | Release branch exists for each shipped version | Manual (review) |
| REQ-OPS-020 | Build | `--version` output matches semver from `git describe` | Yes (integration) |
| REQ-OPS-022 | Build | `LICENSES/` directory present in distribution with NOTICE file | Yes (CI) |
| REQ-OPS-023 | Review | GPL v2 analysis document completed and reviewed by legal | Manual (BLOCKER) |
| REQ-OPS-014 | CI | Per-PR fuzz runs seed corpus without crash; nightly runs 4+ hrs | Yes (CI) |
| REQ-OPS-015 | CI | `test/fuzz/corpus/` directory exists in repo with crash inputs | Yes (CI) |
| **Quality Engineering** | | | |
| REQ-QA-001 | Test | Simulate 30s suspend (advance clock), verify recovery within 3 frames | Yes (integration) |
| REQ-QA-005 | Test | Force step error, verify run loop pauses + error dialog shown | Yes (integration) |
| REQ-QA-006 | Test | Force dimension oscillation, verify context recreated only after 3 stable frames | Yes (integration) |
| REQ-QA-007 | Test | Change resolution between capture calls, verify no overrun (ASAN) | Yes (unit + ASAN) |
| REQ-QA-008 | CI | Pairwise config matrix (~30-60 configs) all boot to prompt without ASAN findings | Yes (CI, nightly) |
| REQ-QA-009 | Test | Configure `machine=hercules + sounddevice=sb16`, verify warning shown | Yes (unit) |
| REQ-QA-011 | Test | Save with VGA/16M, load with EGA/4M, verify warning dialog + no crash | Yes (integration) |
| REQ-QA-012 | Test | Kill process mid-save, verify `.sav` file intact (atomic write) | Yes (integration) |
| REQ-QA-015 | Build | Windows manifest includes DPI awareness declaration | Yes (build) |
| REQ-QA-018 | Test | Launch with `SDL_AUDIODRIVER=dummy`, verify no crash, audio features no-op | Yes (integration) |
| REQ-QA-019 | CI | Golden tests use SSIM; text-mode tests compare cell grids | Yes (CI) |
| REQ-QA-021 | CI | Frame timing tolerance ±250 ms; timing failures are warnings not errors | Yes (CI) |
| REQ-QA-024 | CI | TSan build in CI matrix; AI capture queued to main thread | Yes (CI + TSAN) |
| REQ-QA-025 | Test | Launch with `SDL_VIDEODRIVER=dummy`, verify graceful error + clean exit | Yes (integration) |
| **User Experience** | | | |
| REQ-UX-001 | Test | First launch (no config), verify wizard displayed | Yes (integration) |
| REQ-UX-003 | Test | HostKey+Delete sends reset; bare Ctrl+Alt+Delete sent to guest | Yes (integration) |
| REQ-UX-005 | Test | Enable perf overlay, verify FPS/cycles/buffer values displayed | Yes (integration) |
| REQ-UX-008 | Test | UI elements legible at 100%, 150%, 200% scale (screenshot compare) | Yes (integration) |
| REQ-UX-009 | Test | Navigate overlay menu entirely via keyboard (Tab, arrows, Enter) | Yes (integration) |
| **GPL v2 Process Isolation** | | | |
| REQ-ISO-001 | Build | `COPYING` file present, contains GPL v2 text (338 lines); `LICENSE` lists SPDX identifiers | Yes (CI) |
| REQ-ISO-002 | Build | `NOTICE` file present with copyright holders, per-directory SPDX, dependency table | Yes (CI) |
| REQ-ISO-003 | Review | `include/legends_ipc/` headers contain MIT SPDX comment; no GPL includes in dependency tree | Yes (CI license scan) |
| REQ-ISO-004 | Test | Round-trip serialization tests for all IPC message types; wire format version header present | Yes (unit) |
| REQ-ISO-005 | Test | `legends_engine_host` boots to DOS prompt and responds to IPC lifecycle commands | Yes (integration) |
| REQ-ISO-006 | Build | `legends_engine_host --version` prints GPL v2 notice; source tarball generated in CI | Yes (CI) |
| REQ-ISO-007 | Test | Shared memory double-buffer: frame latency < 1 ms from engine VSync to shell read | Yes (integration) |
| REQ-ISO-008 | Test | Lock-free ring buffer: no underruns at 44100 Hz steady state; overrun drops oldest samples | Yes (unit) |
| REQ-ISO-009 | Test | Named pipe control channel: request/response round-trip for all command types | Yes (integration) |
| REQ-ISO-010 | Test | `legends_proxy` passes existing integration test suite (same results as `legends_core`) | Yes (integration) |
| REQ-ISO-011 | Build | `cmake -DLEGENDS_USE_IPC=OFF` and `cmake -DLEGENDS_USE_IPC=ON` both configure and build | Yes (CI matrix) |
| REQ-ISO-012 | Test | Engine process spawned within 2 s; shell detects child exit via OS notification | Yes (integration) |
| REQ-ISO-013 | Test | Kill engine host mid-run; shell displays error dialog within 1 s and offers restart | Yes (integration) |
| REQ-ISO-014 | Benchmark | Nightly benchmark: IPC overhead < 5% of frame time at 60 FPS (p95 < 0.83 ms) | Yes (nightly) |
| REQ-ISO-015 | Build | CI passes on Windows + Linux + macOS; platform code confined to `src/legends_ipc/platform/` | Yes (CI matrix) |
| REQ-ISO-016 | Build | Linker map scan: zero `aibox_core`/`legends_core` symbols in `project_legends` when IPC=ON | Yes (CI) |
| **Wasm Sandbox** | | | |
| REQ-WASM-001 | Test | Wasmtime host runner instantiates component; smoke test lifecycle passes | Yes (integration) |
| REQ-WASM-002 | Build | `wasm-tools component validate` accepts output `.wasm` artifact | Yes (CI) |
| REQ-WASM-003 | Build | WASI Preview 1 fallback build produces valid core module (when enabled) | Yes (CI) |
| REQ-WASM-004 | Build | Toolchain version manifest present; CI installs pinned versions | Yes (CI) |
| REQ-WASM-005 | Build | Two clean builds from same commit produce byte-identical `.wasm` | Yes (CI) |
| REQ-WASM-006 | Review | Host prerequisite docs exist for Windows, Linux, macOS | Manual (review) |
| REQ-WASM-007 | Build | `wit/` directory exists; WIT package validates with `wasm-tools` | Yes (CI) |
| REQ-WASM-008 | Test | WIT create → reset → destroy round-trip completes without error | Yes (integration) |
| REQ-WASM-009 | Test | `step-ms(100)` returns cycle count > 0; determinism hash matches native | Yes (integration) |
| REQ-WASM-010 | Test | `capture-text` and `capture-rgb` output matches native headless | Yes (integration) |
| REQ-WASM-011 | Test | `text-input("DIR\n")` + step produces matching DOS output | Yes (integration) |
| REQ-WASM-012 | Test | Save → load round-trip produces identical state hash | Yes (integration) |
| REQ-WASM-013 | Test | Each `LEGENDS_ERR_*` code triggers correct WIT error variant | Yes (unit) |
| REQ-WASM-014 | Test | Oversized capture returns error; normal capture returns bounded `list<u8>` | Yes (unit) |
| REQ-WASM-015 | Test | Default policy denies all capabilities; ungrantable op produces trap | Yes (integration) |
| REQ-WASM-016 | Test | Socket operation from guest returns denied error | Yes (integration) |
| REQ-WASM-017 | Test | Unlisted env vars return empty; listed vars return correct values | Yes (integration) |
| REQ-WASM-018 | Test | Access outside preopened directories returns permission error | Yes (integration) |
| REQ-WASM-019 | Test | Guest paths map to correct host platform directories per Appendix D | Yes (integration) |
| REQ-WASM-020 | Test | Write to read-only preopened dir returns permission error | Yes (integration) |
| REQ-WASM-021 | Test | Path traversal (`../../`) and symlink escape blocked on all platforms | Yes (integration) |
| REQ-WASM-022 | Test | Deterministic mode denies wall-clock; identical hashes across runs | Yes (integration) |
| REQ-WASM-023 | Test | Guest never self-advances; only host-called steps produce progress | Yes (integration) |
| REQ-WASM-024 | Test | Concurrent host calls are serialized or return error | Yes (unit) |
| REQ-WASM-025 | Test | Second `create` call returns error in single-instance mode | Yes (unit) |
| REQ-WASM-026 | Test | Same config + input + steps → identical hash in Wasm and native | Yes (CI) |
| REQ-WASM-027 | Test | Guest trap produces structured host error; host process survives | Yes (integration) |
| REQ-WASM-028 | Test | Guest exceeding memory limit traps with OOM error | Yes (integration) |
| REQ-WASM-029 | Test | Fuel/epoch exhaustion produces structured error | Yes (integration) |
| REQ-WASM-030 | Test | Input queue overflow returns error or drops oldest (documented) | Yes (unit) |
| REQ-WASM-031 | Test | Each resource limit exhaustion triggers configured behavior | Yes (integration) |
| REQ-WASM-032 | Test | Checksum mismatch aborts with clear error; valid checksum proceeds | Yes (integration) |
| REQ-WASM-033 | Build | SBOM file (SPDX/CycloneDX) generated for Wasm release artifacts | Yes (CI) |
| REQ-WASM-034 | Build | Wasm component imports only allowed WIT interfaces; CI validates | Yes (CI) |
| REQ-WASM-035 | Test | AI enabled + network denied: emulator component cannot open sockets | Yes (integration) |
| REQ-WASM-036 | Test | Structured log entries include runtime version, capabilities, lifecycle events | Yes (integration) |
| REQ-WASM-037 | Test | Per-run metrics (startup time, step throughput, memory) are collected | Yes (integration) |
| REQ-WASM-038 | Test | Determinism report (JSON) includes config hash, input hash, state hash | Yes (CI) |
| REQ-WASM-039 | Build | CI builds Wasm artifact on Linux + one additional platform | Yes (CI) |
| REQ-WASM-040 | Test | Native and Wasm headless produce identical state hashes for same inputs | Yes (CI) |
| REQ-WASM-041 | Test | Input trace recorded in native, replayed in Wasm — hashes match | Yes (CI) |
| REQ-WASM-042 | Test | Sandbox denial tests: network, filesystem, env var access all denied | Yes (CI) |
| REQ-WASM-043 | Build | WIT change without version bump fails CI | Yes (CI) |
| REQ-WASM-044 | Build | Release package contains `.wasm`, host runner/instructions, `checksums.sha256` | Yes (CI) |
| REQ-WASM-045 | Build | Release notes state project version and WIT interface version | Yes (CI) |
| REQ-WASM-046 | Review | Release notes document min/max tested Wasmtime versions | Manual (review) |
| REQ-WASM-047 | Test | MVP host runner completes full lifecycle; determinism test passes | Yes (integration) |
| REQ-WASM-048 | Test | All sandbox denial + parity + governance tests pass before release | Yes (CI) |
| REQ-WASM-049 | Test | Audio capture via WIT returns valid PCM; replay tooling functional | Yes (integration) |
| REQ-WASM-050 | Build | Wasm build has no GUI/windowing dependencies; WIT has no display ops | Yes (CI) |

---

## 19. Appendices

### Appendix A: Hotkey Reference

> **Note (v3.0.0):** REQ-UX-003 introduces a configurable "host key" modifier
> (default: Right-Ctrl) to disambiguate host vs. guest hotkeys. When implemented,
> hotkeys below prefixed with HostKey replace their current modifier. Example:
> HostKey+Delete replaces Ctrl+Alt+Delete for machine reset, freeing
> Ctrl+Alt+Delete to pass through to the guest.

Default hotkey bindings for the interactive binary:

| Hotkey | Action | Requirement |
|--------|--------|-------------|
| Alt+Enter | Toggle fullscreen | REQ-FULLSCREEN-001 |
| Alt+Pause | Pause/Resume | REQ-PAUSE-001 |
| Ctrl+F1 | Key mapper | REQ-MAPPER-001 |
| Ctrl+F5 | Screenshot | REQ-CAPTURE-001 |
| Ctrl+Shift+F5 | Start/Stop video capture | REQ-CAPTURE-003 |
| Ctrl+Shift+V | Paste from host clipboard | REQ-INPUT-004 |
| Ctrl+Shift+F1..F9 | Save state (slots 1-9) | REQ-SAVE-001 |
| Ctrl+Alt+F1..F9 | Load state (slots 1-9) | REQ-SAVE-002 |
| Ctrl+F10 | Release mouse (primary) | REQ-INPUT-003 |
| Middle mouse button | Release mouse (alternative) | REQ-INPUT-003 |
| Ctrl+F12 | AI assistant panel | REQ-AI-001 |
| Ctrl+Alt+Delete | Machine reset | REQ-RESET-001 |
| F12 | Overlay menu (fallback) | REQ-MENU-002 |

### Appendix B: Data Directory Layout

```
<platform_data_dir>/ProjectLegends/    (see Appendix D for platform_data_dir)
├── saves/
│   ├── slot_1.sav            # Save state data
│   ├── slot_1.png            # Save state thumbnail
│   ├── slot_2.sav
│   ├── slot_2.png
│   └── ...                   # Up to slot_9
├── capture/
│   ├── capture_20260225_143012_001.png
│   └── ...
└── logs/                     (only on Linux; macOS uses ~/Library/Logs)
    └── project_legends.log

<platform_config_dir>/ProjectLegends/  (see Appendix D for platform_config_dir)
├── default.conf              # Default configuration
└── mapper.txt                # Key mapper bindings
```

### Appendix C: Build Commands

```bash
# Phase 0: Minimal build
cmake -B build -DPAL_BACKEND_SDL3=ON -DPAL_DEFAULT_BACKEND=SDL3
cmake --build build --target project_legends

# With all backends (for testing)
cmake -B build -DPAL_BACKEND_SDL3=ON -DPAL_BACKEND_HEADLESS=ON

# Run
./build/project_legends
./build/project_legends --conf my.conf GAME.EXE
./build/project_legends --fullscreen --cycles 20000 --profile interactive

# Test
cd build && ctest --output-on-failure

# Package
cmake --build build --target package
```

### Appendix D: Platform Directory Policy

All file paths follow platform conventions. The `PlatformDirs` module
(`src/app/platform_dirs.h`) resolves these at runtime.

| Purpose | XDG Variable | Linux Default | macOS | Windows |
|---------|-------------|---------------|-------|---------|
| **Config** (settings, mapper) | `$XDG_CONFIG_HOME` | `~/.config/projectlegends/` | `~/Library/Preferences/ProjectLegends/` | `%APPDATA%\ProjectLegends\` |
| **Data** (saves, captures) | `$XDG_DATA_HOME` | `~/.local/share/projectlegends/` | `~/Library/Application Support/ProjectLegends/` | `%APPDATA%\ProjectLegends\` |
| **State** (logs) | `$XDG_STATE_HOME` | `~/.local/state/projectlegends/` | `~/Library/Logs/ProjectLegends/` | `%APPDATA%\ProjectLegends\logs\` |
| **Cache** (shader cache) | `$XDG_CACHE_HOME` | `~/.cache/projectlegends/` | `~/Library/Caches/ProjectLegends/` | `%LOCALAPPDATA%\ProjectLegends\cache\` |

**Portable mode** (`portable.txt` next to executable): All four categories
collapse to `<exe_dir>/` subdirectories (`config/`, `data/`, `logs/`, `cache/`).

### Appendix E: DOSBox-X Parity Scoreboard

Tracks feature parity against DOSBox-X essentials. Updated as features land.

| Feature | DOSBox-X | ProjectLegends | Status | Requirement |
|---------|----------|---------------|--------|-------------|
| Boot to DOS prompt | Yes | Planned | Blocked (G1) | REQ-PLUMB-001 |
| Drive mounting (C:) | Yes | Planned | — | REQ-CORE-001 |
| Keyboard input | Yes | Planned | — | REQ-INPUT-001 |
| Mouse support | Yes | Planned | — | REQ-INPUT-002 |
| PC speaker audio | Yes | Planned | Blocked (G2) | REQ-PLUMB-003 |
| Sound Blaster | Yes | Planned | Blocked (G2) | REQ-AUDIO-001 |
| OPL/AdLib music | Yes | Planned | Blocked (G2) | REQ-AUDIO-001 |
| Input mapper | Yes | Planned | — | REQ-MAPPER-001 |
| Save/load state | Yes | Planned | — | REQ-SAVE-001/002 |
| Screenshot capture | Yes | Planned | — | REQ-CAPTURE-001 |
| Fullscreen toggle | Yes | Planned | — | REQ-FULLSCREEN-001 |
| Menu system | Yes | Planned | — | REQ-MENU-001/002 |
| VGA mode switching | Yes | Planned | — | REQ-VIDEO-002 |
| Config file (.conf) | Yes | Planned | — | REQ-CONFIG-001 |
| Joystick support | Yes | Planned | — | REQ-JOYSTICK-001 |
| Printer output | Yes | Planned | — | REQ-PRINT-001 |
| MIDI output | Yes | Planned | — | REQ-MIDI-001 |
| TTF rendering | Yes | Planned | — | REQ-TTF-001 |
| Host dir mounting | Yes | **Done** | mount_manager.cpp | REQ-MOUNT-001 |
| CD/floppy image mounting | Yes | Planned | — | REQ-MOUNT-002 |
| Clipboard paste | Yes | Planned | — | REQ-INPUT-004 |
| Video recording | Yes | **Done** | video_capture.cpp, zmbv_codec.cpp | REQ-CAPTURE-003 |
| IPX networking | Yes | Planned | — | REQ-NET-001 |
| 3dfx Voodoo/Glide | Yes | Planned | — | REQ-HW-001 |
| NEC PC-98 support | Yes | Planned | — | REQ-HW-002 |
| MT-32 emulation (MUNT) | Yes | Planned | — | REQ-AUDIO-003 |
| FluidSynth/SoundFont | Yes | Planned | — | REQ-AUDIO-003 |
| Windows 9x support | Yes | Future | — | — |
| **AI assistant** | **No** | Planned | — | REQ-AI-001 |
| **Deterministic replay** | **No** | Planned | — | REQ-TEST-006 |
| **Stable C embed API** | **No** | **Done** | Complete | — |

### Appendix F: Compatibility Corpus

Three-tier test corpus for Gate G3 (compatibility pass threshold).

**Tier 1: Command-Line Utilities** (100% pass required)

| Program | Tests |
|---------|-------|
| `DIR` / `VER` / `TYPE` / `COPY` | Basic shell operation |
| `EDIT.COM` | TUI text editor, mouse support |
| `DEBUG.COM` | Memory inspection, CPU instruction test |
| `TREE.COM` | Directory traversal display |

**Tier 2: Mode-Switching Applications** (90% pass required)

| Program | Tests |
|---------|-------|
| Norton Commander | Text mode, mouse, function keys |
| QBasic | Text mode, menus, graphics mode switching |
| `MODE CO80` / `MODE CO40` | Text mode resolution change |
| Mode 13h test program | 320x200 256-color graphics |

**Tier 3: Representative Games** (80% pass required)

| Program | Tests |
|---------|-------|
| Commander Keen (CGA/EGA) | Keyboard input, scrolling, PC speaker |
| DOOM (VGA) | Mouse look, Sound Blaster, complex rendering |
| SimCity (VGA) | Mouse-driven UI, timer-sensitive gameplay |
| Monkey Island (VGA+SB) | Mouse, Sound Blaster, AdLib, palette effects |

**Tier 4: Advanced Hardware Targets** (Release B, informational — no gate threshold)

| Program | Tests |
|---------|-------|
| DOOM (IPX multiplayer) | IPX networking, multi-instance packet exchange |
| Sierra games (MT-32) | MUNT MT-32 audio, correct instrument selection |
| Touhou Project (PC-98) | PC-98 boot, GDC graphics, YM2608 audio |
| Tomb Raider (3dfx/Glide) | Glide → OpenGL translation, textured 3D scenes |
| Windows 95 (IDE+VGA) | Win9x boot, desktop, basic application launch |

---

## Changelog

### v4.1.0 (2026-02-25) — Wasm Sandbox Integration

Integrated the Wasmtime/WASI sandbox requirements (`wasm.md`) into the roadmap,
requirements catalogue, risk register, and verification matrix.

**New section added:**
- **Section 15: Wasm Sandbox** — 50 new EARS requirements (REQ-WASM-001 through
  REQ-WASM-050) across 10 subsections covering runtime and toolchain, WIT
  component interface, sandbox capabilities, execution model, resource
  governance, security, observability, CI and verification, packaging and
  distribution, and rollout plan.

**New risks added:**
- RISK-029: Wasm execution performance significantly slower than native headless (High/High)
- RISK-030: WASI Preview 2 specification instability during transition (Medium/High)
- RISK-031: Wasm memory limit insufficient for complex DOS programs (Medium/Medium)
- RISK-032: WIT interface compatibility breaks between Wasmtime releases (Medium/High)

**Structural changes:**
- Version bumped from 4.0.0 to 4.1.0
- Sections renumbered: 15→16 (Catalogue), 16→17 (Risk Register), 17→18
  (Verification Matrix), 18→19 (Appendices)
- 50 REQ-WASM rows added to Section 16 requirements catalogue
- 50 REQ-WASM verification entries added to Section 18 verification matrix
- CMakeLists.txt updated with `LEGENDS_BUILD_WASM` option and Wasm build support
- ARCHITECTURE.md updated with Wasm Sandbox Architecture section
- README.md updated with Wasm capabilities and project structure entries

**Key architectural decisions:**
- Wasmtime is the primary Wasm runtime; WASI Preview 2 is the target ABI
- WIT package defines stable component interface mirroring `legends_embed.h`
- Default-deny capability policy: no network, no env vars, preopened dirs only
- Host-authoritative run loop: guest never self-advances
- Headless-only scope: GUI excluded from initial Wasm target
- Determinism parity: Wasm and native headless must produce identical state hashes

**Open decisions from `wasm.md`:**
1. Whether to use Component Model only, or dual support with core modules during transition
2. Exact WIT package namespace/versioning policy
3. Performance acceptance thresholds versus native headless baseline
4. Signed artifact policy (required vs optional) for internal builds

**Requirement count:** 50 new REQ-WASM requirements, bringing total from ~156
to ~206 tracked requirements.

### v4.0.0 (2026-02-25) — GPL v2 Process Isolation

Integrated the GPL v2 process isolation design (`docs/design/GPL2_PROCESS_ISOLATION_DESIGN.md`,
TDD-LIC-001) into the roadmap, requirements catalogue, risk register, and
verification matrix.

**New section added:**
- **Section 14: GPL v2 Process Isolation** — 16 new EARS requirements
  (REQ-ISO-001 through REQ-ISO-016) across 10 subsections covering license
  files, IPC protocol, engine host process, shared memory framebuffer and audio,
  control channel, application shell proxy, process lifecycle, performance
  budget, and platform support with GPL isolation verification.

**Updated existing requirements:**
- **REQ-OPS-023** — Added cross-reference to Section 14, acceptance criteria
  referencing process isolation architecture and license files.
- **RISK-019** — Updated mitigation to reference Section 14, REQ-ISO-001 through
  REQ-ISO-016, and the design document. Residual risk tracked as RISK-028.

**New risks added:**
- RISK-026: IPC overhead exceeds performance budget (Medium/High)
- RISK-027: Shared memory leak on abnormal termination (Medium/Medium)
- RISK-028: GPL "derivative work" challenge despite process isolation (Medium/Critical)

**New files at repo root:**
- `COPYING` — Verbatim GNU GPL v2 license text
- `LICENSE` — Multi-component license overview with SPDX identifiers
- `NOTICE` — Copyright attributions and third-party dependency licenses

**Structural changes:**
- Sections renumbered: 14→15 (Catalogue), 15→16 (Risk Register), 16→17
  (Verification Matrix), 17→18 (Appendices)
- 16 REQ-ISO rows added to Section 15 requirements catalogue
- 16 REQ-ISO verification entries added to Section 17 verification matrix
- CMakeLists.txt updated with `LEGENDS_USE_IPC` option, `legends_ipc` library,
  `legends_engine_host` executable, `legends_proxy` library, and conditional linking

**Key architectural decisions:**
- Two-process architecture: GPL engine in `legends_engine_host`, MIT IPC protocol
  in `legends_ipc`, non-GPL application shell linked via `legends_proxy`
- Compile-time backend switch (`LEGENDS_USE_IPC`) preserves monolithic mode
- Shared memory for bulk data (framebuffer, audio), named pipes for control
- Performance budget: < 5% overhead at 60 FPS

**Requirement count:** 16 new REQ-ISO requirements, bringing total from ~140
to ~156 tracked requirements.

### v3.0.0 (2026-02-25) — Multi-Persona Expert Review

Changes incorporated from 5 parallel expert persona reviews: Security Engineer,
Embedded SDK Developer, QA/Test Engineer, DevOps/Release Engineer, and
End-User/DOS Gamer.

**New cross-cutting sections added:**
- **Section 9: Security Hardening** — 22 REQ-SEC requirements covering host
  filesystem isolation, save state integrity, config file security, AI panel
  security, network security, supply chain, and code signing
- **Section 10: Embedding API Completeness** — 11 REQ-API requirements covering
  audio capture API (`legends_capture_audio()`), drive mount API
  (`legends_mount_drive()`), event callbacks, thread safety docs, ABI
  extensibility, DLL export annotations, and multi-instance guidance
- **Section 11: Operational Infrastructure** — 17 REQ-OPS requirements covering
  SDL3 version pinning, hermetic CI builds, tiered CI pipeline, artifact
  management, release branching, semantic versioning, license compliance (GPL v2
  analysis BLOCKER), fuzz infrastructure, crash reporting, and auto-update
- **Section 12: Quality Engineering** — 19 REQ-QA requirements covering
  suspend/resume handling, display hotplug, audio device changes, step error
  handling, dimension debouncing, framebuffer overrun protection, pairwise config
  testing, invalid config rejection, cross-config save loading, atomic save
  writes, DPI awareness, Retina rendering, Wayland testing, audio backend
  resilience, SSIM visual regression, frame timing tolerance, and thread safety
- **Section 13: User Experience & Accessibility** — 11 REQ-UX requirements
  covering first-run wizard, drag-and-drop, host key modifier, command palette,
  performance overlay, settings dialog, DPI-aware scaling, keyboard navigation,
  autosave, and hung guest detection

**Release gate added:**
- **G5: Security baseline** — Threat model documented, all Critical REQ-SEC items
  implemented, no unresolved Critical/High findings

**New risks added:**
- RISK-018: Host filesystem compromise via mount (Critical)
- RISK-019: GPL v2 licensing implications (Critical BLOCKER)
- RISK-020: AI panel thread safety data race (High)
- RISK-021: Windows SmartScreen blocking unsigned executables (High)
- RISK-022: Suspend/resume run loop corruption (Medium)
- RISK-023: Missing audio capture API blocks embedders (High)
- RISK-024: CI time explosion without tiering (High)
- RISK-025: Save file corruption from power loss (High)

**Requirement count:** ~80 new requirements (22 SEC + 11 API + 17 OPS + 19 QA +
11 UX), bringing the total from ~60 to ~140 tracked requirements.

**Key architectural decisions surfaced:**
- Embedding API is a first-class citizen, not an afterthought
- Security must be addressed in Phase 0-1 (not deferred to Phase 4)
- GPL v2 compliance analysis is a release BLOCKER
- Windows Authenticode signing is essential for user adoption
- Thread safety contract must be defined before AI panel implementation
- Atomic save writes are mandatory (standard practice)

### v2.1.0 (2026-02-25) — DOSBox-X Parity Gap Analysis

Changes incorporated from `feedbackGemini.md` compatibility gap analysis:

**Phase 2 additions (Release A):**
- **REQ-MOUNT-001**: Host directory mounting (drive letter mapping via .conf, CLI, or menu)
- **REQ-MOUNT-002**: Block device image mounting (.iso, .cue/.bin, .img with MSCDEX/FAT)
- **REQ-INPUT-004**: Clipboard paste — host-to-guest keystroke injection via `legends_text_input()`
- **REQ-CAPTURE-003**: Video capture streaming — AVI/ZMBV encoding with synchronized audio

**Phase 3 additions (Release B):**
- **REQ-NET-001**: IPX network emulation over UDP (multiplayer DOS games)
- **REQ-HW-001**: 3dfx Voodoo / Glide → OpenGL translation (Windows 9x games)
- **REQ-HW-002**: NEC PC-98 architecture support (memory map, GDC, YM2608)
- **REQ-AUDIO-003**: Advanced MIDI synthesis — FluidSynth (SoundFont) and MUNT (MT-32 emulation)

**Phase 4 additions (testing strategy):**
- **REQ-TEST-008**: Soak testing — 12-24hr endurance runs monitoring memory and audio health
- **REQ-TEST-009**: Performance regression benchmarking — IPS baseline comparison per commit
- **REQ-TEST-010**: Fuzz testing — libFuzzer targets for config parser, input injection, save state loader, IPX packets
- **REQ-TEST-011**: Save state forward-compatibility matrix — versioned .sav archive tested on each build
- **REQ-TEST-012**: Deterministic rendering validation — SSIM > 99% for shader/3dfx FBO output

**New risks:**
- RISK-013: 3dfx/Glide translation accuracy across GPU vendors
- RISK-014: FluidSynth/MUNT library licensing and bundling
- RISK-015: IPX network security exposure
- RISK-016: Video encoding performance impact on frame rate
- RISK-017: Save state forward-compatibility breakage

**Parity scoreboard expanded** with 10 new feature rows (mounting, clipboard, video recording, networking, 3dfx, PC-98, MT-32, FluidSynth, Windows 9x).

**Compatibility corpus expanded** with Tier 4 (advanced hardware targets) for Release B validation.

### v2.0.0 (2026-02-25) — Deep Review Revision

Changes incorporated from deep review:

**Critical fixes:**
- Added **Phase -1: Engine I/O Plumbing** (REQ-PLUMB-001 through 005) — addresses real framebuffer and audio paths not being wired
- Split **release definition** into Release A (Core Emulator) and Release B (Differentiators) — AI no longer blocks core shipping
- Added **release gates** G1 (framebuffer), G2 (audio), G3 (compatibility), G4 (packaging)
- Replaced "Existing Assets (No Changes Needed)" with **Interface Delta** section acknowledging required changes

**High-priority fixes:**
- Added **menu abstraction policy**: menus are app-layer, intentionally outside PAL (no `IMenuHost`)
- Defined **presentation ownership contract** (Section 2.5): context owns present, not window
- Addressed **dynamic resolution lifecycle** (REQ-VIDEO-002): destroy/recreate sequence with cache
- Fixed **slot count inconsistency**: standardized on 9 slots everywhere (hotkeys now Ctrl+Shift+F1..F9 and Ctrl+Alt+F1..F9)
- Fixed **mouse release inconsistency**: Ctrl+F10 is primary, middle mouse is documented alternative
- Fixed **Linux capture path typo** (was backslash, now forward slash)
- Normalized all paths to **XDG directory policy** (Appendix D)
- Moved **packaging skeleton** to Phase 0 (REQ-BUILD-005)

**Medium-priority additions:**
- Added **ActionBus** centralized dispatch (Section 2.3)
- Added **State Ownership Map** (Section 2.7)
- Added **execution profiles** (interactive/deterministic/benchmark) to REQ-CORE-001
- Added **spin-wait hybrid** frame pacing to REQ-THROTTLE-001
- Noted **window title mismatch** (`WindowConfig::title` default is "DOSBox-X") in REQ-BUILD-002
- Added **AI guardrails**: opt-in default, privacy mode, context budget controls
- Added **golden visual tests** (REQ-TEST-004), **audio validation** (REQ-TEST-005), **replay determinism** (REQ-TEST-006), **UI smoke test** (REQ-TEST-007)
- Converted most manual-only verification items to **automatable proxy checks**
- Added **DOSBox-X Parity Scoreboard** (Appendix E)
- Added **Compatibility Corpus** (Appendix F) with 3-tier structure

**New risks:**
- RISK-011: Framebuffer not wired to real engine VRAM (critical)
- RISK-012: Context recreate storms on rapid mode switches
