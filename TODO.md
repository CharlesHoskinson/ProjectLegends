# Project Legends — Implementation Status Audit

**Last updated:** 2026-06-10
**Audited against:** `ROADMAP.md` v4.2.1-record (206 tracked requirements)

---

## Overall Progress

| Phase | Status | Implemented | Stub/Partial | Missing |
|-------|--------|-------------|--------------|---------|
| Phase -1: Engine I/O Plumbing | **COMPLETE** | All 5 REQs | — | — |
| Phase 0: Build Infrastructure | **COMPLETE** | All 5 core REQs | — | — |
| Phase 1: MVP | **COMPLETE** | All 13 core REQs | — | — |
| Phase 2: Core Experience | **COMPLETE** | All 18 REQs | — | — |
| Phase 3: Enhanced Features | **PARTIAL** | 7 of 14 REQs | 4 stubs | 3 missing |
| Phase 4: Polish & Release | **COMPLETE** | All 16 core REQs | — | — |
| Security Hardening | **PARTIAL** | 6 of 22 | — | 16 missing |
| GPL v2 Process Isolation | **PARTIAL** | IPC wire/messages/SHM/audio/control pieces exist | `protocol.cpp` stub + proxy parity gaps | Remaining parity/verification |
| Wasm Sandbox | **DEFERRED** | 0 of 50 (deferred 2026-06-10) | — | deferred — see ROADMAP §15 |
| UX & Accessibility | **PARTIAL** | 2 of 11 | — | 9 missing |

---

## Phase -1: Engine I/O Plumbing — COMPLETE

All items implemented and tested:

- [x] REQ-PLUMB-001 — Engine framebuffer sync (real VRAM)
- [x] REQ-PLUMB-002 — Real text-mode font rendering (VGA ROM glyphs)
- [x] REQ-PLUMB-003 — Engine audio path activation
- [x] REQ-PLUMB-004 — Audio sample transfer interface
- [x] REQ-PLUMB-005 — Presentation contract enforcement test

---

## Phase 0: Build Infrastructure — COMPLETE

- [x] REQ-BUILD-001 — SDL3 executable CMake target (`project_legends`)
- [x] REQ-BUILD-002 — main.cpp with Application class, window, event loop
- [x] REQ-BUILD-003 — Cross-platform CI (Win/Linux/macOS) via `ci.yml`
- [x] REQ-BUILD-004 — Application class skeleton with PAL service ownership
- [x] REQ-BUILD-005 — Packaging skeleton (NSIS, AppImage, macOS bundle in cmake/)
- [x] REQ-OPS-001 — SDL3 version pinning
- [x] REQ-OPS-002 — Hermetic CI builds
- [x] REQ-ISO-001 — COPYING file (GPL v2)
- [x] REQ-ISO-002 — NOTICE file, LICENSES/ directory

---

## Phase 1: MVP — Display, Input, Audio — COMPLETE

All core requirements implemented in `src/app/application.cpp`:

- [x] REQ-CORE-001 — Engine initialization with profile presets
- [x] REQ-CORE-002 — Run loop stepping at ~60 FPS
- [x] REQ-CORE-003 — Clean shutdown
- [x] REQ-VIDEO-001 — Framebuffer capture and RGB blit display
- [x] REQ-VIDEO-002 — Dynamic resolution handling (destroy/recreate context)
- [x] REQ-INPUT-001 — Keyboard SDL3→AT Set 1 translation (`scancode_map.cpp`, `input_mapper.cpp`)
- [x] REQ-INPUT-002 — Mouse input translation + relative delta injection
- [x] REQ-INPUT-003 — Mouse capture toggle (middle-click release)
- [x] REQ-AUDIO-001 — Audio output via push model (`pumpAudio()`)
- [x] REQ-AUDIO-002 — Volume control + mute (`audio_mixer.cpp`)
- [x] REQ-THROTTLE-001 — Frame pacing with spin-wait hybrid
- [x] REQ-CONFIG-001 — .conf file loading (`config_parser.cpp`)
- [x] REQ-CLI-001 — Full CLI parser (--conf, --fullscreen, --cycles, --machine, --memsize, --profile, --log, --version, --help)

---

## Phase 2: Core Experience — COMPLETE

### Implemented

- [x] REQ-MENU-001 — Enhanced menu bar with dropdowns (`menu_system.cpp` — bar mode)
- [x] REQ-MENU-002 — Overlay menu (F12 hotkey, `menu_system.cpp`)
- [x] REQ-MENU-003 — Pause emulation on menu open
- [x] REQ-SAVE-001 — Save state to file (9 slots, `save_manager.cpp`)
- [x] REQ-SAVE-002 — Load state from file (9 slots)
- [x] REQ-SAVE-003 — Save slot visual browser with 3x3 grid (`save_browser.cpp`)
- [x] REQ-SAVE-004 — Platform-appropriate save directory (`platform_dirs.cpp`)
- [x] REQ-MAPPER-001 — Key mapper visual UI with capture mode (`mapper_ui.cpp`)
- [x] REQ-MAPPER-002 — Mapper persistence (mapper.txt loading)
- [x] REQ-MAPPER-003 — Default SDL3→AT Set 1 scancode table (104 keys)
- [x] REQ-CAPTURE-001 — Screenshot to PNG (Ctrl+F5, `capture.cpp`)
- [x] REQ-CAPTURE-002 — Capture directory with timestamps
- [x] REQ-CAPTURE-003 — Video capture AVI/ZMBV with audio (`video_capture.cpp`, `zmbv_codec.cpp`)
- [x] REQ-PAUSE-001 — Pause/resume emulation (Alt+Pause)
- [x] REQ-RESET-001 — Machine reset (Ctrl+Alt+Delete → `legends_reset`)
- [x] REQ-MOUNT-001 — Host directory mounting (`mount_manager.cpp`, `legends_mount_drive` API)
- [x] REQ-MOUNT-002 — Block device image mounting (.iso, .img, .cue/.bin)
- [x] REQ-INPUT-004 — Clipboard paste (Ctrl+Shift+V via SDL3 clipboard)

---

## Phase 3: Enhanced Features — PARTIAL

### Implemented

- [x] REQ-FULLSCREEN-001 — Fullscreen toggle (Alt+Enter via `hotkey_dispatcher`)
- [x] REQ-JOYSTICK-001 — Joystick/gamepad support (`joystick_mapper.cpp`, wired to engine)
- [x] REQ-SHADER-001 — OpenGL shader rendering path (`shader_renderer.cpp`)
- [x] REQ-SHADER-002 — Shader preset selection (CRT, Scanlines, Sharp, Smooth in `shader_presets.cpp`)
- [x] REQ-AI-001 — AI assistant panel (`ai_panel.cpp`, opt-in, async, non-blocking)
- [x] REQ-AI-002 — AI screen context capture (`ai_screen_context.cpp`)
- [x] REQ-AI-003 — AI configuration with privacy mode (`ai_config.cpp`)
- [x] REQ-TTF-001 — TrueType font rendering (`ttf_renderer.cpp` via stb_truetype)

### Stubs (config UI exists, engine wiring missing)

- [~] REQ-NET-001 — **IPX networking**: `ipx_config.cpp` loads from INI, but `legends_ipx_*` functions are TODO stubs in `legends_embed_api.cpp`
- [~] REQ-HW-001 — **3dfx Glide**: `glide_config.cpp` loads from INI, but `legends_glide_*` functions are TODO stubs
- [~] REQ-HW-002 — **PC-98**: `pc98_config.cpp` loads from INI, but `legends_set_machine_pc98` is a TODO stub
- [~] REQ-MIDI-001 — **MIDI routing**: `midi_config.cpp` loads from INI, but actual MIDI output routing depends on engine wiring

### Missing

- [ ] REQ-PRINT-001 — **Printer emulation**: `printer_manager.cpp` exists but LPT1 capture not wired to engine
- [ ] REQ-AUDIO-003 — **Advanced MIDI synthesis** (FluidSynth/MUNT not integrated)

---

## Phase 4: Polish & Release — COMPLETE

All core testing and packaging requirements implemented:

### Testing (all have test files)

- [x] REQ-TEST-001 — Unit test coverage (98 unit test files across `tests/unit/`)
- [x] REQ-TEST-002 — Boot to prompt integration test (`test_boot_to_prompt.cpp`)
- [x] REQ-TEST-003 — Determinism verification (`test_determinism_hash.cpp`)
- [x] REQ-TEST-004 — Golden visual snapshot tests (`test_golden_visual.cpp`)
- [x] REQ-TEST-005 — Audio validation (`test_audio_validation.cpp`)
- [x] REQ-TEST-006 — Replay determinism (`test_replay_determinism.cpp`)
- [x] REQ-TEST-007 — Cross-platform smoke test (`test_cross_platform_smoke.cpp`)
- [x] REQ-TEST-008 — Soak testing (`test_soak_endurance.cpp`, `soak-nightly.yml`)
- [x] REQ-TEST-009 — Performance benchmarks (`bench_emulation.cpp`, `baseline_perf.json`)
- [x] REQ-TEST-010 — Fuzz testing (`fuzz_config_parser.cpp`, `fuzz_engine_load_state.cpp`, `fuzz_input_injection.cpp`, `fuzz-nightly.yml`)
- [x] REQ-TEST-011 — Save state compatibility (`test_save_state_compat.cpp`)
- [x] REQ-TEST-012 — Visual regression SSIM (`test_visual_regression.cpp`, `ssim.cpp`)

### Packaging

- [x] REQ-PACKAGE-001 — Windows NSIS installer (`cmake/nsis_config.nsi.in`)
- [x] REQ-PACKAGE-002 — Linux AppImage (`cmake/appimage.cmake`)
- [x] REQ-PACKAGE-003 — macOS bundle (`cmake/macos_bundle.cmake`)
- [x] REQ-PACKAGE-004 — Portable mode (`portable_mode.cpp`, `portable.txt` detection)

### Logging, Errors, Operations

- [x] REQ-LOG-001 — Structured JSON logging (`file_logger.cpp`, rotation, permissions)
- [x] REQ-ERROR-001 — User-facing error reporting (`error_reporter.cpp`)
- [x] REQ-OPS-017 — Update checker (`update_checker.cpp` + platform implementations)
- [x] REQ-OPS-028 — Crash reporting (`crash_reporter.cpp`, signal handlers)
- [x] REQ-OPS-029 — Crash breadcrumb ring buffer (`crash_breadcrumb.cpp`)
- [x] REQ-OPS-022 — LICENSES/ directory + NOTICE with SPDX
- [x] REQ-SEC-040 — Restrictive log file permissions (0600/ACL)

---

## Not Yet Implemented — Grouped by Priority

### Must-Have (Release Blockers)

| Req ID | Description | Category | Effort |
|--------|-------------|----------|--------|
| REQ-SEC-031 | Formal threat model document | Security | Medium |
| REQ-SEC-010 | Save state header + CRC validation | Security | Medium |
| REQ-SEC-011 | Save state file size limit (256 MB) | Security | Small |
| REQ-SEC-023 | Canonical path resolution for mounts | Security | Medium |
| REQ-SEC-024 | Read-only mount option | Security | Small |
| REQ-API-004 | `legends_mount_drive()` C API | API | Large |
| REQ-ISO-003–016 | GPL v2 Process Isolation (IPC) | Isolation | Very Large |
| REQ-WASM-001–050 | Wasm Sandbox (50 requirements) | Wasm | Very Large |

### Should-Have (Important for Quality)

| Req ID | Description | Category | Effort |
|--------|-------------|----------|--------|
| REQ-UX-001 | First-run wizard | UX | Medium |
| REQ-UX-002 | Drag-and-drop program launch | UX | Small |
| REQ-UX-005 | Performance overlay (FPS counter) | UX | Small |
| REQ-UX-008 | DPI-aware UI scaling | UX | Medium |
| REQ-UX-009 | Keyboard-only menu navigation | UX | Small |
| REQ-UX-010 | Autosave on crash + recovery | UX | Medium |
| REQ-SEC-035 | Code signing (Authenticode/notarize/GPG) | Security | Medium |
| REQ-SEC-036 | SHA-256 checksum publication | Security | Small |

### Could-Have (Deferred/Enhancement)

| Req ID | Description | Category | Effort |
|--------|-------------|----------|--------|
| REQ-NET-001 | IPX networking (engine wiring) | Phase 3 | Large |
| REQ-HW-001 | 3dfx Glide → OpenGL | Phase 3 | Very Large |
| REQ-HW-002 | PC-98 support (engine wiring) | Phase 3 | Large |
| REQ-AUDIO-003 | FluidSynth/MUNT MIDI synthesis | Phase 3 | Large |
| REQ-PRINT-001 | Printer emulation (LPT1 to file) | Phase 3 | Medium |
| REQ-UX-004 | Command palette | UX | Medium |
| REQ-UX-006 | GUI settings dialog | UX | Large |
| REQ-UX-011 | Hung guest detection | UX | Small |

---

## Engine-Level Technical Debt

These items from the original sprint tracking remain open:

### Open

- [ ] **Eliminate thread-local `current_context()` accessors** — Macro redirects still exist in headers
- [ ] **Remove compat shim files** — `dma_compat.cpp`, `memory_compat.cpp`, `pic_compat.cpp`, `vga_compat.cpp`, `int10_compat.cpp`, `state_hash_compat.cpp`, `cpu_bridge.h`/`cpu_bridge.cpp`
- [ ] **Machine context subsystem initialization** — 8 placeholder TODOs in `machine_context.cpp` (PIC, PIT, VGA, keyboard, mouse, sound, DOS kernel, emulation logic)
- [ ] **Dead code removal** — Unused networking, printer/parallel drivers in vendored engine

### Complete

- [x] Sprint 1 — Library Foundation
- [x] Sprint 2 — Instance Reality (global migration 87%, 61/70 migrated)
- [x] Sprint 3 — Module Graph (DAG enforcement)
- [x] Phase -1 — Engine I/O Plumbing (all 5 REQs)
- [x] CPU bridge wired, serialization V4, CI hardening, context unification

---

## File Inventory Summary

| Category | Count |
|----------|-------|
| `src/app/*.cpp` + `*.h` | 35 component pairs (70 files) |
| `tests/unit/*.cpp` | 98 test files |
| `tests/integration/*.cpp` | 28 test files |
| `tests/fuzz/*.cpp` | 5 fuzz targets |
| `benchmarks/*.cpp` | 2 benchmark suites |
| `.github/workflows/*.yml` | 6 CI workflows |
| `cmake/*.cmake` | 11 build modules |
| `scripts/*.py` | 15 utility scripts |

---

## Key Architectural Decisions (Implemented)

| Decision | Implementation |
|----------|---------------|
| GUI framework | Overlay menu via RGB framebuffer blit (`menu_system.cpp`) — not native SDL3 menus |
| Rendering | Software context RGB blit for core; OpenGL shader path (`shader_renderer.cpp`) for Phase 3 |
| Audio model | Push-based via `IAudioSink::pushSamples()` with MIDI mixing |
| Configuration | INI-style `.conf` files (`config_parser.cpp`) |
| AI integration | Async HTTP client + overlay panel (`ai_panel.cpp`, `ai_http_client.cpp`) |
| Logging | Structured JSON Lines to file with rotation (`file_logger.cpp`) |
| Crash handling | Signal/exception handler + breadcrumb ring buffer (`crash_reporter.cpp`) |
| IPC isolation | **PARTIAL** — `src/legends_ipc/` contains real wire/message, framebuffer SHM, audio ring, shared-memory, control-channel, and engine-spawner code; `src/legends_ipc/protocol.cpp` is still a one-line stub and proxy parity gaps remain |
| Wasm sandbox | **NOT STARTED** — documentation only |
