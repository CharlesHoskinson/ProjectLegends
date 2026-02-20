# Project Legends Codebase Audit

Date: 2026-02-21
Scope: Full repository audit across 5 dimensions

---

## Current State

Project Legends is an embeddable x86 emulation framework built on a refactored DOSBox-X engine. Three sprints are complete:
- Sprint 1: Library foundation (C API, error model, handle system)
- Sprint 2: Instance reality (global-to-context migration, 87% complete)
- Sprint 3: Module graph (DAG enforcement, build boundaries)

~1.2M lines of vendored DOSBox-X engine code, ~24.5K lines of new wrapper code. C API surface is complete (22 functions, all implemented). CI covers 3 platforms with sanitizers.

---

## Top Findings by Severity

### Critical

| # | Finding |
|---|---------|
| C1 | **Massive code duplication** -- 27+ header pairs and 11 source pairs are near-identical between `src/legends/` and `engine/src/aibox/`, differing only in namespace. Same logic compiled twice. Bug fixes must be manually replicated. |
| C2 | **CPU bridge is a stub** -- `cpu_bridge.cpp` does not execute any x86 instructions. It increments counters in a loop. The real emulation runs through legacy DOSBox-X `Normal_Loop()`, not through this bridge. |
| C3 | **gsl-lite version mismatch** -- root fetches v1.0.0, engine fetches v0.41.0, FetchContent deduplication silently gives everyone v1.0.0. |

### High

| # | Finding |
|---|---------|
| H1 | **State serialization loses data** -- mixer, VGA, DMA, DOS kernel not serialized. PIC partially serialized. Keyboard buffer truncated 96->16 entries causing potential OOB reads on load. |
| H2 | **No endianness handling** in serialization. Cross-platform state files broken. |
| H3 | **Missing security hardening flags** -- no stack protectors, FORTIFY_SOURCE, RELRO, CFI, or Control Flow Guard. |
| H4 | **Engine-wide `/wd4244` suppression** silences narrowing conversion warnings across an x86 emulator where register widths are critical. |
| H5 | **Three unsynchronized `g_current_context` pointers** across dosbox/aibox/legends layers. Cross-layer calls can see stale contexts. |
| H6 | **Broken CMake package export** -- LegendsTargets.cmake never generated. |
| H7 | **No fuzzing in CI** -- harnesses exist but never run. |
| H8 | **No TLA+ verification in CI** -- model checking the 4 minimal specs takes seconds. |

### Medium

| # | Finding |
|---|---------|
| M1 | Reentrancy guard declared but unenforced |
| M2 | `legends_text_input` partial commit on queue-full (stuck shift) |
| M3 | 8 of 10 MachineContext subsystem initializers are stubs |
| M4 | Config string pointers not deep-copied (dangling after create) |
| M5 | Static `last_buttons` in mouse injection leaks across instances |
| M6 | `dosbox_lib_destroy()` has no thread check (race with owner) |
| M7 | MixerState accessed from callback thread without synchronization |
| M8 | 30-40 mutable extern globals not tracked in registry |
| M9 | Sprint 3 phases 2/4/5/6 unimplemented |
| M10 | headless_stub.cpp has 7 process-global variables |
| M11 | No code coverage reporting in CI |
| M12 | No MSan or TSan CI jobs |

---

## What Works Well

- C API surface is well-designed and complete. Null checks, bounds validation, thread affinity, and error codes are consistent.
- Save/load has robust integrity verification (CRC32, section bounds, four-phase atomic load).
- Module DAG (legends_core -> aibox_core, legends_pal -> nothing) is clean and CI-enforced.
- Test suite exercises real engine behavior, not mocks. Determinism tests prove input-to-engine coupling.
- Compat shim containment works: `current_context()` usage properly confined to shim files.
- Python tooling scripts are clean, well-documented, and CI-integrated.
- PAL abstraction is cleanly designed with proper interface segregation.

---

## 1. Public API & Implementation

### Files Examined

- `include/legends/legends_embed.h` (stable C ABI surface)
- `include/legends/handle_registry.h`
- `include/legends/machine_context.h`
- `include/pal/*.h` (all PAL interface headers)
- `src/legends/legends_embed_api.cpp` (2459 lines)

### API Completeness

All 22 declared functions are implemented. No stubs remain. The "Phase 4+: stubs" comment at line 8 of the implementation is stale.

### Safety

Consistently applied. Every handle-taking function validates via `get_instance()` and checks output pointers with `LEGENDS_REQUIRE`. Save/load uses four-phase atomic load pattern. Bounds checking uses `SAFE_MULTIPLY_OR_ERROR`, `VALIDATE_SECTION_BOUNDS`, `VALIDATE_DATA_BOUNDS`, `VALIDATE_COUNT_MAX` macros.

### Findings

**M1: Reentrancy guard declared but not enforced.** `LEGENDS_ERR_REENTRANT_CALL` (-5) is defined but never returned. No `in_step` flag exists. A log callback re-entering `legends_step_ms()` would corrupt state.

**M2: `legends_text_input` partial commit on queue-full.** If the input queue fills mid-character (after shift-down but before key press), the shift key gets stuck down. No rollback.

**M3: 8 of 10 MachineContext subsystem initializers are TODO stubs.** PIC, PIT, VGA, keyboard, mouse, sound, DOS kernel, and BIOS init are all `return Ok()`. Emulation delegated entirely to DOSBox-X engine bridge.

**L1: README documents 15 of 22 functions.** Missing: `legends_get_api_version`, `legends_get_config`, `legends_key_event_ext`, `legends_is_frame_dirty`, `legends_get_cursor`, `legends_get_last_error`, `legends_set_log_callback`.

**L2: README says SaveStateHeader is 96 bytes; code has `static_assert(...== 64)`.** Documentation is wrong.

**L3: Three error codes defined but never used:** `REENTRANT_CALL` (-5), `IO_FAILED` (-10), `NOT_SUPPORTED` (-12).

**L4: HandleRegistry fully implemented but unused.** Embed API uses raw pointer comparison. Dead code until API unification.

**L5: `LEGENDS_ERROR` macro collision.** `error.h` defines it one way; `legends_embed_api.cpp` undefs and redefines it differently.

**L6: `LEGENDS_TRY` macro uses GCC statement expressions.** Incompatible with MSVC.

**L7: `legends_destroy` fallback path** will destroy any active instance even with wrong handle.

### Dual API Surface

Two parallel FFI surfaces exist:
1. `include/legends/legends_embed.h` (stable, active)
2. `engine/include/aibox/ffi_*.h` (legacy, deprecated)

TODO.md task #14 acknowledges this.

---

## 2. Engine Bridge Layer

### Files Examined

- `engine/include/dosbox/dosbox_library.h`
- `engine/include/dosbox/dosbox_context.h`
- `engine/include/dosbox/engine_state.h`
- `engine/include/dosbox/engine_services.h`
- `engine/include/dosbox/cpu_bridge.h`
- `engine/src/misc/dosbox_library.cpp`
- `engine/src/misc/cpu_bridge.cpp`

### Implemented vs Stubbed

| Component | Status |
|-----------|--------|
| C API surface (17 functions) | Fully implemented |
| Context structure with subsystem states | Fully implemented |
| State serialization (5 subsystems) | Implemented, partial coverage |
| Service table / DI pattern | Fully implemented |
| Instance registry with generations | Fully implemented but unused |
| Error model and safe_call boundary | Fully implemented |
| **CPU execution bridge** | **STUB -- no real CPU execution** |

### CPU Bridge Is a Stub

`cpu_bridge.cpp` does NOT execute any x86 instructions. It increments counters in a loop:

```cpp
// STUB IMPLEMENTATION: Simulate CPU execution
result.cycles_executed += batch;
cycles_remaining -= batch;
result.events_processed++;
```

The real emulation runs through the legacy DOSBox-X `Normal_Loop()` / `PIC_RunQueue()` path.

### State Serialization Data Loss

| Subsystem | Serialized | Notes |
|-----------|-----------|-------|
| Timing | Yes | Full coverage |
| CPU | Yes | Full coverage |
| PIC | Partial | Only IMR/ISR + master auto_eoi. Missing: IRR, priority, ICW state, slave auto_eoi, 10+ fields per controller |
| Keyboard | Partial | Buffer truncated from 96 to 16 entries. `buffer_used` can exceed 16 after load, causing OOB reads |
| Memory config | Yes | Full coverage |
| **Mixer** | **No** | Entire audio state lost |
| **VGA registers** | **No** | Display mode/state lost |
| **DMA channels** | **No** | Transfer state lost |
| **DOS kernel** | **No** | PSP/DTA/file handles lost |

No endianness handling. No alignment check on load (`reinterpret_cast` on unaligned buffer is UB). Version check is exact match only -- no forward compatibility.

### Library-Layer Global State

Despite context-based architecture, the library layer is a singleton wrapper around file-scoped globals: `g_instance_exists`, `g_owner_thread_id`, `g_context`, `g_config`, `g_last_error`, `g_log_state`, `g_time_state`.

- `g_last_error` not thread-safe (`dosbox_lib_get_last_error()` skips thread check)
- Static `last_buttons` in mouse injection leaks across instance lifetimes
- `dosbox_lib_destroy()` has no thread check
- Dual `total_cycles` accounting between `ctx->timing` and `g_time_state`
- Config string pointers not deep-copied (dangling risk)

### Context Structure Issues

- VGA hardware state partially opaque (`VGA_Type_t* hw` ~20KB, `reset()` doesn't reset it)
- DMA state holds raw pointers (double-reset leaks)
- DosFilesystemState holds raw pointer arrays
- MixerState has thread safety notes but no synchronization (data race)
- TickerBlock function pointers have no context parameter (relies on thread-local)

---

## 3. Tests, TLA+ Specifications, and CI/CD

### Test Coverage

All 22 public API functions have test coverage. Tests exercise real DOSBox-X engine behavior through the headless backend.

**Gaps:**

| Area | Gap |
|------|-----|
| PIC/PIT device models | TLA+ specs exist but no C++ unit tests |
| Scheduler | Heavily specified in TLA+ but no `test_scheduler.cpp` |
| EmuKernel | Top-level state machine in TLA+ has no C++ test |
| Audio | `legends_push_audio` only tested in contract gates |
| DOS program execution | No test loads/runs an actual COM/EXE binary |
| SVGA mode | No test exercises SVGA machine type |
| Long-running determinism | All tests run <200K cycles |
| Multi-process determinism | All tests single-process |
| Graphics mode determinism | All tests use default text mode |

### TLA+ Specifications

Only 4 of 15 specifications are model-checked:

| Spec | Properties Verified | States |
|------|-------------------|--------|
| LifecycleMinimal | AtMostOneInstance, MisuseSafe, HandleConsistency | 85 |
| PALMinimal | AudioPushModel, ThreadSafety, AudioQueueBounded | 99 |
| ThreadingMinimal | CoreSingleThreaded, PALIsolation, NoDataRaces | 1,474 |
| SaveStateTest | ObservationPreserved, EventCountPreserved, TimePreserved | 8 |

11 specs (EmuKernel, Scheduler, Determinism, APIContract, Bus, DMA, PIC, PIT, Capture, Input, and full Lifecycle/PAL/Threading) are documentation only.

**Event queue serialization gap.** SaveState.tla notes: "DOSBox-X implementation does NOT serialize the event queue." But EmuKernel.tla's `Obs()` includes `Q_digest`. Round-trip invariant may not hold for states with pending events.

### CI/CD

**Exists:** `ci.yml` (Linux/Windows/macOS, ASan, UBSan, clang-tidy), `pal-ci.yml` (backend builds, contract gates, symbol firewall), `module-dag.yml` (include rules, DAG verify), `sprint2-checks.yml` (globals tracking, migration status).

**Missing:**

| Missing | Impact |
|---------|--------|
| No fuzzing CI job | Harnesses exist but never run |
| No TLA+ verification in CI | Model checking takes seconds |
| No code coverage reporting | Cannot quantify what's tested |
| No MSan job | Misses uninitialized memory reads |
| No TSan job | Data races could hide |
| clang-tidy scope too narrow | Only `engine/src/misc` |
| `check_gsl_lite_usage.py` not in any workflow | Script exists but unused |

### Fuzzing

Exists: `fuzz_engine_load_state.cpp`, `fuzz_legends_load_state.cpp`, `generate_corpus.cpp`. Missing: no fuzz targets for input injection, configuration, capture functions. No continuous fuzzing integration. No differential fuzzing for determinism.

### Determinism Tests

Meaningful, not trivial. `InputAffectsStateBeyondTime` proves input-to-engine coupling. `DeterministicReplayAfterLoad` proves save/load + determinism compose. But all tests run <200K cycles in text mode within a single process.

---

## 4. Build System and Code Quality

### Build Issues

**CRITICAL: gsl-lite version mismatch.** Root fetches v1.0.0, engine fetches v0.41.0. FetchContent deduplication means engine always gets v1.0.0. Engine also links gsl-lite as PUBLIC (leaks) while root links PRIVATE.

**HIGH: Broken package export.** `LegendsConfig.cmake.in` includes `LegendsTargets.cmake` but no `install(TARGETS ... EXPORT LegendsTargets)` exists. `find_package(Legends)` will fail.

**HIGH: Missing security hardening flags.** No `-fstack-protector-strong`, `-D_FORTIFY_SOURCE=2`, `-fPIE`, `-Wl,-z,relro,-z,now`, `-fcf-protection`, `/GUARD:CF`.

**MEDIUM: `project_legends` executable unbuildable.** `src/main.cpp` and `external/SDL2/` don't exist. Hardcoded `mingw32` link. Gated behind PAL_BACKEND_SDL2 so headless builds are fine.

### Code Duplication

11 duplicated source file pairs between `src/legends/` and `engine/src/aibox/`:

| Legends layer | Engine layer |
|---------------|-------------|
| `llm_frame.cpp` | `llm_frame.cpp` |
| `llm_actions.cpp` | `llm_actions.cpp` |
| `llm_diff.cpp` | `llm_diff.cpp` |
| `llm_serializer.cpp` | `llm_serializer.cpp` |
| `machine_context.cpp` | `machine_context.cpp` |
| `vision_framebuffer.cpp` | `vision_framebuffer.cpp` |
| `vision_capture.cpp` | `vision_capture.cpp` |
| `vision_overlay.cpp` | `vision_overlay.cpp` |
| `vision_annotations.cpp` | `vision_annotations.cpp` |
| `headless_stub.cpp` | `headless_stub.cpp` |
| `legends_embed_api.cpp` | `dosboxx_embed_api.cpp` |

Plus 27+ duplicated header pairs. Both compile into separate static libraries. Same logic twice, two namespaces.

### Suppressed Warnings

| Suppression | Scope | Risk |
|-------------|-------|------|
| `/wd4244` (narrowing) | Entire engine | Silences data loss bugs in register operations |
| `_CRT_SECURE_NO_WARNINGS` | Entire project | Blanket-suppresses insecure C runtime |

### TODO Inventory

| File | Line | Content | Severity |
|------|------|---------|----------|
| `machine_context.cpp` | 228 | "Actual emulation would go here" | Critical |
| `machine_context.cpp` | 381-417 | PIC/PIT/VGA/keyboard/mouse/sound/DOS/BIOS init stubs | High |
| `llm_frame.cpp` | 267 | "Implement actual diff logic" | High |
| `cpu_context.h` | 521 | "Add paging translation" | Medium |
| `cpu_context.h` | 534 | "Check stack segment B bit" | Low |

7 forward-declared classes (VgaContext, DosKernel, PicController, PitTimer, KeyboardController, MouseController, SoundSubsystem) have no definitions anywhere.

### sprint3/ Directory

Planning documentation for partially-complete work. Only Phases 1 and 3 implemented (ModuleManifest.cmake, ModuleDAG.cmake). Phases 2, 4, 5, 6 unimplemented.

---

## 5. Global State Migration and AIBox Layer

### Migration Progress

| Category | Count | % |
|----------|-------|---|
| Migrated | 61 | 87% |
| Deferred | 9 | 13% |
| **Total tracked** | **70** | |

An estimated 30-40 additional mutable extern globals in `engine/include/` are NOT tracked (callback.h, bios.h, bios_disk.h, cpu.h, dos_inc.h).

### The 9 Deferred Globals

| # | Name | File | Why Deferred |
|---|------|------|-------------|
| 1 | `cycle_count` | `core_normal.cpp` | Core-local transient counter. Invasive to migrate. |
| 2 | `SDL2_AudioDevice` | `mixer.cpp` | SDL handle. Dead in headless mode. |
| 3 | `MixTemp` | `mixer.cpp` | Scratch buffer. Dead in headless mode. |
| 4 | `sdl` | `sdlmain.cpp` | Giant SDL state. Dead in headless mode. |
| 5 | `frames` | `sdlmain.cpp` | Frame counter. Dead in headless mode. |
| 6 | `currentWindowWidth` | `sdlmain.cpp` | Window dim. Dead in headless mode. |
| 7 | `currentWindowHeight` | `sdlmain.cpp` | Window dim. Dead in headless mode. |
| 8 | `BIOS_drive_signature` | `bios.cpp` | Determinism-relevant. Needs BiosState struct. |
| 9 | `g_log_callback` | `logging.cpp` | Global callback. Arguably correct. |

7 of 9 are SDL/display globals dead in headless mode. Items 1 and 8 need migration for multi-instance or replay.

### current_context() Usage

All production usage properly contained to 6 compat shim files (33 total calls). No calls in headers. Test code has ~90 calls (legitimate fixture setup). `state_hash_compat.cpp` is ripe for immediate cleanup.

### Thread-Local State: Three Unsynchronized Contexts

The dosbox, aibox, and legends layers each maintain their own `g_current_context` thread-local. These are NOT synchronized. `compat::ContextGuard` in aibox sets the aibox-layer context but does NOT set the dosbox-layer context. Cross-layer calls see stale or null contexts.

10 total thread_local variables across the codebase (3 context pointers, 4 error buffers, 2 error flags, 1 pre-creation error string).

### AIBox Layer

The aibox layer is the DOSBox-X-side API (in `engine/`). It provides a complete parallel C API (`ffi_core.h`, `ffi_llm.h`, `ffi_vision.h`, `ffi_events.h`). `dosboxx_embed_api.cpp` is explicitly `@deprecated`.

What aibox has that legends doesn't: LLM integration (batch actions, token-efficient frames), vision model support (capture, annotations), event bus subscription.

### Multi-Instance Bug Risks

| Risk | Severity |
|------|----------|
| Three unsynchronized `g_current_context` pointers | High |
| headless_stub.cpp globals (7 vars including `g_virtual_ticks`) | Medium |
| Untracked legacy externs: CallBack_Handlers[], imageDiskList[], BIOS state | Medium |
| dosboxx_embed_api.cpp has parallel singleton enforcement | Medium |
| pic_compat.cpp / memory_compat.cpp static fallbacks | Low |

---

## Sprint Recommendation

### Option A: "Consolidation Sprint" (reduce technical debt)

Focus: eliminate the duplication, fix the build, harden the foundation.

| Task | Priority | Effort |
|------|----------|--------|
| Unify legends/aibox layers (eliminate 38+ duplicate files) | Critical | Large |
| Fix gsl-lite version mismatch | Critical | Small |
| Add security hardening flags | High | Small |
| Fix CMake package export | High | Small |
| Remove or fix unbuildable `project_legends` target | Medium | Small |
| Clean up sprint3/ stale docs | Medium | Small |
| Add reentrancy guard | Medium | Small |
| Fix config string deep copy | Medium | Small |
| Fix mouse `last_buttons` leak | Medium | Small |
| Remove `/wd4244` suppression, fix resulting warnings | High | Medium |

**Why:** Code duplication is the single largest structural risk. Every future sprint pays a tax for maintaining two copies. Fixing this now reduces ongoing cost.

### Option B: "Serialization Sprint" (complete state round-trip)

Focus: make save/load actually preserve complete machine state.

| Task | Priority | Effort |
|------|----------|--------|
| Serialize VGA register state | High | Medium |
| Serialize mixer/audio state | High | Medium |
| Serialize DMA channel state | High | Medium |
| Serialize DOS kernel state | High | Medium |
| Fix keyboard buffer truncation (96 entries) | High | Small |
| Complete PIC serialization (all fields) | High | Small |
| Add endianness handling | High | Medium |
| Fix alignment on load (use memcpy) | Medium | Small |
| Add forward-compatible version check | Medium | Small |
| Expand determinism tests for long runs + graphics modes | Medium | Medium |

**Why:** The roadmap lists Sprint 4 as "Deterministic Replay as Product." Deterministic replay is broken if save/load loses half the machine state. This sprint is a prerequisite.

### Option C: "CI & Testing Sprint" (raise confidence)

Focus: fill testing gaps, add fuzzing/spec verification to CI, get coverage numbers.

| Task | Priority | Effort |
|------|----------|--------|
| Add fuzz CI job (60-second smoke runs) | High | Small |
| Add TLA+ model checking to CI | High | Small |
| Add code coverage reporting | Medium | Medium |
| Add TSan job | Medium | Small |
| Add MSan job | Medium | Small |
| Add PIC/PIT/Scheduler C++ unit tests | Medium | Medium |
| Expand clang-tidy scope | Medium | Small |
| Add input injection fuzzer | Medium | Medium |
| Add actual DOS program test | Medium | Medium |
| Add long-running determinism soak test | Medium | Medium |

**Why:** Adding automated fuzzing, spec verification, and coverage would catch bugs before they ship.

### Recommended: Option A first, then B

The duplication tax compounds. Every week on top of 38+ duplicate files increases drift risk and doubles review burden. Option A makes everything else cheaper.

After consolidation, Option B (serialization) unblocks Sprint 4 (Deterministic Replay) from the existing roadmap.

Option C tasks are individually small and can be sprinkled into either sprint.
