# Project Legends Codebase Audit

Date: 2026-02-24
Scope: Full repository audit across 5 dimensions
Previous audit: 2026-02-21

---

## Current State

Project Legends is an embeddable x86 emulation framework built on a refactored DOSBox-X engine. Three sprints are complete plus significant cross-cutting work:
- Sprint 1: Library foundation (C API, error model, handle system)
- Sprint 2: Instance reality (global-to-context migration, 87% complete)
- Sprint 3: Module graph (DAG enforcement, build boundaries)
- Cross-cutting: CPU bridge wired, serialization expanded to V4, CI hardened, context unification

~1.2M lines of vendored DOSBox-X engine code, ~24.5K lines of new wrapper code. C API surface is complete (22 functions, all implemented). CI covers 3 platforms with 4 sanitizers, fuzzing, TLA+ model checking, and code coverage.

**Highlight:** Phase 0 (quick wins), Phase A (CPU bridge), Phase C (context unification), and Phase D (CI hardening) are largely complete. Phase B (serialization) is ~60% done. Phase E (determinism at scale) is blocked on Phase B completion. A parallel static audit surfaced 11 additional findings (H5-H9, M6-M8, L6-L8), now incorporated. Total: 2C + 9H + 11M + 8L = 30 findings. All findings translated to 50 EARS requirements; all 11 CI-checked TLA+ specs reviewed invariant-by-invariant (49 invariants: 33 conformant, 11 partial, 5 non-conformant).

---

## Resolved Since Last Audit (2026-02-21)

| Old ID | Finding | Resolution | Evidence |
|--------|---------|------------|----------|
| C2 | CPU bridge is a stub | Bridge now calls `(*cpudecoder)()` with real cycle management | `engine/src/misc/cpu_bridge.cpp:89` |
| C3 | gsl-lite version mismatch (v1.0.0 vs v0.41.0) | Both root and engine specify v1.0.0 | `CMakeLists.txt:124`, `engine/CMakeLists.txt:239` |
| H2 | No endianness handling in serialization | Wire format helpers with portable LE encoding | `engine/include/dosbox/wire_format.h` |
| H3 | Missing security hardening flags | Stack protectors, FORTIFY_SOURCE, PIE, CFG all enabled | `CMakeLists.txt:112-118` |
| H4 | Engine-wide `/wd4244` suppression | Removed; only `/wd4100` (unused params) remains | `engine/CMakeLists.txt` |
| H6 | Broken CMake package export | `LegendsTargets.cmake` now generated | `cmake/LegendsConfig.cmake.in` |
| H7 | No fuzzing in CI | 3 fuzz targets run 60s smoke under ASan | `.github/workflows/ci.yml:237-287` |
| H8 | No TLA+ verification in CI | 11 specs model-checked in CI | `.github/workflows/ci.yml:291-373` |
| M3 | `dosbox_lib_destroy()` has no thread check | Thread affinity now enforced via `LIB_CHECK_THREAD()` | `engine/src/misc/dosbox_library.cpp:295` |
| M5 | Static `last_buttons` leaks across instances | Wrapped in `HeadlessState` struct with `reset()` | `engine/src/aibox/headless_stub.cpp` |
| M9 | Sprint 3 phases 2/4/5/6 unimplemented | Module DAG enforcement complete | `cmake/ModuleDAG.cmake` |
| M10 | headless_stub.cpp 7 process-global variables | Wrapped in `HeadlessState` struct | `engine/src/aibox/headless_stub.cpp` |
| M11 | No code coverage reporting in CI | lcov coverage job with artifact upload | `.github/workflows/ci.yml:378-431` |
| M12 | No MSan or TSan CI jobs | 4-sanitizer matrix: ASan, UBSan, TSan, MSan | `.github/workflows/ci.yml:114-161` |
| L2 | README says SaveStateHeader is 96 bytes | Fixed to 64 bytes matching `static_assert` | `README.md` |

> **Cross-audit note:** Findings H5-H9, M6-M8, and L6-L8 were identified by a parallel static audit (Feb 24 2026) and verified against source before incorporation. Finding M9 was un-resolved after verification showed `strdup()` is not used (shallow struct copy remains). Findings M10-M11 were identified during cross-audit verification.

---

## Prior-Finding Resolution Status (verified 2026-06-10)

This section annotates the 30 findings below without deleting or rewriting the
original audit text. Statuses are based on the 2026-06-09 backlog-miner report
in `audit-wiki/raw/backlog-miner-report.md`, spot-checked against source at the
Sprint 1 base. Tally: **22 resolved / 8 open**. `C2` is resolved for the
missing-call finding; execution conformance remains partial because the linked
PIC implementation still includes stub behavior.

| ID | Resolution status | Current evidence / note |
|----|-------------------|-------------------------|
| C1 | RESOLVED | Public overlapping headers are forwarding headers; implementation lives in the engine tree. |
| C2 | RESOLVED | `engine/src/misc/cpu_bridge.cpp` calls `PIC_RunQueue()` and `CPU_Check_NMI()`; PIC functional delivery remains partial. |
| H1 | RESOLVED | V5 engine state serializes CPU GPRs and zero-RLE RAM/VRAM; event scheduler serialization remains a separate partial. |
| H2 | OPEN | Two engine-layer `g_current_context` thread-local pointers remain. |
| H3 | OPEN | `MachineContext::step()` remains a deprecated counter stub. |
| H4 | RESOLVED (reclassified) | Seven `init_*` no-ops are documented as intentional DOSBox-X bridge delegation; related phantom types remain tracked under M5. |
| H5 | RESOLVED | `legends_destroy()` now strict-matches the active handle; invalid non-null handles do not destroy the instance. |
| H6 | RESOLVED | Memory read/write bounds checks use subtraction form to avoid wraparound. |
| H7 | OPEN | `HashMode::Full` now hashes memory, but VGA/device hashing remains outside the documented contract. |
| H8 | RESOLVED | Frame/text capture syncs from engine state with synthetic data only as fallback. |
| H9 | RESOLVED | Save/load caller-buffer parsing uses byte helpers rather than unaligned struct casts. |
| M1 | RESOLVED | Mutating APIs now check the in-step reentrancy guard. |
| M2 | RESOLVED | `legends_text_input()` reserves all queue slots for a character before enqueueing. |
| M3 | RESOLVED | Mixer ring producer/consumer indices are atomic. |
| M4 | OPEN | Registry coverage improved, but mutable legacy externs remain outside the registry. |
| M5 | OPEN | Forward-declared subsystem classes still have no definitions. |
| M6 | RESOLVED | Log callback invocation is wrapped against exceptions. |
| M7 | RESOLVED | `dosbox_lib_get_context_ptr()` now validates thread affinity. |
| M8 | RESOLVED | Engine handles validate against the sentinel value, not just non-null. |
| M9 | RESOLVED | Config string fields are deep-copied in the engine and legends layers. |
| M10 | OPEN | Deprecated `dosbox_step()` still routes through the counter-stub path. |
| M11 | RESOLVED | `legends_step_cycles()` checks `dosbox_lib_get_context_ptr()` before using the context pointer. |
| L1 | OPEN | README API coverage is stale relative to the current `legends_embed.h` surface. |
| L2 | RESOLVED | Previously unused error codes are now returned by real paths. |
| L3 | OPEN | `HandleRegistry` remains unused by production embed API code. |
| L4 | RESOLVED | The `LEGENDS_ERROR` macro collision was removed. |
| L5 | RESOLVED | `project_legends` has a real `src/main.cpp` and executable target. |
| L6 | RESOLVED | `check_gsl_lite_usage.py` excludes generated/vendor directories. |
| L7 | RESOLVED | `requirements-dev.txt` declares PyYAML. |
| L8 | RESOLVED | Invalid-handle destroy sentinel tests no longer expect success. |

---

## Top Findings by Severity

### Critical

| # | Finding |
|---|---------|
| C1 | **Massive code duplication** — 27+ header pairs between `include/legends/` and `engine/include/aibox/` with overlapping names. Same structural patterns compiled into separate static libraries. Bug fixes risk manual replication. *(CARRIED from old C1)* |
| C2 | **CPU bridge skips PIC_RunQueue / CPU_Check_NMI** — `cpu_bridge.cpp` now calls `(*cpudecoder)()` for real x86 execution, but does not call `PIC_RunQueue()` before decoding or `CPU_Check_NMI()` in the loop. Timer/interrupt-driven code (BIOS tick, keyboard IRQ) may not fire during bridge-controlled execution. *(NEW — old C2 was "stub"; now it's "incomplete execution path")* |

### High

| # | Finding |
|---|---------|
| H1 | **Serialization gaps** — V4 format covers 8 subsystems (680 bytes) but CPU GPRs (EAX-EDI, segment registers), full VGA hardware state (~20KB opaque pointer), and RAM contents are not serialized. Save/load preserves config-level state but not instruction-level CPU register state or video memory. *(UPDATED from old H1 — was 5 subsystems, now 8, but register/RAM gaps remain)* |
| H2 | **Two unsynchronized `g_current_context` globals** — aibox and dosbox layers each maintain a `thread_local MachineContext*` / `DOSBoxContext*`. Phase C added a `dosbox::ContextGuard` in `legends_step_cycles()`, eliminating the legends-layer pointer, but the two engine-layer pointers remain independently managed. Cross-layer calls during non-step contexts may see stale pointers. *(NARROWED from old H5 — was 3, now 2)* |
| H3 | **MachineContext.step() is a TODO stub** — `engine/src/aibox/machine_context.cpp:226` contains `// TODO: Actual emulation would go here`. Real execution flows through `cpu_bridge.cpp`, making this the canonical dead path. *(ELEVATED from old M3)* |
| H4 | **7 MachineContext init_\* methods are stubs** — `init_pic`, `init_pit`, `init_vga`, `init_input`, `init_sound`, `init_dos`, `init_bios` all return `Ok()` immediately. Only `init_memory`, `init_cpu`, and `init_dma` have real implementations. Subsystem initialization is delegated entirely to the DOSBox-X engine bridge. *(CARRIED from old M3 — was 8 stubs, now 7; init_dma implemented)* |
| H5 | **`legends_destroy()` fallback destroys active instance on any non-null handle** — `get_instance()` failure falls back to `g_active_instance` (line 953), so passing any invalid non-null handle destroys the real active instance instead of returning an error. `legends_embed_api.cpp:949-957` *(cross-audit)* |
| H6 | **Integer overflow in memory bounds checks** — `address + size` can wrap around in `dosbox_lib_read_memory`/`dosbox_lib_write_memory`, bypassing bounds validation. `dosbox_library.cpp:1277,1301` *(cross-audit)* |
| H7 | **`HashMode::Full` contract mismatch** — header documents memory/VGA/device hashing but implementation only appends `"FULL_MODE"` marker string. `state_hash.h:41-43`, `state_hash.cpp:296-301` *(cross-audit)* |
| H8 | **Frame capture decoupled from engine** — `frame_state` initialized with synthetic test pattern, `sync_state_from_engine()` syncs timing/PIC only, not framebuffer. `legends_embed_api.cpp:919-920,1498` *(cross-audit)* |
| H9 | **Legends-layer save/load uses unaligned `reinterpret_cast` on caller-provided buffers** — UB on strict-alignment architectures. `legends_embed_api.cpp:1657,1668,2058,2122` *(cross-audit)* |

### Medium

| # | Finding |
|---|---------|
| M1 | **Reentrancy guard enforced for step functions but not all re-entrant paths** — `legends_step_cycles()` checks `inst->in_step` and returns `LEGENDS_ERR_REENTRANT_CALL` (line 1053), but other API functions callable from engine callbacks (e.g., through the log callback chain) do not have equivalent guards. *(NARROWED from old M1 — step reentrancy is enforced)* |
| M2 | **`legends_text_input` partial commit on queue-full** — If the input queue fills mid-character (after shift-down but before key press), the shift key gets stuck down. No rollback mechanism. *(CARRIED from old M2)* |
| M3 | **MixerState callback thread access unsynchronized** — `MixerState` has thread safety comments but no actual synchronization primitives. Audio callback thread can race with main thread. *(CARRIED from old M7)* |
| M4 | **Untracked legacy extern globals** — 30-40 mutable extern globals in `engine/include/` (`callback.h`, `bios.h`, `bios_disk.h`, `cpu.h`, `dos_inc.h`) are not tracked in the migration registry. CI now tracks a known set via `sprint2-checks.yml`. *(NARROWED from old M8)* |
| M5 | **7 forward-declared classes with no definitions** — `VgaContext`, `DosKernel`, `PicController`, `PitTimer`, `KeyboardController`, `MouseController`, `SoundSubsystem` are forward-declared in `engine/include/aibox/machine_context.h` but have no definitions anywhere. These correspond to the 7 stub init methods (H4). *(NEW)* |
| M6 | **Callback invocation not exception-safe at C ABI boundary** — `log()` in `instance_state.h:51` called unguarded from `extern "C"` functions (e.g. `legends_destroy` line 962). If the callback throws, stack unwinding across the C ABI boundary is undefined behavior. `instance_state.h:49-51`, `legends_embed_api.cpp:962` *(cross-audit)* |
| M7 | **`dosbox_lib_get_context_ptr()` bypasses `LIB_CHECK_THREAD()`** — every other context/state API function checks thread affinity, this one doesn't. `dosbox_library.cpp:466-476` *(cross-audit)* |
| M8 | **Engine handle validation is null-only** — handle created as sentinel `(void*)1` but validation only checks `!= nullptr`, so any non-null pointer passes validation. `dosbox_library.cpp:240,255,359` *(cross-audit)* |
| M9 | **Config string dangling pointers not fixed** — `dosbox_lib_create()` shallow-copies the config struct (`g_config = *config`, line 213). `config_path` and `working_dir` are `const char*` fields — if the caller frees the backing strings after create, the library holds dangling pointers. Previously claimed resolved via `strdup()` but no `strdup` calls exist. `dosbox_library.cpp:213`, `dosbox_library.h:106-107` *(UN-RESOLVED — old M4 resolution was incorrect)* |
| M10 | **Dual runtime path divergence** — legacy `dosbox_step()` routes through `MachineContext::step()` (TODO stub, line 226), while `dosbox_lib_step_cycles()` uses the real CPU bridge via `dosbox::execute_cycles()` (line 371). Two execution paths with completely different behavior coexist. `dosbox_context.cpp:895,920`, `dosbox_library.cpp:371`, `machine_context.cpp:226` *(NEW)* |
| M11 | **`legends_step_cycles()` ignores `dosbox_lib_get_context_ptr()` return value** — the return value is discarded (line 1065) and the resulting `raw_ctx` pointer is dereferenced unconditionally via `static_cast` (line 1067). If the call fails, this is a null pointer dereference. `legends_embed_api.cpp:1065,1067` *(NEW)* |

### Low

| # | Finding |
|---|---------|
| L1 | **README documents ~18 of 22 API functions** — Coverage improved from 15/22 (Phase 0 added 7) but some function descriptions remain brief or missing detail. *(UPDATED from old L1)* |
| L2 | **Three error codes defined but never used** — `LEGENDS_ERR_REENTRANT_CALL` (-5), `LEGENDS_ERR_IO_FAILED` (-10), `LEGENDS_ERR_NOT_SUPPORTED` (-12). *(CARRIED from old L3)* |
| L3 | **HandleRegistry fully implemented but unused** — Embed API uses raw pointer comparison instead. Dead code until API unification. *(CARRIED from old L4)* |
| L4 | **`LEGENDS_ERROR` macro collision** — `error.h` defines it one way; `legends_embed_api.cpp` undefs and redefines it differently. *(CARRIED from old L5)* |
| L5 | **`project_legends` executable target unbuildable** — `src/main.cpp` and `external/SDL2/` don't exist. Hardcoded `mingw32` link. Gated behind `PAL_BACKEND_SDL2` so headless builds are unaffected. *(CARRIED from build section)* |
| L6 | **`check_gsl_lite_usage.py` reports false positives from `_deps` trees** — exclusion list misses `build_test` and other generated dirs. `scripts/check_gsl_lite_usage.py:207` *(cross-audit)* |
| L7 | **YAML-gated scripts require undeclared `pyyaml`** — no `requirements-dev.txt`; CI installs it but local runs fail. `scripts/check_migration_status.py:20`, `sprint2-checks.yml:38` *(cross-audit)* |
| L8 | **Test suite uses sentinel invalid-handle destroy pattern** — masks H5 permissive behavior by passing `(void*)0xDEAD` and expecting success. `tests/unit/test_legends_embed.cpp:23` *(cross-audit)* |

---

## What Works Well

- **C API** — 22 functions, all real implementations, well-validated with null checks, bounds validation, thread affinity, and consistent error codes
- **Save/load V4 format** — 8 subsystems, 680 bytes, CRC32 integrity, section bounds checking, four-phase atomic load, V3 backward compatibility
- **Wire format** — Portable little-endian encoding via `wire_format.h`, eliminates cross-platform serialization bugs
- **Module DAG enforcement** — `legends_core` -> `aibox_core`, `legends_pal` -> nothing; CI-enforced via `module-dag.yml`
- **CI pipeline** — 3 platforms (Linux/Windows/macOS), 4 sanitizers (ASan/UBSan/TSan/MSan), 3 fuzz targets, 11 TLA+ model checks, code coverage
- **Compat shim containment** — `current_context()` usage properly confined to 6 compat shim files (33 calls)
- **Python verification scripts** — Clean, well-documented, CI-integrated tooling
- **PAL abstraction** — Clean interface segregation with proper backend isolation
- **Real CPU execution via cpu_bridge** — `(*cpudecoder)()` called with proper cycle budget management and callback dispatch
- **Determinism tests** — Prove input-to-engine coupling and save/load compose with determinism
- **gsl-lite contract enforcement** — v1.0.0 everywhere, PRIVATE linkage, usage checked by script
- **Security hardening** — Stack protectors, FORTIFY_SOURCE, PIE, Control Flow Guard on MSVC

---

## 1. Public API & Implementation

### Files Examined

- `include/legends/legends_embed.h` (stable C ABI surface)
- `include/legends/handle_registry.h`
- `include/legends/machine_context.h`
- `include/pal/*.h` (all PAL interface headers)
- `src/legends/legends_embed_api.cpp` (2459 lines)

### API Completeness

All 22 declared functions are implemented. No stubs remain. The "Phase 4+: stubs" comment at line 8 of the implementation is stale but harmless.

### Safety

Consistently applied. Every handle-taking function validates via `get_instance()` and checks output pointers with `LEGENDS_REQUIRE`. Save/load uses four-phase atomic load pattern. Bounds checking uses `SAFE_MULTIPLY_OR_ERROR`, `VALIDATE_SECTION_BOUNDS`, `VALIDATE_DATA_BOUNDS`, `VALIDATE_COUNT_MAX` macros.

### Improvements Since Last Audit

- Reentrancy guard struct added (RAII pattern in `legends_step_ms` / `legends_step_cycles`) — enforced via `in_step` flag
- HeadlessState struct wraps 7 former process-global variables with `reset()` on destroy
- README updated with 7 previously undocumented functions

### Current Findings

**M1: Reentrancy guard enforced for step functions, not all paths.** `legends_step_cycles()` enforces reentrancy via `in_step` flag (line 1053), but other API functions callable from engine callbacks lack equivalent guards.

**M2: `legends_text_input` partial commit on queue-full.** If the input queue fills mid-character (after shift-down but before key press), the shift key gets stuck down. No rollback.

**L1: README API documentation gaps.** Most functions documented but some descriptions remain brief.

**L2: Three error codes defined but never used:** `REENTRANT_CALL` (-5), `IO_FAILED` (-10), `NOT_SUPPORTED` (-12).

**L3: HandleRegistry fully implemented but unused.** Embed API uses raw pointer comparison.

**L4: `LEGENDS_ERROR` macro collision.** `error.h` defines it one way; `legends_embed_api.cpp` undefs and redefines it differently.

**H5: `legends_destroy()` fallback destroys active instance on any non-null handle.** `get_instance()` failure falls back to `g_active_instance` (line 953), meaning any invalid non-null handle silently destroys the real instance.

**H8: Frame capture decoupled from engine.** `frame_state` initialized with synthetic test pattern; `sync_state_from_engine()` syncs timing/PIC only, not the actual framebuffer.

**H9: Unaligned `reinterpret_cast` on caller-provided buffers in save/load.** UB on strict-alignment architectures (ARM, SPARC).

**M6: Callback invocation not exception-safe at C ABI boundary.** `log()` callback in `instance_state.h:51` called unguarded from `extern "C"` functions — stack unwinding across the C boundary is UB.

**M11: `legends_step_cycles()` ignores `dosbox_lib_get_context_ptr()` return value.** Line 1065 discards the error code; line 1067 dereferences the resulting pointer unconditionally. Null dereference if the call fails.

**L8: Test suite uses sentinel invalid-handle destroy pattern.** `test_legends_embed.cpp:23` passes `(void*)0xDEAD` to destroy and expects success, masking H5's permissive behavior.

---

## 2. Engine Bridge Layer

### Files Examined

- `engine/include/dosbox/dosbox_library.h`
- `engine/include/dosbox/dosbox_context.h`
- `engine/include/dosbox/engine_state.h`
- `engine/include/dosbox/engine_services.h`
- `engine/include/dosbox/cpu_bridge.h`
- `engine/include/dosbox/wire_format.h`
- `engine/src/misc/dosbox_library.cpp`
- `engine/src/misc/cpu_bridge.cpp`

### CPU Bridge — Real Execution with Gaps

`cpu_bridge.cpp` now executes real x86 instructions via `(*cpudecoder)()` (line 89). The bridge:
- Initializes the CPU decoder in `init_cpu_bridge()` (lines 33-44)
- Manages cycle budgets via `CPU_Cycles` / `CPU_CycleLeft` (lines 86-87)
- Handles return codes: `CBRET_STOP`, callbacks, HLT state (lines 91-96)
- Syncs context timing after execution (line 116)
- Provides millisecond-based wrapper via `execute_ms()` (lines 121-133)

**Finding C2:** The bridge does NOT call `PIC_RunQueue()` before `(*cpudecoder)()` or `CPU_Check_NMI()` in the execution loop. In the original DOSBox-X `Normal_Loop()`, `PIC_RunQueue()` fires pending timer/interrupt events and `CPU_Check_NMI()` checks for non-maskable interrupts. Without these calls, timer ticks, keyboard IRQs, and other PIC-driven events may not fire during bridge-controlled execution.

### State Serialization — V4 Format

| Subsystem | Bytes | Status | Notes |
|-----------|-------|--------|-------|
| Header | 48 | Complete | Magic, version, CRC32, section count |
| Timing | 40 | Complete | Full coverage |
| PIC | 72 | **Complete** | Full 18-field controller state (both controllers) |
| Keyboard | 264 | Complete | Full 96-entry buffer (fixed from old 16-entry truncation) |
| CPU | 96 | **Partial** | Cycle counters, NMI state — but no GPRs (EAX-EDI, segments) |
| Memory | 72 | Complete | Page config, A20 gate |
| Mixer (V4) | 36 | **New** | Freq, blocksize, volumes, flags |
| VGA (V4) | 32 | **New** | Width, height, mode, refresh — but not ~20KB hardware state |
| DOS (V4) | 20 | **New** | Kernel state, PSP, DTA, drive, codepage |
| **Total** | **680** | | V3 backward compat at 544 bytes |

**Finding H1:** CPU GPRs (EAX-EDI, segment registers), full VGA hardware state (~20KB opaque `VGA_Type_t*`), and RAM contents are not serialized. Config-level determinism is preserved but instruction-level state is not.

Wire format (`wire_format.h`) provides portable little-endian encoding, eliminating the old endianness bug (resolved H2).

### Library-Layer State

Improved since last audit:
- `g_time_state` eliminated — timing flows through `g_config.cpu_cycles` and inline `cycles_per_ms()`
- `g_cycles_per_ms` global eliminated — replaced by inline function
- HeadlessState struct wraps former globals (resolved M5, M10)

Remaining: `g_instance_exists`, `g_owner_thread_id`, `g_context`, `g_config`, `g_last_error`, `g_log_state` — these are architectural singletons, acceptable for single-instance design.

### Context Pointers

**Finding H2:** Two `g_current_context` thread-locals remain:
1. `engine/src/aibox/machine_context.cpp:20` — `thread_local MachineContext*`
2. `engine/src/misc/dosbox_context.cpp` — `thread_local DOSBoxContext*`

Phase C added `dosbox::ContextGuard` in `legends_step_cycles()` so both pointers are set during step scope. The legends-layer pointer was eliminated. Down from 3 to 2.

### Additional Engine-Layer Findings

**H6: Integer overflow in memory bounds checks.** `dosbox_lib_read_memory` (line 1277) and `dosbox_lib_write_memory` (line 1301) compute `address + size` which can wrap around on 32-bit, bypassing bounds validation. Should use subtraction form (`size > max - address`).

**H7: `HashMode::Full` contract mismatch.** `state_hash.h:41-43` documents memory/VGA/device hashing for `HashMode::Full`, but `state_hash.cpp:296-301` only appends the literal string `"FULL_MODE"` — no actual memory or device state is hashed.

**M7: `dosbox_lib_get_context_ptr()` bypasses `LIB_CHECK_THREAD()`.** Every other context/state API function in `dosbox_library.cpp` checks thread affinity via `LIB_CHECK_THREAD()`, but `dosbox_lib_get_context_ptr()` (lines 466-476) skips this check.

**M8: Engine handle validation is null-only.** The library handle is created as sentinel `(void*)1` (line 240) but validation (lines 255, 359) only checks `!= nullptr`. Any non-null pointer passes, risking silent misuse.

**M9: Config string dangling pointers not fixed.** `dosbox_lib_create()` shallow-copies the config struct (`g_config = *config`, line 213). The `config_path` and `working_dir` fields are `const char*` — if the caller frees the backing strings after create, the library holds dangling pointers. Previously claimed resolved via `strdup()` but no `strdup` calls exist in `dosbox_library.cpp`.

**M10: Dual runtime path divergence.** Legacy `dosbox_step()` (`dosbox_context.cpp:920`) routes through `MachineContext::step()` (the TODO stub at `machine_context.cpp:226`), while `dosbox_lib_step_cycles()` (`dosbox_library.cpp:371`) uses the real CPU bridge. These two paths have completely different behavior — one is a no-op counter, the other executes real x86 instructions. If any code path still calls `dosbox_step()`, it silently does nothing useful.

---

## 3. Tests, TLA+ Specifications, and CI/CD

### Test Coverage

| Category | Count |
|----------|-------|
| Unit tests | 61 |
| Integration tests | 10 |
| Toolchain tests | 1 |
| Fuzz targets | 3 |
| **Total** | **75** |

All 22 public API functions have test coverage. Tests exercise real DOSBox-X engine behavior through the headless backend.

### Test Gaps

| Area | Gap |
|------|-----|
| DOS program execution | No test loads/runs an actual COM/EXE binary |
| Long-running determinism | All tests run <200K cycles |
| Graphics mode determinism | All tests use default text mode |
| Multi-process determinism | All tests single-process |
| PIC/PIT device models | TLA+ specs exist but no C++ unit tests |

### TLA+ Specifications

33 total TLA+ specs in `spec/tla/`. 11 model-checked in CI:

| Spec | In CI |
|------|-------|
| LifecycleMinimal | Yes |
| PALMinimal | Yes |
| ThreadingMinimal | Yes |
| SaveStateTest | Yes |
| DeterminismMinimal | Yes |
| CaptureMinimal | Yes |
| InputMinimal | Yes |
| ReentrancyMinimal | Yes |
| ErrorModel | Yes |
| ConfigValidation | Yes |
| APIContract | Yes |

Up from 4 specs in CI at last audit. Remaining 22 specs are documentation/reference only.

### CI/CD Pipeline

4 workflow files, 11+ jobs:

| Job | Workflow | Status |
|-----|----------|--------|
| Linux (GCC/Clang) | ci.yml | Active |
| Windows (MSVC) | ci.yml | Active |
| macOS (AppleClang) | ci.yml | Active |
| Sanitizers (ASan/UBSan/TSan/MSan) | ci.yml | **4 jobs** |
| ABI check | ci.yml | Active |
| Static analysis (clang-tidy) | ci.yml | Active |
| Fuzz (3 targets, 60s smoke) | ci.yml | **New** |
| TLA+ (11 model checks) | ci.yml | **New** |
| Coverage (lcov) | ci.yml | **New** |
| PAL backend tests | pal-ci.yml | Active |
| Module DAG verification | module-dag.yml | Active |
| Sprint 2 checks | sprint2-checks.yml | Active |

### Fuzzing

3 fuzz targets in CI:
- `fuzz_engine_load_state.cpp` — engine-layer state deserialization
- `fuzz_legends_load_state.cpp` — legends-layer state deserialization
- `fuzz_input_injection.cpp` — key/mouse event injection (**New**)

Missing: differential fuzzing for determinism, long-running continuous fuzzing.

---

## 4. Build System and Code Quality

### Resolved Build Issues

- **gsl-lite: FIXED** — Both root and engine specify v1.0.0, PRIVATE linkage, usage checked by `check_gsl_lite_usage.py`
- **Security hardening: FIXED** — `-fstack-protector-strong`, `-D_FORTIFY_SOURCE=2`, `-fPIE`, `-pie` (GNU/Clang); `/GUARD:CF` (MSVC)
- **CMake export: FIXED** — `LegendsTargets.cmake` properly generated
- **Warning suppression: IMPROVED** — Only `/wd4100` (unused parameters) remains, acceptable for vendored engine code

### Code Duplication — Still Critical

**Finding C1:** 27+ header pairs between `include/legends/` and `engine/include/aibox/` share overlapping names and structural patterns. While some are forwarding headers, the dual static library compilation remains. Both `legends_core` and `aibox_core` link into the final library. This is the single largest structural risk: bug fixes risk manual replication, review burden is doubled, and namespace divergence accumulates over time.

Duplicated header pairs include: `builder`, `callback_registry`, `cpu_context`, `dma`, `enums`, `error`, `event_bus`, `events`, `exceptions`, `function_ref`, `handle_registry`, `headless_stub`, `io_port`, `llm_actions`, `llm_diff`, `llm_frame`, `llm_serializer`, `machine_context`, `memory`, `optional_utils`, `safe_arithmetic`, `vision_annotations`, `vision_capture`, `vision_framebuffer`, `vision_overlay`, and more.

### Forward-Declared Classes

**Finding M5:** 7 classes forward-declared in `engine/include/aibox/machine_context.h` with no definitions anywhere:
- `VgaContext`, `DosKernel`, `PicController`, `PitTimer`, `KeyboardController`, `MouseController`, `SoundSubsystem`

These correspond directly to the 7 stub init methods (H4).

### Remaining Build Issues

**L5: `project_legends` executable target unbuildable.** `src/main.cpp` and `external/SDL2/` don't exist. Gated behind `PAL_BACKEND_SDL2`.

**L6: `check_gsl_lite_usage.py` reports false positives from `_deps` trees.** The exclusion list at line 207 misses `build_test` and other generated directories, causing spurious failures on local builds with non-standard build dirs.

**L7: YAML-gated scripts require undeclared `pyyaml`.** `check_migration_status.py` imports `yaml` (line 20) and `sprint2-checks.yml` installs it (line 38), but there is no `requirements-dev.txt`. Local runs fail with `ModuleNotFoundError`.

### TODO Inventory

| File | Line | Content | Severity |
|------|------|---------|----------|
| `machine_context.cpp` | 226 | "Actual emulation would go here" | High (H3) |
| `machine_context.cpp` | 374-413 | 7 init_* stubs (PIC/PIT/VGA/input/sound/DOS/BIOS) | High (H4) |
| `cpu_context.h` | 521 | "Add paging translation" | Medium |
| `cpu_context.h` | 534 | "Check stack segment B bit" | Low |

---

## 5. Global State Migration and AIBox Layer

### Migration Progress

| Category | Count | % |
|----------|-------|---|
| Migrated | 61 | 87% |
| Deferred | 9 | 13% |
| **Total tracked** | **70** | |

Unchanged from last audit. The 9 deferred globals are architectural (7 SDL/display dead in headless, 1 core-local transient, 1 global log callback). `sprint2-checks.yml` tracks the known set.

### Context Unification — Phase C Complete

Phase C work completed:
- `dosbox::ContextGuard` added to `legends_step_cycles()` — both TLS pointers set during step
- `g_cycles_per_ms` eliminated — single timing source via `cycles_per_ms()` inline
- CPU globals sync convention documented in `cpu_bridge.h` with debug assertions

**Finding H2:** Two `g_current_context` pointers remain (aibox + dosbox layers). These are set during step scope but not during non-step API calls. Merging `MachineContext` and `DOSBoxContext` would be too invasive; the current dual-guard approach is a pragmatic compromise.

### current_context() Usage

All production usage properly contained to 6 compat shim files (33 total calls). No calls in headers. Test code has ~90 calls (legitimate fixture setup).

### AIBox Layer

The aibox layer remains the DOSBox-X-side API in `engine/`. It provides LLM integration (batch actions, token-efficient frames), vision model support (capture, annotations), and event bus subscription. `dosboxx_embed_api.cpp` was deleted in Phase 0 (resolved dead code).

---

## 6. Implementation Requirements (EARS Notation)

All 30 findings plus TLA+ specification requirements translated to [EARS notation](https://www.jamasoftware.com/requirements-management-guide/writing-requirements/adopting-the-ears-notation-to-improve-requirements-engineering/). Patterns: **U**biquitous ("shall"), **E**vent-driven ("When…shall"), **S**tate-driven ("While…shall"), **X** Unwanted ("If…then shall"), **C**omplex ("While…when…shall").

### LC — Lifecycle

| ID | Pat | Requirement | Source | Status |
|----|-----|-------------|--------|--------|
| REQ-LC-001 | U | The system shall enforce that at most one instance exists per process | LifecycleMinimal:`AtMostOneInstance` | **OK** |
| REQ-LC-002 | E | When `legends_create()` is called with valid config and no instance exists, the system shall return a non-null handle | LifecycleMinimal:`MisuseSafe` | **OK** |
| REQ-LC-003 | X | If `legends_destroy()` receives a non-null handle not matching the active instance, then the system shall return an error without destroying the active instance | H5, LifecycleMinimal:`HandleConsistency` | **GAP** |
| REQ-LC-004 | E | When `legends_destroy()` is called with a null handle, the system shall return OK without side effects | ErrorModel:`ResolveError` | **OK** |
| REQ-LC-005 | U | The system shall route all step execution through the CPU bridge; no alternative stub path shall exist | M10, H3 | **GAP** |
| REQ-LC-006 | U | The system shall provide definitions for all forward-declared classes in public/internal headers | M5 | **GAP** |

### EX — Execution

| ID | Pat | Requirement | Source | Status |
|----|-----|-------------|--------|--------|
| REQ-EX-001 | C | While the CPU bridge is executing, when `(*cpudecoder)()` is about to be called, the system shall call `PIC_RunQueue()` | C2, PIC.tla:`PriorityRespected` | **GAP** |
| REQ-EX-002 | C | While the CPU bridge is executing, when the decoder returns, the system shall call `CPU_Check_NMI()` | C2 | **GAP** |
| REQ-EX-003 | X | If step is called while a step is in progress, then the system shall return `REENTRANT_CALL` | ReentrancyMinimal:`NoNestedStep` | **OK** |
| REQ-EX-004 | X | If any API function is called from an engine callback during step, then the system shall return an error without modifying state | M1, ReentrancyMinimal:`CallbackSafe` | **PARTIAL** |
| REQ-EX-005 | E | When a step function is called, the system shall drain all pending input events before executing cycles | InputMinimal:`InputDeterminism` | **OK** |
| REQ-EX-006 | X | If `dosbox_lib_get_context_ptr()` returns an error, then `legends_step_cycles()` shall propagate the error without dereferencing | M11 | **GAP** |

### SR — Serialization

| ID | Pat | Requirement | Source | Status |
|----|-----|-------------|--------|--------|
| REQ-SR-001 | E | When state is saved then loaded, the system shall restore observable state: `Obs(Deserialize(Serialize(S))) = Obs(S)` | SaveStateTest:`ObservationPreserved` | **PARTIAL** |
| REQ-SR-002 | E | When `legends_save_state()` is called, the system shall serialize CPU GPRs (EAX-EDI), segment registers, and EIP | H1 | **GAP** |
| REQ-SR-003 | E | When `legends_save_state()` is called, the system shall serialize full VGA hardware state and video memory | H1 | **GAP** |
| REQ-SR-004 | E | When `legends_save_state()` is called, the system shall serialize guest RAM contents | H1 | **GAP** |
| REQ-SR-005 | E | When `legends_save_state()` is called, the system shall serialize the event queue (deadline, kind, tieKey) | SaveStateTest:`EventCountPreserved` | **PARTIAL** |
| REQ-SR-006 | X | If a loaded state buffer has a CRC32 mismatch, then the system shall reject the load without modifying state | SaveStateTest:`CorruptionDetected` | **OK** |
| REQ-SR-007 | U | The system shall use `memcpy` (not `reinterpret_cast`) for deserialization from caller-provided buffers | H9 | **GAP** |
| REQ-SR-008 | U | The system shall implement load as an atomic operation: all state restored or none modified | SaveStateTest:`PartialSaveSafe` | **OK** |

### DT — Determinism

| ID | Pat | Requirement | Source | Status |
|----|-----|-------------|--------|--------|
| REQ-DT-001 | U | The system shall produce identical hashes for identical (config, input trace, step schedule) | DeterminismMinimal:`TraceDeterminism` | **OK** |
| REQ-DT-002 | U | The system shall produce different hashes for different configs, all else equal | DeterminismMinimal:`ConfigSensitivity` | **OK** |
| REQ-DT-003 | U | The system shall produce identical hashes for identical states regardless of when computed | DeterminismMinimal:`HashStability` | **OK** |
| REQ-DT-004 | S | While `HashMode::Full` is selected, the system shall hash memory, VGA, and device state | H7 | **GAP** |

### IN — Input

| ID | Pat | Requirement | Source | Status |
|----|-----|-------------|--------|--------|
| REQ-IN-001 | U | The system shall accept AT Scancode Set 1 format key events | InputMinimal:`ScancodeValid` | **OK** |
| REQ-IN-002 | E | When an extended key event is injected, the system shall prepend the 0xE0 prefix byte | InputMinimal:`E0PrefixCorrect` | **OK** |
| REQ-IN-003 | U | The system shall process input events in monotonic sequence order, preserving insertion order | InputMinimal:`InputDeterminism` | **OK** |
| REQ-IN-004 | X | If the queue fills mid-character during `text_input`, then the system shall roll back all events for that character | M2, InputMinimal:`BufferNotCorrupted` | **GAP** |
| REQ-IN-005 | U | The system shall enforce a queue capacity limit and return `BUFFER_TOO_SMALL` when full | InputMinimal:`BufferBounded` | **OK** |

### CP — Capture

| ID | Pat | Requirement | Source | Status |
|----|-----|-------------|--------|--------|
| REQ-CP-001 | U | The system shall return captures in RGB24 format (3 bytes/pixel, pitch = width * 3) | CaptureMinimal:`FormatFixed` | **OK** |
| REQ-CP-002 | U | The system shall return dimensions matching the current video mode | CaptureMinimal:`DimensionsConsistent` | **OK** |
| REQ-CP-003 | E | When `sync_state_from_engine()` is called, the system shall sync the framebuffer, not only timing/PIC | H8, CaptureMinimal:`BackendIndependent` | **GAP** |
| REQ-CP-004 | U | The system shall produce identical captures regardless of PAL backend | CaptureMinimal:`BackendIndependent` | **OK** |

### TH — Threading and Safety

| ID | Pat | Requirement | Source | Status |
|----|-----|-------------|--------|--------|
| REQ-TH-001 | U | The system shall reject API calls from non-owner threads with `WRONG_THREAD` | ThreadingMinimal:`CoreSingleThreaded` | **OK** |
| REQ-TH-002 | U | The system shall apply `LIB_CHECK_THREAD()` in every engine function that accesses context or state | M7, ThreadingMinimal:`CoreSingleThreaded` | **GAP** |
| REQ-TH-003 | X | If a callback throws a C++ exception, then the system shall catch it before unwinding across `extern "C"` | M6 | **GAP** |
| REQ-TH-004 | S | While the audio callback thread accesses `MixerState`, the system shall synchronize access with the main thread | M3, PALMinimal:`ThreadSafety` | **GAP** |
| REQ-TH-005 | U | The system shall ensure PAL-spawned threads never invoke core API functions | PALMinimal:`AudioPushModel` | **OK** |

### ER — Error Handling

| ID | Pat | Requirement | Source | Status |
|----|-----|-------------|--------|--------|
| REQ-ER-001 | U | The system shall check errors in priority: NULL_HANDLE → WRONG_THREAD → REENTRANT_CALL → BUFFER_TOO_SMALL | ErrorModel:`ErrorCodeDeterministic` | **OK** |
| REQ-ER-002 | U | The system shall never return OK for a core op when no instance exists | ErrorModel:`SuccessRequiresValidState` | **OK** |
| REQ-ER-003 | X | If a non-null handle not matching sentinel `(void*)1` is passed to an engine function, then the system shall return an error | M8 | **GAP** |

### CF — Configuration

| ID | Pat | Requirement | Source | Status |
|----|-----|-------------|--------|--------|
| REQ-CF-001 | X | If `api_version` does not match, then `legends_create()` shall return `VERSION_MISMATCH` | ConfigValidation:`VersionChecked` | **OK** |
| REQ-CF-002 | X | If `cpu_cycles` is zero or outside valid range, then `legends_create()` shall return `INVALID_CONFIG` | ConfigValidation:`AllFieldsValidated` | **GAP** |
| REQ-CF-003 | E | When `dosbox_lib_create()` receives non-null string fields, the system shall deep-copy them | M9 | **PARTIAL** |

### BQ — Build and Quality

| ID | Pat | Requirement | Source | Status |
|----|-----|-------------|--------|--------|
| REQ-BQ-001 | U | The system shall compile each source definition exactly once (no duplicated headers) | C1 | **GAP** |
| REQ-BQ-002 | X | If `address + size` would overflow, then memory read/write shall return an error (subtraction form) | H6 | **GAP** |
| REQ-BQ-003 | U | `check_gsl_lite_usage.py` shall exclude all generated directories from its scan | L6 | **GAP** |
| REQ-BQ-004 | U | The system shall declare all Python dev dependencies in `requirements-dev.txt` | L7 | **GAP** |
| REQ-BQ-005 | E | When a test passes an invalid handle to destroy, the test shall assert an error return | L8 | **GAP** |
| REQ-BQ-006 | U | The system shall track all mutable extern globals in the migration registry | M4 | **GAP** |

### Requirements Summary

| Domain | Total | OK | PARTIAL | GAP |
|--------|-------|----|---------|-----|
| LC — Lifecycle | 6 | 2 | 0 | 4 |
| EX — Execution | 6 | 2 | 1 | 3 |
| SR — Serialization | 8 | 3 | 2 | 3 |
| DT — Determinism | 4 | 3 | 0 | 1 |
| IN — Input | 5 | 4 | 0 | 1 |
| CP — Capture | 4 | 3 | 0 | 1 |
| TH — Threading | 5 | 2 | 0 | 3 |
| ER — Error Handling | 3 | 2 | 0 | 1 |
| CF — Configuration | 3 | 1 | 1 | 1 |
| BQ — Build/Quality | 6 | 0 | 0 | 6 |
| **Total** | **50** | **22** | **4** | **24** |

---

## 7. TLA+ Specification Conformance

All 11 CI-checked TLA+ specs evaluated invariant-by-invariant against implementation source. Ratings: **C** = Conformant, **P** = Partial, **N** = Non-Conformant.

### LifecycleMinimal.tla (~250 states)

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `AtMostOneInstance` | C | Atomic CAS at `legends_embed_api.cpp:807` |
| `MisuseSafe` | C | All misuse paths return error codes |
| `HandleConsistency` | **N** | H5: `get_instance()` fallback destroys active instance on any non-null handle |
| `NoReentrantSuccess` | C | `in_step` flag at line 1053 |
| `WrongThreadBlocked` | C | `LEGENDS_CHECK_THREAD()` macro |
| `ConfigGated` | C | Config checked before creation (lines 828-838) |

**Fix**: Remove `g_active_instance` fallback in `get_instance()`. **Effort: Small.**

### PALMinimal.tla (~200 states)

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `AudioPushModel` | C | Core→PAL only; headless stub is push model |
| `ThreadSafety` | **N** | M3: `MixerState` has no mutex/atomic synchronization |
| `AudioQueueBounded` | C | Fixed capacity with drop-on-overflow |
| `ComponentDependency` | C | PAL components initialize after context |
| `BackpressureNonNegative` | C | Unsigned dropped frame counter |

**Fix**: Add `std::mutex` to `MixerState`. **Effort: Small.**

### ThreadingMinimal.tla (~2,000 states)

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `CoreSingleThreaded` | **P** | Legends layer enforces; `dosbox_lib_get_context_ptr()` bypasses `LIB_CHECK_THREAD()` (M7) |
| `PALIsolation` | C | PAL threads never call core |
| `NoDataRaces` | **P** | MixerState unsynchronized (M3); context pointer accessible without thread check (M7) |
| `CallStackValid` | C | Guard clauses enforce valid call order |
| `WrongThreadBlocked` | **P** | Enforced at legends layer; one engine function is the exception |
| `NoReentrantStep` | C | `in_step` flag blocks nested steps |

**Fix 1**: Add `LIB_CHECK_THREAD()` to `dosbox_lib_get_context_ptr()`. **Effort: Trivial** (one line).
**Fix 2**: MixerState mutex (same as PALMinimal).

### SaveStateTest.tla (~30 states)

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `ObservationPreserved` | **P** | Round-trip works for serialized fields; CPU GPRs, VGA, RAM not serialized (H1) |
| `EventCountPreserved` | **P** | Legends event queue serialized; engine `PIC_RunQueue` events not serialized |
| `EventDigestPreserved` | **P** | Same gap as `EventCountPreserved` |
| `TimePreserved` | C | `total_cycles`, `emu_time_us`, `cycles_per_ms` all serialized |
| `IntegrityCheckPasses` | C | CRC32 verified before any mutation |
| `CorruptionDetected` | C | Load rejects CRC mismatch |
| `PartialSaveSafe` | C | Four-phase commit pattern |

**Fix 1**: Serialize CPU GPRs, VGA state, RAM (Phase B). **Effort: Large.**
**Fix 2**: Serialize engine event scheduler queue. **Effort: Medium.**

### DeterminismMinimal.tla (~500 states)

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `TraceDeterminism` | C | SHA-256 hash; identical inputs → identical hashes (tested) |
| `HashStability` | C | Pure function of state |
| `ConfigSensitivity` | C | Different configs → different hashes (tested) |

**All invariants satisfied.** TLA+ uses abstract polynomial hash; implementation uses SHA-256 (stronger). Properties hold.

### CaptureMinimal.tla (~100 states)

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `DimensionsConsistent` | C | Dimensions from `frame_state` tracking video mode |
| `FormatFixed` | C | RGB24, pitch = width * 3 |
| `BackendIndependent` | **P** | Captures are backend-independent but also engine-independent — `frame_state` has synthetic test pattern (H8), not real framebuffer |
| `FramebufferSizeConsistent` | C | Size = width * height * 3 |

**Fix**: Wire `sync_state_from_engine()` to copy actual framebuffer from engine. **Effort: Medium.**

### InputMinimal.tla (~300 states)

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `ScancodeValid` | C | AT Scancode Set 1 used throughout |
| `BufferNotCorrupted` | **N** | M2: `text_input()` partial commit can leave shift key stuck |
| `E0PrefixCorrect` | C | Extended keys push 0xE0 then scancode |
| `InputDeterminism` | C | Monotonic sequence counter, FIFO drain |
| `BufferBounded` | C | 320-event ring buffer, error on full |

**Fix**: Add transactional semantics to `text_input()` — pre-check queue slots before each character. **Effort: Small.**

### ReentrancyMinimal.tla (~50 states)

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `NoNestedStep` | C | `in_step` flag, returns `REENTRANT_CALL` |
| `PhaseConsistent` | **P** | Step functions OK; non-step API functions from callbacks don't check `in_step` (M1) |
| `CallbackSafe` | **P** | Callbacks during step can re-enter non-step APIs undetected |

**Fix**: Extend `in_step` guard to mutating API functions (key_event, mouse_event, save_state, load_state, reset). **Effort: Small.**

### ErrorModel.tla (~500 states)

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `ErrorCodeDeterministic` | **P** | Priority chain matches, but H5 destroy fallback makes destroy non-deterministic for invalid handles |
| `SuccessRequiresValidState` | C | All core ops check instance |
| `ErrorCodesComplete` | C | All codes in defined 14+1 set |
| `NullHandleConsistent` | **N** | H5: invalid non-null handles bypass null check and destroy real instance |
| `ReentrantCodeCorrect` | C | `REENTRANT_CALL` iff `in_step && op == STEP` |
| `WrongThreadCodeCorrect` | C | `WRONG_THREAD` iff non-owner thread |

**Fix**: Same as LifecycleMinimal — remove `g_active_instance` fallback. **Effort: Small.**

### ConfigValidation.tla (~20 states)

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `InvalidConfigBlocked` | **P** | `struct_size` and `api_version` validated; `cpu_cycles` accepts any value including 0 |
| `ValidConfigAccepted` | C | Valid config → instance created |
| `VersionChecked` | C | Wrong version → `VERSION_MISMATCH` |
| `AllFieldsValidated` | **N** | `cpu_cycles` not range-checked; no `audio_rate` field exists |

**Fix**: Add `cpu_cycles > 0` validation. **Effort: Trivial.**

### APIContract.tla (~1,000 states, composite)

| Gate Group | Rating | Blocking Issues |
|------------|--------|-----------------|
| Gates 2a-2c (Lifecycle/Config) | **P** | HandleConsistency (H5), AllFieldsValidated |
| Gates 4a-4c (Determinism/SaveState) | **P** | ObservationPreserved (H1) |
| Gates 5a-5c (Capture) | **P** | BackendIndependent (H8) |
| Gates 6a-6b (Input) | **P** | BufferNotCorrupted (M2) |
| Gates 7a-7d (PAL/Threading) | **P** | ThreadSafety (M3), CoreSingleThreaded (M7) |
| Gates 8a-8c (Reentrancy) | **P** | PhaseConsistent (M1) |
| NoExitAbort, NoStdout, NoEnvChange, VersionHandshake | C | — |

### Non-CI Specs: Key Gaps

| Spec | Invariant | Issue |
|------|-----------|-------|
| Scheduler.tla | `DeterministicSelection` | DOSBox-X event system doesn't guarantee deterministic tie-breaking by `tieKey` |
| Scheduler.tla | `EventsNotInPast` | Not verified in implementation |
| PIC.tla | `MaskedIRQNotDelivered` | Not testable — C2 means PIC_RunQueue never runs during bridge execution |
| PIC.tla | `PriorityRespected` | Same — PIC priority only matters when events are processed |
| Bus.tla | `MemRangesDisjoint` | H6 integer overflow can bypass routing invariant |
| EmuKernel.tla | `MonotonicTime` | `load_state` can rewind `total_cycles` (intentional; spec accounts for it) |

### Conformance Summary

| Spec | Invariants | C | P | N |
|------|-----------|---|---|---|
| LifecycleMinimal | 6 | 5 | 0 | 1 |
| PALMinimal | 5 | 4 | 0 | 1 |
| ThreadingMinimal | 6 | 3 | 3 | 0 |
| SaveStateTest | 7 | 4 | 3 | 0 |
| DeterminismMinimal | 3 | 3 | 0 | 0 |
| CaptureMinimal | 4 | 3 | 1 | 0 |
| InputMinimal | 5 | 4 | 0 | 1 |
| ReentrancyMinimal | 3 | 1 | 2 | 0 |
| ErrorModel | 6 | 4 | 1 | 1 |
| ConfigValidation | 4 | 2 | 1 | 1 |
| **Total** | **49** | **33 (67%)** | **11 (22%)** | **5 (10%)** |

---

## Sprint Recommendation

The roadmap below integrates audit findings, EARS requirements, and TLA+ conformance gaps into a unified phased plan. Each phase unblocks the next; items within a phase are independent and can be parallelized.

### Phase 1: Quick Wins (~2 days) — unblocks 5 TLA+ specs, fixes 11 invariants

| # | Item | Finding | Req | TLA+ Spec Fixed | Effort |
|---|------|---------|-----|-----------------|--------|
| 1 | Fix memory bounds overflow (subtraction form) | H6 | REQ-SR-003 | — | Small |
| 2 | Remove/constrain `g_active_instance` destroy fallback | H5 | REQ-LC-005 | LifecycleMinimal, ErrorModel | Small |
| 3 | Resolve `HashMode::Full` contract mismatch | H7 | REQ-DT-002 | — | Small |
| 4 | Add `LIB_CHECK_THREAD()` to `dosbox_lib_get_context_ptr()` | M7 | REQ-TH-001 | ThreadingMinimal | Small |
| 5 | Validate `cpu_cycles` range at config time | — | REQ-CF-001 | ConfigValidation | Small |
| 6 | Add `MixerState` mutex for PAL audio | — | REQ-CP-003 | PALMinimal | Small |
| 7 | Wrap `text_input` in transaction (commit/rollback) | — | REQ-IN-002 | InputMinimal | Small |

### Phase 2: Bridge & Capture (~1 week) — fixes ReentrancyMinimal, CaptureMinimal

| # | Item | Finding | Req | TLA+ Spec Fixed | Effort |
|---|------|---------|-----|-----------------|--------|
| 8 | Extend `in_step` guard to all mutating APIs | M1 | REQ-EX-004 | ReentrancyMinimal | Medium |
| 9 | Sync framebuffer from engine (replace synthetic test pattern) | H8 | REQ-CP-001 | CaptureMinimal | Medium |
| 10 | Resolve dual runtime path divergence (`dosbox_step` vs `dosbox_lib_step_cycles`) | M10 | REQ-EX-001 | — | Medium |
| 11 | Guard `dosbox_lib_get_context_ptr()` return in `legends_step_cycles` | M11 | REQ-ER-003 | ErrorModel | Small |
| 12 | Exception-safe callback invocation at C ABI boundary | M6 | REQ-ER-004 | — | Small |

### Phase 3: Phase B Serialization (~2 weeks) — SaveStateTest fully CONFORMANT, Phase E unblocked

| # | Item | Finding | Req | TLA+ Spec Fixed | Effort |
|---|------|---------|-----|-----------------|--------|
| 13 | Serialize CPU GPRs (EAX-EDI, segment registers) | H1 | REQ-SR-001 | SaveStateTest | Small |
| 14 | RAM content serialization approach | H1 | REQ-SR-002 | SaveStateTest | Medium |
| 15 | VGA hardware state serialization | H1 | REQ-SR-001 | SaveStateTest | Medium |
| 16 | Engine event queue serialization | — | REQ-SR-004 | SaveStateTest | Medium |
| 17 | Full round-trip tests for all 8 V4 subsystems | — | REQ-SR-005 | — | Small |
| 18 | Fix unaligned `reinterpret_cast` on caller buffers | H9 | REQ-SR-001 | — | Small |
| 19 | V3 backward compatibility test | — | — | — | Small |

Completing Phase 3 unblocks Phase E (determinism at scale) and Sprint 4 (Deterministic Replay as Product).

### Phase 4: PIC/Scheduler Integration & Structural Work

| # | Item | Finding | Req | TLA+ Spec Fixed | Effort |
|---|------|---------|-----|-----------------|--------|
| 20 | Add `PIC_RunQueue()` / `CPU_Check_NMI()` to CPU bridge | C2 | REQ-EX-002 | PIC, Scheduler (non-CI) | Medium |
| 21 | Deterministic event scheduler tie-breaking | — | REQ-DT-001 | DeterminismMinimal | Medium |
| 22 | Code deduplication (27+ header pairs) | C1 | REQ-BQ-001 | — | Large |
| 23 | Strengthen handle validation beyond null-check | M8 | REQ-LC-001 | — | Small |
| 24 | Deep-copy or validate engine-layer config lifetime | M9 | REQ-CF-003 | — | Small |

Phase 4 makes device model specs (PIC, Scheduler, EmuKernel) testable and addresses the two critical structural findings.
