# Project Legends — Implementation Requirements (EARS Notation)

Derived from: AUDIT.md (2026-02-24), 33 TLA+ specifications, source verification
Date: 2026-02-24

Notation: [EARS (Easy Approach to Requirements Syntax)](https://www.jamasoftware.com/requirements-management-guide/writing-requirements/adopting-the-ears-notation-to-improve-requirements-engineering/)

## EARS Pattern Key

| Pattern | Template | Use |
|---------|----------|-----|
| Ubiquitous | The [system] shall [response] | Always-active, no trigger |
| Event-driven | When [trigger], the [system] shall [response] | Response to event |
| State-driven | While [condition], the [system] shall [response] | Active in state |
| Unwanted | If [condition], then the [system] shall [response] | Error/fault handling |
| Optional | Where [feature], the [system] shall [response] | Feature-gated |
| Complex | While [state], when [trigger], the [system] shall [response] | State + event |

### Status Legend

- **OK** — Implementation conforms
- **GAP** — Implementation does not conform; work required
- **PARTIAL** — Partially conforms; narrowed gap remains

---

## LC — Lifecycle

### REQ-LC-001 Single Instance Enforcement [Ubiquitous]

The system shall enforce that at most one legends instance exists per process.

| | |
|---|---|
| Source | LifecycleMinimal.tla:`AtMostOneInstance` |
| Evidence | `legends_embed_api.cpp:807` atomic CAS |
| Status | **OK** |

### REQ-LC-002 Create Returns Handle [Event-driven]

When `legends_create()` is called with a valid config and no instance exists, the system shall allocate an instance and return a non-null handle via `handle_out`.

| | |
|---|---|
| Source | LifecycleMinimal.tla:`MisuseSafe`, ConfigValidation.tla:`ValidConfigAccepted` |
| Status | **OK** |

### REQ-LC-003 Destroy Rejects Invalid Handle [Unwanted]

If `legends_destroy()` receives a non-null handle that does not match the active instance, then the system shall return an error without modifying or destroying the active instance.

| | |
|---|---|
| Source | AUDIT H5, LifecycleMinimal.tla:`HandleConsistency` |
| Evidence | `legends_embed_api.cpp:949-957` — `get_instance()` falls back to `g_active_instance` |
| Status | **GAP** — any non-null handle silently destroys the real instance |

### REQ-LC-004 Destroy Null Handle [Event-driven]

When `legends_destroy()` is called with a null handle, the system shall return `LEGENDS_OK` without side effects.

| | |
|---|---|
| Source | ErrorModel.tla:`ResolveError` (DESTROY + NONE → OK) |
| Status | **OK** |

### REQ-LC-005 Single Execution Path [Ubiquitous]

The system shall route all step execution through the CPU bridge (`dosbox::execute_cycles()`); no alternative stub step path shall exist.

| | |
|---|---|
| Source | AUDIT M10 (dual runtime path), H3 (MachineContext.step stub) |
| Evidence | `dosbox_context.cpp:920` routes through stub; `dosbox_library.cpp:371` routes through bridge |
| Status | **GAP** — `dosbox_step()` routes through TODO stub, `dosbox_lib_step_cycles()` uses real bridge |

### REQ-LC-006 No Phantom Definitions [Ubiquitous]

The system shall provide definitions for all forward-declared classes used in public or internal headers.

| | |
|---|---|
| Source | AUDIT M5 — 7 classes forward-declared with no definitions |
| Evidence | `engine/include/aibox/machine_context.h` |
| Status | **GAP** — VgaContext, DosKernel, PicController, PitTimer, KeyboardController, MouseController, SoundSubsystem have no definitions |

---

## EX — Execution

### REQ-EX-001 PIC Event Processing [Complex]

While the CPU bridge is executing cycles, when `(*cpudecoder)()` is about to be called, the system shall call `PIC_RunQueue()` to process pending timer and interrupt events.

| | |
|---|---|
| Source | AUDIT C2, PIC.tla:`PriorityRespected`, EmuKernel.tla |
| Evidence | `cpu_bridge.cpp:89` — no `PIC_RunQueue()` call |
| Status | **GAP** — timer ticks, keyboard IRQs, and PIC-driven events do not fire during bridge execution |

### REQ-EX-002 NMI Check [Complex]

While the CPU bridge is executing cycles, when the decoder returns, the system shall call `CPU_Check_NMI()` before the next decoder invocation.

| | |
|---|---|
| Source | AUDIT C2 |
| Evidence | `cpu_bridge.cpp` — no `CPU_Check_NMI()` call |
| Status | **GAP** |

### REQ-EX-003 Step Reentrancy Guard [Unwanted]

If `legends_step_cycles()` or `legends_step_ms()` is called while a step is already in progress, then the system shall return `LEGENDS_ERR_REENTRANT_CALL` without executing any cycles.

| | |
|---|---|
| Source | ReentrancyMinimal.tla:`NoNestedStep` |
| Evidence | `legends_embed_api.cpp:1053` — `in_step` flag checked |
| Status | **OK** |

### REQ-EX-004 Callback Reentrancy Guard [Unwanted]

If any legends API function is called from an engine callback during step execution, then the system shall return the appropriate error code without modifying state.

| | |
|---|---|
| Source | AUDIT M1, ReentrancyMinimal.tla:`CallbackSafe` |
| Evidence | Only step functions check `in_step`; other API functions lack guards |
| Status | **PARTIAL** — step reentrancy enforced; non-step API calls from callbacks unguarded |

### REQ-EX-005 Input Drain Before Step [Event-driven]

When a step function is called, the system shall drain all pending input events to the engine before executing any CPU cycles.

| | |
|---|---|
| Source | InputMinimal.tla:`InputDeterminism` |
| Evidence | `legends_embed_api.cpp:1073` — `drain_input_to_engine()` before step |
| Status | **OK** |

### REQ-EX-006 Context Pointer Validation [Unwanted]

If `dosbox_lib_get_context_ptr()` returns an error, then `legends_step_cycles()` shall propagate the error to the caller without dereferencing the context pointer.

| | |
|---|---|
| Source | AUDIT M11 |
| Evidence | `legends_embed_api.cpp:1065` — return value ignored, line 1067 dereferences unconditionally |
| Status | **GAP** — null dereference if call fails |

---

## SR — Serialization

### REQ-SR-001 Save/Load Round-Trip [Event-driven]

When state is saved and then loaded, the system shall restore observable state such that `Obs(Deserialize(Serialize(S))) = Obs(S)`.

| | |
|---|---|
| Source | SaveStateTest.tla:`ObservationPreserved` |
| Status | **PARTIAL** — round-trip works for serialized fields, but CPU GPRs, VGA, and RAM are not serialized (H1) |

### REQ-SR-002 CPU Register Serialization [Event-driven]

When `legends_save_state()` is called, the system shall serialize CPU general-purpose registers (EAX-EDI), segment registers, and the instruction pointer.

| | |
|---|---|
| Source | AUDIT H1 |
| Evidence | CPU section only has cycle counters and NMI state (96 bytes) |
| Status | **GAP** |

### REQ-SR-003 VGA State Serialization [Event-driven]

When `legends_save_state()` is called, the system shall serialize the full VGA hardware state including the register file and video memory.

| | |
|---|---|
| Source | AUDIT H1 |
| Evidence | VGA section only has width/height/mode/refresh (32 bytes) |
| Status | **GAP** |

### REQ-SR-004 RAM Serialization [Event-driven]

When `legends_save_state()` is called, the system shall serialize guest RAM contents.

| | |
|---|---|
| Source | AUDIT H1 |
| Evidence | Memory section only has page config and A20 gate (72 bytes) |
| Status | **GAP** |

### REQ-SR-005 Event Queue Serialization [Event-driven]

When `legends_save_state()` is called, the system shall serialize the event queue including deadline, kind, and tieKey for each pending event.

| | |
|---|---|
| Source | SaveState.tla (critical note), SaveStateTest.tla:`EventCountPreserved`, `EventDigestPreserved` |
| Evidence | `legends_embed_api.cpp:1699` — legends-layer event queue serialized; engine-layer PIC_RunQueue events NOT serialized |
| Status | **PARTIAL** — legends event queue serialized, engine event queue not |

### REQ-SR-006 CRC Integrity [Unwanted]

If a loaded state buffer has a CRC32 mismatch, then the system shall reject the load and return an error without modifying any state.

| | |
|---|---|
| Source | SaveStateTest.tla:`CorruptionDetected`, `IntegrityCheckPasses` |
| Status | **OK** |

### REQ-SR-007 Aligned Buffer Access [Ubiquitous]

The system shall use `memcpy` (not `reinterpret_cast`) when reading structured data from caller-provided buffers to avoid undefined behavior on strict-alignment architectures.

| | |
|---|---|
| Source | AUDIT H9 |
| Evidence | `legends_embed_api.cpp:1657,1668,2058,2122` |
| Status | **GAP** — uses `reinterpret_cast` |

### REQ-SR-008 Atomic Load [Ubiquitous]

The system shall implement state loading as an atomic operation: either all state is restored or none is modified.

| | |
|---|---|
| Source | SaveStateTest.tla:`PartialSaveSafe` |
| Evidence | Four-phase commit pattern in load_state |
| Status | **OK** |

---

## DT — Determinism

### REQ-DT-001 Trace Determinism [Ubiquitous]

The system shall produce identical state hashes when given identical configuration, input trace, and step schedule.

| | |
|---|---|
| Source | DeterminismMinimal.tla:`TraceDeterminism` |
| Status | **OK** — verified by `test_workflow_determinism.cpp` |

### REQ-DT-002 Config Sensitivity [Ubiquitous]

The system shall produce different state hashes when given different configurations, all else equal.

| | |
|---|---|
| Source | DeterminismMinimal.tla:`ConfigSensitivity` |
| Status | **OK** |

### REQ-DT-003 Hash Stability [Ubiquitous]

The system shall produce identical state hashes for identical machine states regardless of when the hash is computed.

| | |
|---|---|
| Source | DeterminismMinimal.tla:`HashStability` |
| Status | **OK** |

### REQ-DT-004 HashMode::Full [State-driven]

While `HashMode::Full` is selected, the system shall hash memory contents, VGA state, and device state.

| | |
|---|---|
| Source | AUDIT H7 |
| Evidence | `state_hash.cpp:296-301` only appends `"FULL_MODE"` marker string |
| Status | **GAP** — no actual memory/VGA/device data hashed |

---

## IN — Input

### REQ-IN-001 Scancode Format [Ubiquitous]

The system shall accept and inject AT Scancode Set 1 format key events.

| | |
|---|---|
| Source | InputMinimal.tla:`ScancodeValid` |
| Status | **OK** |

### REQ-IN-002 Extended Key Prefix [Event-driven]

When an extended key event is injected, the system shall prepend the 0xE0 prefix byte before the scancode byte.

| | |
|---|---|
| Source | InputMinimal.tla:`E0PrefixCorrect` |
| Status | **OK** |

### REQ-IN-003 Input Ordering [Ubiquitous]

The system shall process input events in monotonic sequence order, preserving insertion order across interleaved keyboard and mouse events.

| | |
|---|---|
| Source | InputMinimal.tla:`InputDeterminism` |
| Evidence | `InputEvent.sequence` monotonic counter, FIFO drain |
| Status | **OK** |

### REQ-IN-004 Text Input Atomicity [Unwanted]

If the input queue fills during `legends_text_input()` processing of a multi-event character (shift-down + key-down + key-up + shift-up), then the system shall roll back all events for that character, leaving no partial key sequences in the queue.

| | |
|---|---|
| Source | AUDIT M2, InputMinimal.tla:`BufferNotCorrupted` |
| Evidence | No rollback mechanism; shift key can get stuck down |
| Status | **GAP** |

### REQ-IN-005 Queue Capacity [Ubiquitous]

The system shall enforce an input queue capacity limit and return `LEGENDS_ERR_BUFFER_TOO_SMALL` when the queue is full.

| | |
|---|---|
| Source | InputMinimal.tla:`BufferBounded` |
| Status | **OK** — 320-event ring buffer with full check |

---

## CP — Capture

### REQ-CP-001 RGB Format [Ubiquitous]

The system shall return frame captures in RGB24 format (3 bytes per pixel, no padding, pitch = width * 3).

| | |
|---|---|
| Source | CaptureMinimal.tla:`FormatFixed` |
| Status | **OK** |

### REQ-CP-002 Dimensions Consistent [Ubiquitous]

The system shall return frame dimensions that match the current video mode, not the backend configuration.

| | |
|---|---|
| Source | CaptureMinimal.tla:`DimensionsConsistent` |
| Status | **OK** |

### REQ-CP-003 Framebuffer Sync [Event-driven]

When `sync_state_from_engine()` is called after a step, the system shall synchronize the framebuffer contents from the engine, not only timing and PIC state.

| | |
|---|---|
| Source | AUDIT H8, CaptureMinimal.tla:`BackendIndependent` |
| Evidence | `legends_embed_api.cpp:1498` — syncs timing/PIC only; frame_state initialized with synthetic test pattern (line 919-920) |
| Status | **GAP** — captures return synthetic test pattern, not engine framebuffer |

### REQ-CP-004 Backend Independence [Ubiquitous]

The system shall produce identical capture output regardless of PAL backend (SDL2, SDL3, Headless).

| | |
|---|---|
| Source | CaptureMinimal.tla:`BackendIndependent` |
| Status | **OK** — capture reads from instance state, not backend |

---

## TH — Threading and Safety

### REQ-TH-001 Owner Thread Enforcement [Ubiquitous]

The system shall reject API calls from any thread other than the owner thread with `LEGENDS_ERR_WRONG_THREAD`.

| | |
|---|---|
| Source | ThreadingMinimal.tla:`CoreSingleThreaded`, `WrongThreadBlocked` |
| Status | **OK** at legends layer; **PARTIAL** at engine layer (see REQ-TH-002) |

### REQ-TH-002 Engine Thread Check Consistency [Ubiquitous]

The system shall apply `LIB_CHECK_THREAD()` in every engine-layer function that accesses context or mutable state.

| | |
|---|---|
| Source | AUDIT M7, ThreadingMinimal.tla:`CoreSingleThreaded` |
| Evidence | `dosbox_library.cpp:466-476` — `dosbox_lib_get_context_ptr()` has no `LIB_CHECK_THREAD()` |
| Status | **GAP** |

### REQ-TH-003 Exception Safety at C ABI [Unwanted]

If a user-provided callback (log, event) throws a C++ exception, then the system shall catch it before the stack unwinds across the `extern "C"` boundary.

| | |
|---|---|
| Source | AUDIT M6 |
| Evidence | `instance_state.h:51` — `log()` called unguarded from `extern "C"` functions |
| Status | **GAP** |

### REQ-TH-004 Mixer Synchronization [State-driven]

While the audio callback thread accesses `MixerState`, the system shall synchronize access with the main thread via a mutex or lock-free protocol.

| | |
|---|---|
| Source | AUDIT M3, PALMinimal.tla:`ThreadSafety` |
| Status | **GAP** — no synchronization primitives in MixerState |

### REQ-TH-005 PAL Thread Isolation [Ubiquitous]

The system shall ensure that PAL-spawned threads (audio callback, input poll, timer) never invoke core API functions.

| | |
|---|---|
| Source | PALMinimal.tla:`AudioPushModel`, ThreadingMinimal.tla:`PALIsolation` |
| Status | **OK** — PAL abstraction enforces push-only model |

---

## ER — Error Handling

### REQ-ER-001 Error Priority Chain [Ubiquitous]

The system shall check error conditions in priority order: NULL_HANDLE → WRONG_THREAD → REENTRANT_CALL → BUFFER_TOO_SMALL → operation-specific errors.

| | |
|---|---|
| Source | ErrorModel.tla:`ErrorCodeDeterministic`, `ResolveError` priority chain |
| Evidence | Guard clause order in `legends_embed_api.cpp` matches: `get_instance` → `CHECK_THREAD` → `in_step` |
| Status | **OK** |

### REQ-ER-002 Success Requires Instance [Ubiquitous]

The system shall never return `LEGENDS_OK` for a core operation when no instance exists.

| | |
|---|---|
| Source | ErrorModel.tla:`SuccessRequiresValidState` |
| Status | **OK** |

### REQ-ER-003 Engine Handle Validation [Unwanted]

If a non-null handle that does not match the sentinel value `(void*)1` is passed to an engine-layer function, then the system shall return an error.

| | |
|---|---|
| Source | AUDIT M8 |
| Evidence | `dosbox_library.cpp:240,255,359` — validation only checks `!= nullptr` |
| Status | **GAP** — any non-null pointer passes |

---

## CF — Configuration

### REQ-CF-001 Version Check [Unwanted]

If the config `api_version` does not match `LEGENDS_API_VERSION`, then `legends_create()` shall return `LEGENDS_ERR_VERSION_MISMATCH` without creating an instance.

| | |
|---|---|
| Source | ConfigValidation.tla:`VersionChecked` |
| Status | **OK** — checked at `legends_embed_api.cpp:834` |

### REQ-CF-002 Cycles Validation [Unwanted]

If `cpu_cycles` is zero or outside the valid range, then `legends_create()` shall return `LEGENDS_ERR_INVALID_CONFIG`.

| | |
|---|---|
| Source | ConfigValidation.tla:`ValidCyclesPerMs`, `AllFieldsValidated` |
| Evidence | No cycles validation in create; accepts any value including 0 |
| Status | **GAP** |

### REQ-CF-003 Config String Ownership [Event-driven]

When `dosbox_lib_create()` receives a config with non-null `config_path` or `working_dir`, the system shall deep-copy those strings so the caller may free the originals.

| | |
|---|---|
| Source | AUDIT M9 |
| Evidence | Legends layer deep-copies via `std::string` (`legends_embed_api.cpp:842-848`). Engine layer shallow-copies (`dosbox_library.cpp:213`). |
| Status | **PARTIAL** — legends layer OK, engine layer GAP |

---

## BQ — Build and Quality

### REQ-BQ-001 Single Compilation Unit [Ubiquitous]

The system shall compile each source definition exactly once, eliminating duplicated header pairs between `include/legends/` and `engine/include/aibox/`.

| | |
|---|---|
| Source | AUDIT C1 — 27+ duplicated header pairs |
| Status | **GAP** |

### REQ-BQ-002 Memory Bounds Check [Unwanted]

If `address + size` would overflow the address space in `dosbox_lib_read_memory` or `dosbox_lib_write_memory`, then the system shall return an error. Bounds checks shall use the subtraction form (`size > max - address`) to prevent integer wrap.

| | |
|---|---|
| Source | AUDIT H6 |
| Evidence | `dosbox_library.cpp:1277,1301` — uses addition form |
| Status | **GAP** |

### REQ-BQ-003 Script Exclusion Lists [Ubiquitous]

The `check_gsl_lite_usage.py` script shall exclude all generated directories (`_deps`, `build_test`, and similar) from its scan.

| | |
|---|---|
| Source | AUDIT L6 |
| Evidence | `scripts/check_gsl_lite_usage.py:207` |
| Status | **GAP** |

### REQ-BQ-004 Dev Dependencies Declared [Ubiquitous]

The system shall declare all Python development dependencies (including `pyyaml`) in a `requirements-dev.txt` file.

| | |
|---|---|
| Source | AUDIT L7 |
| Status | **GAP** |

### REQ-BQ-005 Test Realism [Event-driven]

When a test passes an invalid handle to `legends_destroy()`, the test shall assert an error return, not success.

| | |
|---|---|
| Source | AUDIT L8, relates to REQ-LC-003 |
| Evidence | `tests/unit/test_legends_embed.cpp:23` expects success for `(void*)0xDEAD` |
| Status | **GAP** |

### REQ-BQ-006 Global State Tracking [Ubiquitous]

The system shall track all mutable extern globals in the migration registry.

| | |
|---|---|
| Source | AUDIT M4 — 30-40 untracked globals in `engine/include/` |
| Status | **GAP** |

---

## Summary

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
