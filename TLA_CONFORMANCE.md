# TLA+ Specification Conformance Analysis

Date: 2026-06-10
verified-at: 9cd8d1778d2c03e7a67b46de5036b77fceb3b577
Scope: All 11 CI-checked TLA+ specs vs. implementation source code

---

## Methodology

Each CI-checked TLA+ specification was read in full. Every named invariant was evaluated against the corresponding implementation code. Conformance ratings:

| Rating | Meaning |
|--------|---------|
| CONFORMANT | Implementation satisfies the invariant |
| PARTIAL | Some paths conform, others don't |
| NON-CONFORMANT | Implementation violates the invariant |
| DEFERRED | Invariant models planned functionality not yet implemented |

Rebaseline note: the February record listed five non-conformant invariants. At
the verification commit above, four are conformant and the remaining config
field-completeness invariant is partial rather than non-conformant.

---

## 1. LifecycleMinimal.tla

**File:** `spec/tla/LifecycleMinimal.tla` (~250 states at MaxOperations=6)
**Implementation:** `legends_embed_api.cpp`, `dosbox_library.cpp`

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `AtMostOneInstance` | CONFORMANT | Atomic CAS at `legends_embed_api.cpp:807` enforces single instance |
| `MisuseSafe` | CONFORMANT | All misuse paths return error codes, never crash |
| `HandleConsistency` | CONFORMANT | `get_instance()` strict-matches the active instance pointer and returns null for invalid non-null handles |
| `NoReentrantSuccess` | CONFORMANT | `in_step` flag at line 1053 blocks nested steps |
| `WrongThreadBlocked` | CONFORMANT | `LEGENDS_CHECK_THREAD()` macro returns `WRONG_THREAD` |
| `ConfigGated` | CONFORMANT | Invalid config checked before instance creation (lines 828-838) |

### Required Work

None for this invariant set.

---

## 2. PALMinimal.tla

**File:** `spec/tla/PALMinimal.tla` (~200 states)
**Implementation:** PAL headers, `headless_stub.cpp`, `MixerState`

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `AudioPushModel` | CONFORMANT | Audio flows core→PAL only; headless stub is push model |
| `ThreadSafety` | CONFORMANT | Mixer callback exchange uses atomic producer/consumer positions in `MixerState` |
| `AudioQueueBounded` | CONFORMANT | Queue has fixed capacity with drop-on-overflow semantics |
| `ComponentDependency` | CONFORMANT | PAL components initialize after context |
| `BackpressureNonNegative` | CONFORMANT | Dropped frame counter is unsigned |

### Required Work

None for this invariant set.

---

## 3. ThreadingMinimal.tla

**File:** `spec/tla/ThreadingMinimal.tla` (~2,000 states)
**Implementation:** `legends_embed_api.cpp`, `dosbox_library.cpp`

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `CoreSingleThreaded` | CONFORMANT | Legends layer enforces owner-thread checks; `dosbox_lib_get_context_ptr()` now uses `LIB_CHECK_THREAD()` |
| `PALIsolation` | CONFORMANT | PAL threads use push-only model, never call core |
| `NoDataRaces` | CONFORMANT | Prior MixerState and context-pointer exceptions were fixed for the modeled paths |
| `CallStackValid` | CONFORMANT | Guard clauses enforce valid call order |
| `WrongThreadBlocked` | CONFORMANT | Engine context pointer access now checks thread affinity |
| `NoReentrantStep` | CONFORMANT | `in_step` flag blocks nested step calls |

### Required Work

None for this invariant set.

---

## 4. SaveStateTest.tla

**File:** `spec/tla/SaveStateTest.tla` (~30 states)
**Implementation:** `legends_embed_api.cpp:1587-2294`, `dosbox_library.cpp:508-1072`

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `ObservationPreserved` | **PARTIAL** | V5 serializes CPU GPRs, RAM, VGA registers, and VRAM; engine event scheduler state is still outside the saved observation. |
| `EventCountPreserved` | **PARTIAL** | Legends-layer event queue serialized. Engine-layer `PIC_RunQueue` event queue is NOT serialized. |
| `EventDigestPreserved` | **PARTIAL** | Same gap — engine event scheduler state not captured |
| `TimePreserved` | CONFORMANT | `total_cycles`, `emu_time_us`, `cycles_per_ms` all serialized |
| `IntegrityCheckPasses` | CONFORMANT | CRC32 computed after all data, verified before any mutation |
| `CorruptionDetected` | CONFORMANT | Load rejects CRC mismatch without modifying state |
| `PartialSaveSafe` | CONFORMANT | Four-phase commit: validate → engine load → stage locals → commit |

### Required Work

1. **Fix `EventCountPreserved` / `EventDigestPreserved`**: Serialize the engine-layer event scheduler queue (PIC events, timer callbacks). Requires engine cooperation. Effort: **Medium**.

---

## 5. DeterminismMinimal.tla

**File:** `spec/tla/DeterminismMinimal.tla` (~500 states)
**Implementation:** `legends_embed_api.cpp` (state_hash, verify_determinism), `test_workflow_determinism.cpp`

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `TraceDeterminism` | CONFORMANT | SHA-256 hash over engine + input + timing + PIC + events. Identical inputs → identical hashes verified in tests. |
| `HashStability` | CONFORMANT | Hash is pure function of state, no side effects |
| `ConfigSensitivity` | CONFORMANT | Different configs produce different hashes (tested) |

### Required Work

None — all invariants satisfied. Note: the TLA+ spec uses a polynomial rolling hash (`(cfgId * 7 + ih * 13 + sh * 19 + cycle) % 997`) while implementation uses SHA-256. This is correct — the spec is an abstraction; the implementation provides a stronger hash. The key properties (determinism, collision resistance, config sensitivity) hold.

---

## 6. CaptureMinimal.tla

**File:** `spec/tla/CaptureMinimal.tla` (~100 states)
**Implementation:** `legends_embed_api.cpp` (capture_text, capture_rgb)

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `DimensionsConsistent` | CONFORMANT | Dimensions read from `frame_state` which tracks video mode |
| `FormatFixed` | CONFORMANT | RGB24 format, pitch = width * 3, no padding |
| `BackendIndependent` | CONFORMANT | Capture reads from `frame_state`, and `sync_state_from_engine()` now syncs display mode, palette, text/font data, and graphics pixels from the engine when available. |
| `FramebufferSizeConsistent` | CONFORMANT | Size = width * height * 3 |

### Required Work

None for this invariant set.

---

## 7. InputMinimal.tla

**File:** `spec/tla/InputMinimal.tla` (~300 states)
**Implementation:** `legends_embed_api.cpp` (key_event, mouse_event, text_input), `instance_state.h`

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `ScancodeValid` | CONFORMANT | AT Scancode Set 1 used throughout |
| `BufferNotCorrupted` | CONFORMANT | `legends_text_input()` verifies all slots needed for a character before enqueueing any of that character's events. |
| `E0PrefixCorrect` | CONFORMANT | Extended keys push 0xE0 then scancode |
| `InputDeterminism` | CONFORMANT | Monotonic `sequence` counter, FIFO drain order |
| `BufferBounded` | CONFORMANT | 320-event ring buffer, returns error on full |

### Required Work

None for this invariant set.

---

## 8. ReentrancyMinimal.tla

**File:** `spec/tla/ReentrancyMinimal.tla` (~50 states)
**Implementation:** `legends_embed_api.cpp:1051-1059`

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `NoNestedStep` | CONFORMANT | `in_step` flag at line 1053, returns `REENTRANT_CALL` |
| `PhaseConsistent` | CONFORMANT | Mutating API paths now check `in_step`, including reset, input, save, and load. |
| `CallbackSafe` | CONFORMANT | Reentrant mutating calls during step return `LEGENDS_ERR_REENTRANT_CALL`. |

### Required Work

None for this invariant set.

---

## 9. ErrorModel.tla

**File:** `spec/tla/ErrorModel.tla` (~500 states)
**Implementation:** `legends_embed_api.cpp` guard clause order

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `ErrorCodeDeterministic` | CONFORMANT | Guard order remains deterministic and invalid non-null destroy handles no longer fall back to the active instance. |
| `SuccessRequiresValidState` | CONFORMANT | All core ops check instance via `get_instance()` |
| `ErrorCodesComplete` | CONFORMANT | All returned codes are in the defined 14+1 set |
| `NullHandleConsistent` | CONFORMANT | Invalid non-null handles return the null-handle error path instead of destroying the active instance. |
| `ReentrantCodeCorrect` | CONFORMANT | `REENTRANT_CALL` returned iff `in_step && op == STEP` |
| `WrongThreadCodeCorrect` | CONFORMANT | `WRONG_THREAD` returned iff caller is not owner thread |

### Required Work

None for this invariant set.

---

## 10. ConfigValidation.tla

**File:** `spec/tla/ConfigValidation.tla` (~20 states)
**Implementation:** `legends_embed_api.cpp:827-858`, `dosbox_library.cpp:196-222`

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `InvalidConfigBlocked` | CONFORMANT | `struct_size`, `api_version`, and non-zero `cpu_cycles` range are validated; zero cycles remains the documented auto/default value. |
| `ValidConfigAccepted` | CONFORMANT | Valid struct_size + api_version → instance created |
| `VersionChecked` | CONFORMANT | Wrong version → `VERSION_MISMATCH` at line 834 |
| `AllFieldsValidated` | **PARTIAL** | `cpu_cycles` is range-checked when non-zero, but the config struct still has no `audio_rate` field and memory validation remains limited. |

### Required Work

1. **Resolve `AllFieldsValidated`**: Decide whether to add `audio_rate`/stronger memory validation to the config struct or update the TLA+ abstraction to match the shipped config surface. Effort: **Small**.

---

## 11. APIContract.tla

**File:** `spec/tla/APIContract.tla` (~1,000 states)
**Implementation:** All source files

This is the composite specification that combines all 23 contract gates. Conformance follows from the individual specs:

| Gate Group | Rating | Blocking Issues |
|------------|--------|-----------------|
| Gates 2a-2c (Lifecycle/Config) | **PARTIAL** | Lifecycle fixed; config field completeness remains partial |
| Gates 4a-4c (Determinism/SaveState) | **PARTIAL** | Engine event scheduler state is not serialized |
| Gates 5a-5c (Capture) | CONFORMANT | Framebuffer/text sync now reads engine state when available |
| Gates 6a-6b (Input) | CONFORMANT | Text input queueing is character-atomic |
| Gates 7a-7d (PAL/Threading) | CONFORMANT | Mixer and engine context pointer exceptions fixed for modeled paths |
| Gates 8a-8c (Threading/Reentrancy) | CONFORMANT | Mutating non-step APIs reject reentry during step |
| Gate: NoExitAbort | CONFORMANT | No `exit()` or `abort()` calls in API |
| Gate: NoStdout | CONFORMANT | All output via log callback |
| Gate: NoEnvironmentChange | CONFORMANT | No environment variable modification |
| Gate: VersionHandshake | CONFORMANT | Version checked at create |

---

## Conformance Summary

### By Specification

| Spec | Invariants | Conformant | Partial | Non-Conformant |
|------|-----------|------------|---------|----------------|
| LifecycleMinimal | 6 | 6 | 0 | 0 |
| PALMinimal | 5 | 5 | 0 | 0 |
| ThreadingMinimal | 6 | 6 | 0 | 0 |
| SaveStateTest | 7 | 4 | 3 | 0 |
| DeterminismMinimal | 3 | 3 | 0 | 0 |
| CaptureMinimal | 4 | 4 | 0 | 0 |
| InputMinimal | 5 | 5 | 0 | 0 |
| ReentrancyMinimal | 3 | 3 | 0 | 0 |
| ErrorModel | 6 | 6 | 0 | 0 |
| ConfigValidation | 4 | 3 | 1 | 0 |
| **Total** | **49** | **45 (92%)** | **4 (8%)** | **0 (0%)** |

### By Effort to Fix

#### Trivial (< 1 hour each)

| Fix | Specs Unblocked | Invariants Fixed |
|-----|----------------|------------------|
| Decide whether `audio_rate` belongs in the public config struct or should be removed from the TLA abstraction | ConfigValidation | AllFieldsValidated |

#### Small (< 1 day each)

No small TLA-conformance fixes remain from the CI-checked invariant set.

#### Medium (1-3 days each)

| Fix | Specs Unblocked | Invariants Fixed |
|-----|----------------|------------------|
| Serialize engine event scheduler queue | SaveStateTest | EventCountPreserved, EventDigestPreserved |

#### Large (post-Phase B device completeness)

| Fix | Specs Unblocked | Invariants Fixed |
|-----|----------------|------------------|
| Integrate functional library-mode PIC/event delivery beyond the current stub queue | PIC/Scheduler non-CI specs | Priority/timer delivery invariants |

---

## Non-CI Specs: Implementation Gaps

The 22 non-CI specs define requirements that the implementation should eventually satisfy. Key gaps identified from the device model and scheduler specs:

### Scheduler (Scheduler.tla, SchedulerMinimal.tla)

- **DeterministicSelection**: Spec requires tie-breaking by `tieKey`, not nondeterministic choice. Implementation uses DOSBox-X's native event system which does NOT guarantee deterministic tie-breaking. This is masked because the current test suite doesn't exercise simultaneous events.
- **EventsNotInPast**: Spec requires all events scheduled at `deadline >= now`. Not verified in implementation.

### PIC (PIC.tla)

- **MaskedIRQNotDelivered**: Spec requires masked IRQs never fire. The CPU bridge now calls `PIC_RunQueue()`, but the library-mode build links a stub PIC queue, so functional delivery remains unverified.
- **PriorityRespected**: Same issue — PIC priority only matters when functional PIC events are processed.

### Bus (Bus.tla, BusMinimal.tla)

- **MemRangesDisjoint**: Spec requires non-overlapping memory handler ranges. H6's caller memory read/write overflow path is fixed; broader device-range disjointness still needs subsystem-level verification.

### EmuKernel (EmuKernel.tla)

- **MonotonicTime**: Spec requires virtual time `now` only advances. Implementation `total_cycles` is monotonic, but `load_state` can rewind it (intentional). The spec's `Obs` function accounts for this via save/load semantics.

---

## Prioritized Implementation Roadmap

### Phase 1: Completed Quick Wins

1. `LIB_CHECK_THREAD()` in `dosbox_lib_get_context_ptr()` — fixes ThreadingMinimal
2. Remove `g_active_instance` fallback — fixes LifecycleMinimal + ErrorModel
3. `cpu_cycles` validation — fixes ConfigValidation
4. `MixerState` atomic producer/consumer synchronization — fixes PALMinimal
5. `text_input` transaction — fixes InputMinimal

**Result**: completed before this rebaseline.

### Phase 2: Completed Bridge & Capture Work

6. `in_step` guard on mutating APIs — fixes ReentrancyMinimal
7. Framebuffer sync from engine — fixes CaptureMinimal

**Result**: completed except engine event queue serialization.

### Phase 3: Completed Phase B/V5 Serialization Work

9. CPU GPR serialization
10. VGA hardware state serialization
11. RAM content serialization

**Result**: observation coverage improved; engine event scheduler serialization remains partial.

### Phase 4: Remaining PIC/Scheduler Integration

12. Replace or integrate the library-mode PIC queue stub so `PIC_RunQueue()` has functional delivery.
13. Serialize engine event queue state.
14. Deterministic event scheduler tie-breaking.

**Result**: Device model specs (PIC, Scheduler, EmuKernel) become testable and verifiable
