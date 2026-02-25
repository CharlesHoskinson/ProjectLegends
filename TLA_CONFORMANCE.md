# TLA+ Specification Conformance Analysis

Date: 2026-02-24
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

---

## 1. LifecycleMinimal.tla

**File:** `spec/tla/LifecycleMinimal.tla` (~250 states at MaxOperations=6)
**Implementation:** `legends_embed_api.cpp`, `dosbox_library.cpp`

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `AtMostOneInstance` | CONFORMANT | Atomic CAS at `legends_embed_api.cpp:807` enforces single instance |
| `MisuseSafe` | CONFORMANT | All misuse paths return error codes, never crash |
| `HandleConsistency` | **NON-CONFORMANT** | H5: `get_instance()` fallback to `g_active_instance` means `instance="CREATED"` but passing invalid handle still destroys it — spec requires `(instance="NONE") <=> (handle="NULL")` |
| `NoReentrantSuccess` | CONFORMANT | `in_step` flag at line 1053 blocks nested steps |
| `WrongThreadBlocked` | CONFORMANT | `LEGENDS_CHECK_THREAD()` macro returns `WRONG_THREAD` |
| `ConfigGated` | CONFORMANT | Invalid config checked before instance creation (lines 828-838) |

### Required Work

1. **Fix `HandleConsistency`**: Remove `g_active_instance` fallback in `get_instance()` (`legends_embed_api.cpp:949-957`). If the handle doesn't match, return `LEGENDS_ERR_NULL_HANDLE`. Effort: **Small**.

---

## 2. PALMinimal.tla

**File:** `spec/tla/PALMinimal.tla` (~200 states)
**Implementation:** PAL headers, `headless_stub.cpp`, `MixerState`

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `AudioPushModel` | CONFORMANT | Audio flows core→PAL only; headless stub is push model |
| `ThreadSafety` | **NON-CONFORMANT** | M3: `MixerState` has thread safety comments but no actual mutex/atomic synchronization |
| `AudioQueueBounded` | CONFORMANT | Queue has fixed capacity with drop-on-overflow semantics |
| `ComponentDependency` | CONFORMANT | PAL components initialize after context |
| `BackpressureNonNegative` | CONFORMANT | Dropped frame counter is unsigned |

### Required Work

1. **Fix `ThreadSafety`**: Add `std::mutex` or `std::atomic` guards to `MixerState` fields accessed from the audio callback thread. Effort: **Small**.

---

## 3. ThreadingMinimal.tla

**File:** `spec/tla/ThreadingMinimal.tla` (~2,000 states)
**Implementation:** `legends_embed_api.cpp`, `dosbox_library.cpp`

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `CoreSingleThreaded` | **PARTIAL** | Legends layer enforces via `LEGENDS_CHECK_THREAD()`. Engine layer: `dosbox_lib_get_context_ptr()` bypasses `LIB_CHECK_THREAD()` (M7) |
| `PALIsolation` | CONFORMANT | PAL threads use push-only model, never call core |
| `NoDataRaces` | **PARTIAL** | M3: `MixerState` has no synchronization; M7: context pointer accessible without thread check |
| `CallStackValid` | CONFORMANT | Guard clauses enforce valid call order |
| `WrongThreadBlocked` | **PARTIAL** | Enforced at legends layer; `dosbox_lib_get_context_ptr()` is the exception |
| `NoReentrantStep` | CONFORMANT | `in_step` flag blocks nested step calls |

### Required Work

1. **Fix `CoreSingleThreaded` / `WrongThreadBlocked`**: Add `LIB_CHECK_THREAD()` to `dosbox_lib_get_context_ptr()` (`dosbox_library.cpp:466`). Effort: **Trivial** — one line.
2. **Fix `NoDataRaces`**: Add synchronization to `MixerState` (same as PALMinimal ThreadSafety fix).

---

## 4. SaveStateTest.tla

**File:** `spec/tla/SaveStateTest.tla` (~30 states)
**Implementation:** `legends_embed_api.cpp:1587-2294`, `dosbox_library.cpp:508-1072`

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `ObservationPreserved` | **PARTIAL** | Round-trip works for serialized fields. CPU GPRs, VGA hardware state, and RAM are NOT serialized (H1). Obs(S) is incomplete. |
| `EventCountPreserved` | **PARTIAL** | Legends-layer event queue serialized. Engine-layer `PIC_RunQueue` event queue is NOT serialized. |
| `EventDigestPreserved` | **PARTIAL** | Same gap — engine event scheduler state not captured |
| `TimePreserved` | CONFORMANT | `total_cycles`, `emu_time_us`, `cycles_per_ms` all serialized |
| `IntegrityCheckPasses` | CONFORMANT | CRC32 computed after all data, verified before any mutation |
| `CorruptionDetected` | CONFORMANT | Load rejects CRC mismatch without modifying state |
| `PartialSaveSafe` | CONFORMANT | Four-phase commit: validate → engine load → stage locals → commit |

### Required Work

1. **Fix `ObservationPreserved`**: Serialize CPU GPRs (EAX-EDI, segment registers, EIP), VGA hardware state, and RAM contents. This is the Phase B serialization completion. Effort: **Medium-Large**.
2. **Fix `EventCountPreserved` / `EventDigestPreserved`**: Serialize the engine-layer event scheduler queue (PIC events, timer callbacks). Requires engine cooperation. Effort: **Medium**.

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
| `BackendIndependent` | **PARTIAL** | Capture reads from `frame_state`, not backend — but `frame_state` is initialized with a synthetic test pattern (`legends_embed_api.cpp:919-920`) and `sync_state_from_engine()` does not sync framebuffer (H8). So captures are backend-independent but also engine-independent (wrong content). |
| `FramebufferSizeConsistent` | CONFORMANT | Size = width * height * 3 |

### Required Work

1. **Fix `BackendIndependent` (real content)**: Wire `sync_state_from_engine()` to copy the actual framebuffer from the DOSBox-X engine into `frame_state`. Currently it only syncs timing and PIC. Effort: **Medium** — requires reading VGA render output through the engine bridge.

---

## 7. InputMinimal.tla

**File:** `spec/tla/InputMinimal.tla` (~300 states)
**Implementation:** `legends_embed_api.cpp` (key_event, mouse_event, text_input), `instance_state.h`

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `ScancodeValid` | CONFORMANT | AT Scancode Set 1 used throughout |
| `BufferNotCorrupted` | **NON-CONFORMANT** | M2: `legends_text_input()` can partially commit a multi-event character (shift-down queued, then queue full on key-down). Shift key stuck. |
| `E0PrefixCorrect` | CONFORMANT | Extended keys push 0xE0 then scancode |
| `InputDeterminism` | CONFORMANT | Monotonic `sequence` counter, FIFO drain order |
| `BufferBounded` | CONFORMANT | 320-event ring buffer, returns error on full |

### Required Work

1. **Fix `BufferNotCorrupted`**: Add transactional semantics to `legends_text_input()`. Before processing each character, check if enough queue slots exist for all its events (shift-down + key-down + key-up + shift-up = up to 4 events). If not, stop before that character and return `LEGENDS_ERR_BUFFER_TOO_SMALL`. Effort: **Small**.

---

## 8. ReentrancyMinimal.tla

**File:** `spec/tla/ReentrancyMinimal.tla` (~50 states)
**Implementation:** `legends_embed_api.cpp:1051-1059`

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `NoNestedStep` | CONFORMANT | `in_step` flag at line 1053, returns `REENTRANT_CALL` |
| `PhaseConsistent` | **PARTIAL** | Step functions transition phases correctly. But non-step API functions called from callbacks don't check `in_step`, so phase consistency isn't enforced for all API paths (M1). |
| `CallbackSafe` | **PARTIAL** | Callbacks during step can re-enter non-step API functions without detection |

### Required Work

1. **Fix `PhaseConsistent` / `CallbackSafe`**: Either (a) extend the `in_step` check to all API functions that mutate state (key_event, mouse_event, save_state, load_state, reset), or (b) add a broader `in_api_call` guard. Option (a) is more targeted. Effort: **Small**.

---

## 9. ErrorModel.tla

**File:** `spec/tla/ErrorModel.tla` (~500 states)
**Implementation:** `legends_embed_api.cpp` guard clause order

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `ErrorCodeDeterministic` | **PARTIAL** | Guard clause order in implementation matches spec priority chain. BUT H5 (destroy fallback) makes destroy non-deterministic for invalid handles — spec says DESTROY + NONE → OK (null handle no-op), but implementation destroys active instance on any non-null handle. |
| `SuccessRequiresValidState` | CONFORMANT | All core ops check instance via `get_instance()` |
| `ErrorCodesComplete` | CONFORMANT | All returned codes are in the defined 14+1 set |
| `NullHandleConsistent` | **NON-CONFORMANT** | H5 again: NULL_HANDLE should be returned when no instance exists, but invalid non-null handles bypass this check and destroy the real instance |
| `ReentrantCodeCorrect` | CONFORMANT | `REENTRANT_CALL` returned iff `in_step && op == STEP` |
| `WrongThreadCodeCorrect` | CONFORMANT | `WRONG_THREAD` returned iff caller is not owner thread |

### Required Work

1. **Fix `ErrorCodeDeterministic` / `NullHandleConsistent`**: Same fix as LifecycleMinimal HandleConsistency — remove `g_active_instance` fallback in `get_instance()`. Effort: **Small** (same fix as REQ-LC-003).

---

## 10. ConfigValidation.tla

**File:** `spec/tla/ConfigValidation.tla` (~20 states)
**Implementation:** `legends_embed_api.cpp:827-858`, `dosbox_library.cpp:196-222`

| Invariant | Rating | Evidence |
|-----------|--------|----------|
| `InvalidConfigBlocked` | **PARTIAL** | `struct_size` and `api_version` validated. But `cpu_cycles` accepts any value (including 0), and there is no `audio_rate` field in the config struct. Spec requires `cycles_per_ms ∈ {50,100,200}` and `audio_rate ∈ {11025,22050,44100}`. |
| `ValidConfigAccepted` | CONFORMANT | Valid struct_size + api_version → instance created |
| `VersionChecked` | CONFORMANT | Wrong version → `VERSION_MISMATCH` at line 834 |
| `AllFieldsValidated` | **NON-CONFORMANT** | `cpu_cycles` not range-checked; no `audio_rate` field exists; `memory_kb` not validated |

### Required Work

1. **Fix `InvalidConfigBlocked` / `AllFieldsValidated`**: Add validation for `cpu_cycles` (reject 0 or unreasonable values) in `legends_create()`. The TLA+ values `{50,100,200}` are abstract model constants — implementation should validate `cpu_cycles > 0` at minimum, and optionally enforce a reasonable range. Effort: **Trivial**.
2. **Consider audio_rate field**: The TLA+ spec models audio rate validation, but the config struct lacks this field. Either add the field and validate it, or update the TLA+ spec to reflect reality. Effort: **Small** (either direction).

---

## 11. APIContract.tla

**File:** `spec/tla/APIContract.tla` (~1,000 states)
**Implementation:** All source files

This is the composite specification that combines all 23 contract gates. Conformance follows from the individual specs:

| Gate Group | Rating | Blocking Issues |
|------------|--------|-----------------|
| Gates 2a-2c (Lifecycle/Config) | **PARTIAL** | HandleConsistency (H5), AllFieldsValidated (cpu_cycles) |
| Gates 4a-4c (Determinism/SaveState) | **PARTIAL** | ObservationPreserved (CPU GPRs, VGA, RAM not serialized) |
| Gates 5a-5c (Capture) | **PARTIAL** | BackendIndependent (framebuffer not synced from engine) |
| Gates 6a-6b (Input) | **PARTIAL** | BufferNotCorrupted (text_input partial commit) |
| Gates 7a-7d (PAL/Threading) | **PARTIAL** | ThreadSafety (MixerState), CoreSingleThreaded (get_context_ptr) |
| Gates 8a-8c (Threading/Reentrancy) | **PARTIAL** | PhaseConsistent, CallbackSafe (non-step reentrancy) |
| Gate: NoExitAbort | CONFORMANT | No `exit()` or `abort()` calls in API |
| Gate: NoStdout | CONFORMANT | All output via log callback |
| Gate: NoEnvironmentChange | CONFORMANT | No environment variable modification |
| Gate: VersionHandshake | CONFORMANT | Version checked at create |

---

## Conformance Summary

### By Specification

| Spec | Invariants | Conformant | Partial | Non-Conformant |
|------|-----------|------------|---------|----------------|
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

### By Effort to Fix

#### Trivial (< 1 hour each)

| Fix | Specs Unblocked | Invariants Fixed |
|-----|----------------|------------------|
| Add `LIB_CHECK_THREAD()` to `dosbox_lib_get_context_ptr()` | ThreadingMinimal | CoreSingleThreaded, WrongThreadBlocked |
| Add `cpu_cycles > 0` validation in `legends_create()` | ConfigValidation | InvalidConfigBlocked, AllFieldsValidated |

#### Small (< 1 day each)

| Fix | Specs Unblocked | Invariants Fixed |
|-----|----------------|------------------|
| Remove `g_active_instance` fallback in `get_instance()` | LifecycleMinimal, ErrorModel | HandleConsistency, NullHandleConsistent, ErrorCodeDeterministic |
| Add `std::mutex` to `MixerState` | PALMinimal, ThreadingMinimal | ThreadSafety, NoDataRaces |
| Add transactional semantics to `legends_text_input()` | InputMinimal | BufferNotCorrupted |
| Extend `in_step` guard to mutating API functions | ReentrancyMinimal | PhaseConsistent, CallbackSafe |

#### Medium (1-3 days each)

| Fix | Specs Unblocked | Invariants Fixed |
|-----|----------------|------------------|
| Wire framebuffer sync in `sync_state_from_engine()` | CaptureMinimal | BackendIndependent (real content) |
| Serialize engine event scheduler queue | SaveStateTest | EventCountPreserved, EventDigestPreserved |

#### Large (Phase B completion, 1-2 weeks)

| Fix | Specs Unblocked | Invariants Fixed |
|-----|----------------|------------------|
| Serialize CPU GPRs, VGA state, RAM | SaveStateTest | ObservationPreserved |

---

## Non-CI Specs: Implementation Gaps

The 22 non-CI specs define requirements that the implementation should eventually satisfy. Key gaps identified from the device model and scheduler specs:

### Scheduler (Scheduler.tla, SchedulerMinimal.tla)

- **DeterministicSelection**: Spec requires tie-breaking by `tieKey`, not nondeterministic choice. Implementation uses DOSBox-X's native event system which does NOT guarantee deterministic tie-breaking. This is masked because the current test suite doesn't exercise simultaneous events.
- **EventsNotInPast**: Spec requires all events scheduled at `deadline >= now`. Not verified in implementation.

### PIC (PIC.tla)

- **MaskedIRQNotDelivered**: Spec requires masked IRQs never fire. Implementation relies on DOSBox-X PIC model, which is correct when `PIC_RunQueue()` runs — but C2 (bridge skips PIC_RunQueue) means this invariant is **not testable** in the current execution model.
- **PriorityRespected**: Same issue — PIC priority only matters when PIC events are processed.

### Bus (Bus.tla, BusMinimal.tla)

- **MemRangesDisjoint**: Spec requires non-overlapping memory handler ranges. H6 (integer overflow in bounds checks) means the routing invariant can be bypassed with crafted addresses.

### EmuKernel (EmuKernel.tla)

- **MonotonicTime**: Spec requires virtual time `now` only advances. Implementation `total_cycles` is monotonic, but `load_state` can rewind it (intentional). The spec's `Obs` function accounts for this via save/load semantics.

---

## Prioritized Implementation Roadmap

### Phase 1: Quick Wins (unblock 5 specs, ~2 days)

1. `LIB_CHECK_THREAD()` in `dosbox_lib_get_context_ptr()` — fixes ThreadingMinimal
2. Remove `g_active_instance` fallback — fixes LifecycleMinimal + ErrorModel
3. `cpu_cycles` validation — fixes ConfigValidation
4. `MixerState` mutex — fixes PALMinimal
5. `text_input` transaction — fixes InputMinimal

**Result**: 5 specs fully CONFORMANT, 11 invariants fixed

### Phase 2: Bridge & Capture (~1 week)

6. `in_step` guard on mutating APIs — fixes ReentrancyMinimal
7. Framebuffer sync from engine — fixes CaptureMinimal
8. Engine event queue serialization — partially fixes SaveStateTest

**Result**: 3 more specs to full/near-full conformance

### Phase 3: Phase B Serialization (~2 weeks)

9. CPU GPR serialization
10. VGA hardware state serialization
11. RAM content serialization

**Result**: SaveStateTest fully CONFORMANT, Phase E unblocked

### Phase 4: PIC/Scheduler Integration (with C2 fix)

12. Add `PIC_RunQueue()` and `CPU_Check_NMI()` to CPU bridge
13. Deterministic event scheduler tie-breaking

**Result**: Device model specs (PIC, Scheduler, EmuKernel) become testable and verifiable
