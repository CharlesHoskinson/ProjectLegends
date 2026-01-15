# Project Legends Contract Specification

This document defines the enforceable contracts that make the architecture diagram into law.
Every statement here is verified by automated tests in `tests/unit/test_contract_gates.cpp`
and TLA+ specifications in `spec/tla/`.

---

## Contract Gates Summary

| Gate | Category | Description | Test | TLA+ |
|------|----------|-------------|------|------|
| 1a | Link/ABI | No `main`, no SDL symbols in core lib | `nm` verification | - |
| 1b | Link/ABI | `legends_embed.h` compiles as C and C++ | `test_legends_abi.c` | - |
| 1c | Link/ABI | ABI version handshake exists | `VersionHandshakeExists` | - |
| 2a | Lifecycle | create->step->destroy 100x | `CreateDestroyLoop100x` | `AtMostOneInstance` |
| 2b | Lifecycle | Misuse returns error, no crash | `MisuseSafe_*` | `MisuseSafe` |
| 2c | Lifecycle | Single-instance enforced | `SingleInstanceEnforced` | `AtMostOneInstance` |
| 3a | Side-Effects | No exit/abort reachable | All tests complete | - |
| 3b | Side-Effects | Log via callback only | `LogCallbackCapturesOutput` | - |
| 3c | Side-Effects | No chdir/getenv/putenv | Code audit | - |
| 4a | Determinism | State hash API exists | `StateHashAPIExists` | - |
| 4b | Determinism | Identical traces -> identical hash | `IdenticalTracesProduceIdenticalHash` | `TraceDeterminism` |
| 4c | Determinism | Save/load round-trip | `SaveLoadRoundTripPreservesState` | `ObservationPreserved` |
| 5a | Capture | Consistent dimensions | `TextCaptureConsistentDimensions` | - |
| 5b | Capture | RGB24 fixed format | `RGBCaptureFixedFormat` | - |
| 5c | Capture | Backend independent | `CaptureBackendIndependent` | - |
| 6a | Input | AT scancode set 1 | `ScancodeEncodingAT` | - |
| 6b | Input | Replay determinism | `InputReplayProducesIdenticalHash` | - |
| 7a | Audio | No callback into core | By design | `AudioPushModel` |
| 7b | Audio | Queue queryable | `AudioQueueQueryable` | `AudioQueueBounded` |
| 7c | Audio | Push model only | `PushModelNoCallback` | `AudioPushModel` |
| 8a | Threading | Core single-threaded | `CoreIsSingleThreaded` | `CoreSingleThreaded` |
| 8b | Threading | PAL threads never call core | By design | `PALIsolation` |

---

## Gate 1: Link/ABI Gates

### 1a) Core Library Exports No `main`, No SDL Symbols

```bash
# Verification command
nm -g libprojectlegends_core.a | grep -E "(main|SDL_)" && exit 1
```

The core library must be embeddable. It cannot:
- Export a `main()` function
- Depend on SDL directly (SDL is behind PAL)

**CI Job:** `contract-gates` runs symbol verification.

### 1b) `legends_embed.h` Compiles as Pure C

```bash
# Verification command
gcc -std=c11 -c test_legends_abi.c -I include/
```

The C API header must be usable from C code without C++ compiler.

**CI Job:** `abi-c-compile` verifies C11 compilation.

### 1c) ABI Version Handshake Exists

```c
legends_config_t config = LEGENDS_CONFIG_INIT;
config.api_version = 0xDEADBEEF;  // Wrong version

legends_handle handle;
legends_error_t err = legends_create(&config, &handle);
assert(err == LEGENDS_ERR_VERSION_MISMATCH);
```

Mismatched API versions are rejected at creation time.

**Test:** `ContractGate_LinkABI::VersionHandshakeExists`
**Test:** `ContractGate_LinkABI::VersionMismatchRejected`

---

## Gate 2: Lifecycle Correctness Gates

### 2a) Create/Step/Destroy Works 100x in Loop

```c
for (int i = 0; i < 100; i++) {
    legends_handle handle;
    legends_create(NULL, &handle);
    legends_step_ms(handle, 10, NULL);
    legends_destroy(handle);
}
```

No memory leaks, no crashes, no resource exhaustion.

**Test:** `ContractGate_Lifecycle::CreateDestroyLoop100x`
**CI Job:** `asan-lifecycle` runs under AddressSanitizer.
**TLA+:** `LifecycleMinimal.tla` - `HandleConsistency` invariant

### 2b) Misuse is Safe

API misuse returns defined error codes, never crashes:

```c
legends_step_ms(NULL, 100, NULL);  // Returns LEGENDS_ERR_NULL_HANDLE
legends_destroy(NULL);              // No-op, returns LEGENDS_OK
legends_destroy(handle);            // First destroy OK
legends_destroy(handle);            // Second destroy safe (handle invalid)
```

**Test:** `ContractGate_Lifecycle::MisuseSafe_StepWithoutCreate`
**Test:** `ContractGate_Lifecycle::MisuseSafe_DoubleDestroy`
**TLA+:** `LifecycleMinimal.tla` - `MisuseSafe` invariant

### 2c) Single-Instance Enforced

```c
legends_handle h1, h2;
legends_create(NULL, &h1);  // OK
legends_create(NULL, &h2);  // LEGENDS_ERR_ALREADY_CREATED
```

Rationale: DOSBox-X uses global state. Future versions may support multi-instance.

**Test:** `ContractGate_Lifecycle::SingleInstanceEnforced`
**TLA+:** `LifecycleMinimal.tla` - `AtMostOneInstance` invariant

---

## Gate 3: Side-Effect Bans

### 3a) No exit/abort Reachable

Core never calls `exit()`, `abort()`, or `E_Exit()`. All error conditions return error codes.

**Verification:** All tests complete without termination.

### 3b) No Direct stdout/stderr

All output goes through log callback:

```c
void log_callback(int level, const char* msg, void* userdata) {
    // Application handles logging
}
legends_set_log_callback(handle, log_callback, NULL);
```

**Test:** `ContractGate_SideEffects::LogCallbackCapturesOutput`

### 3c) No chdir/getenv/putenv

Core never accesses:
- Environment variables (`getenv`, `putenv`)
- Current working directory (`chdir`, `getcwd`)
- Command-line arguments

All configuration via `legends_config_t`.

**Verification:** Code audit, grep for banned functions.

---

## Gate 4: Determinism Gates

### 4a) State Hash API Exists

```c
uint8_t hash[32];
legends_get_state_hash(handle, hash);
```

Returns SHA-256 of observable state.

**Test:** `ContractGate_Determinism::StateHashAPIExists`

### 4b) Identical Traces Produce Identical Hash

**The Core Determinism Guarantee:**

```
f(config, input_trace, step_schedule) -> state_hash
```

```c
// Run 1
legends_create(&config, &h1);
legends_step_cycles(h1, 10000, NULL);
legends_key_event(h1, 0x1E, 1);
legends_step_cycles(h1, 10000, NULL);
legends_get_state_hash(h1, hash1);
legends_destroy(h1);

// Run 2 - identical
legends_create(&config, &h2);
legends_step_cycles(h2, 10000, NULL);
legends_key_event(h2, 0x1E, 1);
legends_step_cycles(h2, 10000, NULL);
legends_get_state_hash(h2, hash2);
legends_destroy(h2);

assert(memcmp(hash1, hash2, 32) == 0);
```

**Test:** `ContractGate_Determinism::IdenticalTracesProduceIdenticalHash`
**TLA+:** `Determinism.tla` - `TraceDeterminism` invariant

### 4c) Save/Load Round-Trip Preserves Observable State

**The Round-Trip Invariant:**

```
Obs(Deserialize(Serialize(S))) = Obs(S)
```

```c
legends_get_state_hash(handle, hash_before);
legends_save_state(handle, buffer, size, &size);
legends_step_cycles(handle, 50000, NULL);  // Mutate
legends_load_state(handle, buffer, size);
legends_get_state_hash(handle, hash_after);

assert(memcmp(hash_before, hash_after, 32) == 0);
```

**Test:** `ContractGate_Determinism::SaveLoadRoundTripPreservesState`
**TLA+:** `SaveStateTest.tla` - `ObservationPreserved` invariant

---

## Gate 5: Capture Correctness Gates

### 5a) Text Capture Returns Consistent Dimensions

```c
legends_text_info_t info1, info2;
legends_capture_text(handle, NULL, 0, &count1, &info1);
legends_step_ms(handle, 100, NULL);
legends_capture_text(handle, NULL, 0, &count2, &info2);

assert(info1.columns == info2.columns);
assert(info1.rows == info2.rows);
```

**Test:** `ContractGate_Capture::TextCaptureConsistentDimensions`

### 5b) RGB Capture Has Fixed Pixel Format

RGB24: 3 bytes per pixel (R, G, B), no padding.

```c
legends_capture_rgb(handle, NULL, 0, &size, &width, &height);
assert(size == width * height * 3);
assert(width == 640 && height == 400);  // Text mode default
```

**Test:** `ContractGate_Capture::RGBCaptureFixedFormat`

### 5c) Capture is Backend Independent

Same capture results regardless of PAL backend (Headless, SDL2, SDL3).

**Test:** `ContractGate_Capture::CaptureBackendIndependent`

---

## Gate 6: Input Correctness Gates

### 6a) Scancode Encoding is AT Set 1

Standard keys use AT scancode set 1:

| Key | Scancode | API Call |
|-----|----------|----------|
| A | 0x1E | `legends_key_event(h, 0x1E, 1/0)` |
| B | 0x30 | `legends_key_event(h, 0x30, 1/0)` |
| Enter | 0x1C | `legends_key_event(h, 0x1C, 1/0)` |
| Esc | 0x01 | `legends_key_event(h, 0x01, 1/0)` |

Extended keys use E0 prefix:

| Key | Base | API Call |
|-----|------|----------|
| Right Arrow | 0x4D | `legends_key_event_ext(h, 0x4D, 1/0)` |
| Left Arrow | 0x4B | `legends_key_event_ext(h, 0x4B, 1/0)` |
| Insert | 0x52 | `legends_key_event_ext(h, 0x52, 1/0)` |
| Delete | 0x53 | `legends_key_event_ext(h, 0x53, 1/0)` |

**Test:** `ContractGate_Input::ScancodeEncodingAT`

### 6b) Input Replay Produces Identical Hash

```c
auto run_trace = []() {
    legends_create(&config, &h);
    legends_step_cycles(h, 5000, NULL);
    legends_key_event(h, 0x1E, 1);
    legends_step_cycles(h, 1000, NULL);
    legends_key_event(h, 0x1E, 0);
    legends_step_cycles(h, 5000, NULL);
    legends_get_state_hash(h, hash);
    legends_destroy(h);
    return hash;
};

assert(run_trace() == run_trace());
```

**Test:** `ContractGate_Input::InputReplayProducesIdenticalHash`

---

## Gate 7: Audio Gates

### 7a) Core Never Invoked from Audio Callback Thread

**The Audio Push Model:**

```
Emulation -> MIXER -> ring buffer -> IAudioSink::pushSamples() -> device
```

Audio callbacks (SDL2) only read from ring buffer. They never call `legends_*()`.
SDL3 has no callbacks at all (uses `SDL_AudioStream`).

**TLA+:** `PALMinimal.tla` - `AudioPushModel` invariant:
```
currentThread = "AudioCallback" => lastCaller # "Core"
```

### 7b) Audio Queue is Queryable

```c
auto sink = pal::Platform::createAudioSink();
sink->open(config);
uint32_t queued = sink->getQueuedFrames();
```

**Test:** `ContractGate_Audio::AudioQueueQueryable`
**TLA+:** `PALMinimal.tla` - `AudioQueueBounded` invariant

### 7c) Push Model Only

```c
std::vector<int16_t> samples(882, 0);
sink->pushSamples(samples.data(), 441);  // Push is the only API
```

No callback registration. Emulation drives audio timing.

**Test:** `ContractGate_Audio::PushModelNoCallback`

---

## Gate 8: Threading Model Gates

### 8a) Core is Single-Threaded

```
┌─────────────────┐
│  Application    │  <- Single thread owns legends_handle
│  Thread         │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  legends_*()    │  <- All API calls from same thread
│  Functions      │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  Core Emulation │  <- Single-threaded execution
└─────────────────┘
```

Concurrent access to `legends_handle` is undefined behavior.

**Test:** `ContractGate_Threading::CoreIsSingleThreaded`
**TLA+:** `ThreadingMinimal.tla` - `CoreSingleThreaded` invariant:
```
coreOwner \in {"None", "Main"}
```

### 8b) PAL Threads Never Call Core

```
         ┌─────────────────┐
         │  PAL Backends   │
         │  (may spawn     │
         │   threads)      │
         └────────┬────────┘
                  │
                  ▼
         ┌─────────────────┐
         │  Audio Callback │  <- Never calls core
         │  (SDL2 only)    │     Only reads ring buffer
         └─────────────────┘
```

PAL backend threads (audio callbacks, event loops) never invoke `legends_*()` functions.

**TLA+:** `ThreadingMinimal.tla` - `PALIsolation` invariant:
```
\A t \in palThreads : t # coreOwner
```

---

## Instance Model

**v1: Single-instance-per-process**

```c
legends_handle handle1, handle2;
legends_create(NULL, &handle1);  // OK
legends_create(NULL, &handle2);  // LEGENDS_ERR_ALREADY_CREATED
```

Rationale: DOSBox-X uses global state internally. Future versions may support
multi-instance once globals are eliminated.

---

## Config Source

**No argv parsing in core. Config passed via `legends_create()`.**

```c
legends_config_t config = LEGENDS_CONFIG_INIT;
config.memory_kb = 1024;
config.deterministic = 1;
legends_create(&config, &handle);
```

The embedding application is responsible for:
- Command-line parsing
- Config file loading
- Environment variable handling

Core never calls `getenv()`, `chdir()`, or reads argv.

---

## Text Capture Specification

### Format

```c
typedef struct {
    uint8_t character;   // CP437 codepoint
    uint8_t attribute;   // VGA text attribute
} legends_text_cell_t;
```

### Attribute Byte

```
Bit 7: Blink (if enabled) or high-intensity background
Bits 6-4: Background color (0-7)
Bits 3-0: Foreground color (0-15)
```

### Codepage

Always CP437 (DOS Latin US). No codepage selection in v1.

### Dimensions

Standard modes:
- 80x25 (default)
- 80x43 (EGA)
- 80x50 (VGA)
- 40x25 (CGA)

---

## RGB Capture Specification

### Format

RGB24: 3 bytes per pixel (R, G, B), no padding.

```c
size_t size;
uint16_t width, height;
legends_capture_rgb(handle, NULL, 0, &size, &width, &height);
// size = width * height * 3
```

### Resolution

Pre-scaler resolution:

| Video Mode | Capture Resolution |
|------------|-------------------|
| Text 80x25 | 640x400 |
| Text 80x50 | 640x400 |
| Mode 13h (320x200) | 320x200 |
| Mode 12h (640x480) | 640x480 |

---

## Save State Specification

### Header Format

```c
struct SaveStateHeader {
    uint32_t magic;        // 0x53584244 ("DBXS")
    uint32_t version;      // Format version
    uint32_t total_size;   // Total bytes including header
    uint32_t flags;        // Reserved
    uint8_t  hash[32];     // SHA-256 of payload
};
```

### Completeness Guarantee

Save state includes all observable state:

1. **CPU**: All registers, flags, mode, instruction pointer
2. **Memory**: All RAM (conventional, EMS, XMS, UMB)
3. **PIC**: IRR, IMR, ISR for master and slave
4. **PIT**: All channel counters, modes, latches
5. **DMA**: All channel state
6. **VGA**: All registers, VRAM, palette
7. **Keyboard**: Buffer contents, LED state
8. **Event Queue**: All pending timer/interrupt events

### Round-Trip Invariant (TLA+)

```
Obs(Deserialize(Serialize(S))) = Obs(S)
```

Verified by `SaveStateTest.tla` with TLC model checking.

---

## Error Handling

### Error Codes

| Code | Value | Meaning |
|------|-------|---------|
| `LEGENDS_OK` | 0 | Success |
| `LEGENDS_ERR_NULL_HANDLE` | -1 | Handle is NULL |
| `LEGENDS_ERR_NULL_POINTER` | -2 | Required pointer is NULL |
| `LEGENDS_ERR_ALREADY_CREATED` | -3 | Instance already exists |
| `LEGENDS_ERR_NOT_INITIALIZED` | -4 | Not initialized |
| `LEGENDS_ERR_ALREADY_RUNNING` | -5 | Already running |
| `LEGENDS_ERR_BUFFER_TOO_SMALL` | -6 | Buffer too small |
| `LEGENDS_ERR_INVALID_CONFIG` | -7 | Invalid configuration |
| `LEGENDS_ERR_INVALID_STATE` | -8 | Invalid save state |
| `LEGENDS_ERR_VERSION_MISMATCH` | -9 | API version mismatch |
| `LEGENDS_ERR_IO_FAILED` | -10 | I/O operation failed |
| `LEGENDS_ERR_OUT_OF_MEMORY` | -11 | Memory allocation failed |
| `LEGENDS_ERR_NOT_SUPPORTED` | -12 | Operation not supported |
| `LEGENDS_ERR_INTERNAL` | -13 | Internal error |

### No Exceptions

Core never throws C++ exceptions across the C API boundary. All errors
are returned as error codes.

### No abort/exit

Core never calls `abort()`, `exit()`, or `E_Exit()` from `legends_*()` functions.
All error conditions return error codes.

---

## CI Enforcement

### Contract Gate Jobs

| Job | Enforcement |
|-----|-------------|
| `contract-gates` | Run all 22 gate tests |
| `asan-lifecycle` | 100x create/destroy under ASan |
| `abi-c-compile` | C11 compilation verification |
| `sdl-firewall` | No SDL headers outside `src/pal/` |

### Symbol Verification

```yaml
- name: Verify no SDL symbols in core
  run: |
    nm -g build/lib/libprojectlegends_core.a | grep "SDL_" && exit 1 || true

- name: Verify no main in core
  run: |
    nm -g build/lib/libprojectlegends_core.a | grep " T main" && exit 1 || true
```

---

## TLA+ Verification

All contract gates with formal specifications are verified by TLC model checking:

| Specification | States | Result |
|--------------|--------|--------|
| `LifecycleMinimal.tla` | 85 | PASSED |
| `PALMinimal.tla` | 99 | PASSED |
| `ThreadingMinimal.tla` | 1,474 | PASSED |
| `SaveStateTest.tla` | 8 | PASSED |

See [`VERIFICATION_REPORT.md`](VERIFICATION_REPORT.md) for details.

---

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 1.0.0 | 2025-01 | Initial contract specification |
| 1.1.0 | 2025-01 | Added 22 contract gates, TLA+ verification |
