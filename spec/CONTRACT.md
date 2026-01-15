# Project Legends Contract Specification

This document defines the enforceable contracts that make the architecture diagram into law.
Every statement here is verified by automated tests in `tests/unit/test_contract_gates.cpp`.

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

## Threading Model

**Core is single-threaded. PAL may have threads, but they never call core.**

```
┌─────────────────┐
│  Application    │  ← Single thread owns legends_handle
│  Thread         │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  legends_*()    │  ← All API calls from same thread
│  Functions      │
└────────┬────────┘
         │
         ├───────────────────┐
         ▼                   ▼
┌─────────────────┐  ┌─────────────────┐
│  Core Emulation │  │  PAL Backends   │
│  (single-thread)│  │  (may spawn     │
│                 │  │   threads)      │
└─────────────────┘  └────────┬────────┘
                              │
                              ▼
                     ┌─────────────────┐
                     │  Audio Callback │  ← Never calls core
                     │  (SDL2 only)    │     Only reads ring buffer
                     └─────────────────┘
```

### Rules

1. All `legends_*()` functions must be called from the same thread
2. Concurrent access to `legends_handle` is undefined behavior
3. PAL backend threads (audio callbacks, event loops) never invoke `legends_*()` functions
4. Audio uses push model: core pushes samples → PAL drains to device

---

## Input Encoding

**AT Scancode Set 1 with E0 prefix for extended keys.**

### Standard Keys

| Key | Scancode | Press | Release |
|-----|----------|-------|---------|
| A | 0x1E | `legends_key_event(h, 0x1E, 1)` | `legends_key_event(h, 0x1E, 0)` |
| B | 0x30 | `legends_key_event(h, 0x30, 1)` | `legends_key_event(h, 0x30, 0)` |
| Enter | 0x1C | `legends_key_event(h, 0x1C, 1)` | `legends_key_event(h, 0x1C, 0)` |
| Esc | 0x01 | `legends_key_event(h, 0x01, 1)` | `legends_key_event(h, 0x01, 0)` |

### Extended Keys (E0 prefix)

| Key | Base Code | Press | Release |
|-----|-----------|-------|---------|
| Right Arrow | 0x4D | `legends_key_event_ext(h, 0x4D, 1)` | `legends_key_event_ext(h, 0x4D, 0)` |
| Left Arrow | 0x4B | `legends_key_event_ext(h, 0x4B, 1)` | `legends_key_event_ext(h, 0x4B, 0)` |
| Up Arrow | 0x48 | `legends_key_event_ext(h, 0x48, 1)` | `legends_key_event_ext(h, 0x48, 0)` |
| Down Arrow | 0x50 | `legends_key_event_ext(h, 0x50, 1)` | `legends_key_event_ext(h, 0x50, 0)` |
| Insert | 0x52 | `legends_key_event_ext(h, 0x52, 1)` | `legends_key_event_ext(h, 0x52, 0)` |
| Delete | 0x53 | `legends_key_event_ext(h, 0x53, 1)` | `legends_key_event_ext(h, 0x53, 0)` |
| Home | 0x47 | `legends_key_event_ext(h, 0x47, 1)` | `legends_key_event_ext(h, 0x47, 0)` |
| End | 0x4F | `legends_key_event_ext(h, 0x4F, 1)` | `legends_key_event_ext(h, 0x4F, 0)` |

### Text Input

`legends_text_input()` handles UTF-8 → scancode translation:

```c
legends_text_input(handle, "Hello\n");  // Types "Hello" + Enter
```

Supported:
- ASCII printable characters (0x20-0x7E)
- Newline (\n) → Enter key
- Tab (\t) → Tab key

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

Color palette:
```
0 = Black       8 = Dark Gray
1 = Blue        9 = Light Blue
2 = Green      10 = Light Green
3 = Cyan       11 = Light Cyan
4 = Red        12 = Light Red
5 = Magenta    13 = Light Magenta
6 = Brown      14 = Yellow
7 = Light Gray 15 = White
```

### Codepage

Always CP437 (DOS Latin US). No codepage selection in v1.

### Page Selection

Always captures active page. No explicit page selection in v1.

### Dimensions

Text mode dimensions are reported via `legends_text_info_t`:

```c
legends_text_info_t info;
legends_capture_text(handle, NULL, 0, &count, &info);
// info.columns = 80, info.rows = 25 (default)
```

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

### Pitch

Pitch equals `width * 3`. No row padding.

### Resolution

Pre-scaler resolution. Text mode 80x25 renders as 640x400.

| Video Mode | Capture Resolution |
|------------|-------------------|
| Text 80x25 | 640x400 |
| Text 80x50 | 640x400 |
| Mode 13h (320x200) | 320x200 |
| Mode 12h (640x480) | 640x480 |

### Palette

VGA palette is applied. Output is true-color RGB24.

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

### Versioning

Version is incremented when:
- Field layout changes
- New required sections added
- Semantic changes to existing fields

Version check on load:
```c
if (header.version > SUPPORTED_VERSION)
    return LEGENDS_ERR_VERSION_MISMATCH;
```

### Buffer Sizing

Query required size before allocation:

```c
size_t required;
legends_save_state(handle, NULL, 0, &required);

uint8_t* buffer = malloc(required);
legends_save_state(handle, buffer, required, &actual);
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

Observable state after load equals observable state before save.

---

## Determinism Specification

### Guarantee

```
f(config, input_trace, step_schedule) → state_hash
```

Given identical:
- Configuration (`legends_config_t`)
- Input trace (sequence of `legends_key_event`, `legends_mouse_event`, etc.)
- Step schedule (sequence of `legends_step_ms`/`legends_step_cycles` calls)

The resulting state hash is identical.

### Requirements

1. `config.deterministic = 1`
2. No host time queries
3. No random number generation from host
4. Fixed CPU cycle timing

### Verification API

```c
int is_deterministic;
legends_verify_determinism(handle, 10000, &is_deterministic);
// Runs 10000 cycles twice, compares hashes
```

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

### Error Messages

```c
char buffer[256];
size_t length;
legends_get_last_error(handle, buffer, sizeof(buffer), &length);
```

### No Exceptions

Core never throws C++ exceptions across the C API boundary. All errors
are returned as error codes.

### No abort/exit

Core never calls `abort()`, `exit()`, or `E_Exit()` from `legends_*()` functions.
All error conditions return error codes.

---

## Audio Contract

### Push Model

Emulation produces samples. PAL consumes them.

```
Emulation → MIXER → ring buffer → IAudioSink::pushSamples() → device
```

### No Callback-Driven Emulation

SDL2 backend has audio callback, but it:
1. Only reads from ring buffer
2. Never calls any `legends_*()` function
3. Never advances emulation time

SDL3 backend has no callbacks at all (uses `SDL_AudioStream`).

### Backpressure

When audio queue is full:
- `pushSamples()` blocks or drops samples (configurable)
- Emulation timing remains authoritative
- Host audio may glitch; emulation does not slow down

### Sample Format

- 16-bit signed PCM
- Stereo interleaved (L, R, L, R, ...)
- Sample rates: 44100 Hz (default), 48000 Hz, 22050 Hz

---

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 1.0.0 | 2025-01 | Initial contract specification |

