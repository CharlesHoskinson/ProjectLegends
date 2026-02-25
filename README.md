# Project Legends

**Embeddable x86 Emulation Framework**

[![Build Status](https://img.shields.io/badge/build-passing-brightgreen)]()
[![License](https://img.shields.io/badge/license-GPL--2.0-blue)]()
[![C++ Standard](https://img.shields.io/badge/C%2B%2B-23-blue)]()
[![Tests](https://img.shields.io/badge/tests-1500%2B%20passing-brightgreen)]()
[![codecov](https://codecov.io/gh/CharlesHoskinson/projectLegends/graph/badge.svg)](https://codecov.io/gh/CharlesHoskinson/projectLegends)

---

## Overview

Project Legends is an embeddable x86 emulation framework built on a refactored DOSBox-X engine. It provides a C API for embedding DOS/x86 emulation into applications requiring deterministic execution and programmatic control.

Existing emulators are standalone applications. They spawn threads, use global state, call `exit()` on errors, and assume process ownership. This makes them unsuitable for embedding into larger systems where you need multiple instances, state serialization, or reproducible execution.

Project Legends treats the emulator as a library. The host application controls execution timing, input injection, and state capture. All mutable state lives in an explicit context structure.

**Capabilities:**

- Context-based state isolation (single instance per process in V1)
- Explicit memory model with per-context RAM and page handlers
- Deterministic stepping via `step_ms()` and `step_cycles()`
- Full state serialization with integrity verification
- Platform abstraction supporting headless, SDL2, and SDL3 backends
- Wasm sandbox support (headless Wasmtime/WASI target for sandboxed execution)
- Stable C ABI for FFI from Rust, Python, or other languages

---

## Architecture

```
                     ┌───────────────────┐
                     │  Host Application │
                     └─────────┬─────────┘
                               │ C ABI
                               ▼
┌──────────────────────────────────────────────────────────────┐
│                       legends_embed.h                        │
│          Lifecycle · Stepping · Capture · Input · State      │
└──────────────────────────────┬───────────────────────────────┘
                               │
               ┌───────────────┴───────────────┐
               ▼                               ▼
┌─────────────────────────┐     ┌─────────────────────────────┐
│      Legends Core       │     │           PAL               │
│                         │     │                             │
│  MachineContext         │     │  IWindow    IAudioSink      │
│  HandleRegistry         │     │  IContext   IHostClock      │
│  EventQueue             │     │  IInputSource               │
│                         │     │                             │
│  ┌───────────────────┐  │     │  Backends:                  │
│  │ DOSBox Library    │  │     │  Headless · SDL2 · SDL3     │
│  │ dosbox_lib_*()    │  │     └─────────────────────────────┘
│  └───────────────────┘  │
└────────────┬────────────┘
             │
             ▼
┌──────────────────────────────────────────────────────────────┐
│                    DOSBox-X Core Engine                      │
│                                                              │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐     │
│  │   CPU    │  │ Hardware │  │ DOS/BIOS │  │  Memory  │     │
│  │ x86 emu  │  │ PIC, PIT │  │ INT 21h  │  │  Paging  │     │
│  │ prot mode│  │ VGA, SB  │  │ FileSys  │  │  A20     │     │
│  └──────────┘  └──────────┘  └──────────┘  └──────────┘     │
└──────────────────────────────────────────────────────────────┘
```

---

## State Serialization

Save and load operations preserve the complete emulator state for deterministic replay.

### Format

```
┌─────────────────────────────────────────────────────────────┐
│ SaveStateHeader (64 bytes)                                  │
│   magic, version, total_size, checksum                      │
│   section offsets: time, cpu, pic, dma, events, input, frame│
│   engine_offset, engine_size                                │
├─────────────────────────────────────────────────────────────┤
│ Legends Layer State                                         │
│   TimeState, PIC shadow, DMA shadow, EventQueue             │
│   InputQueue, FrameState                                    │
├─────────────────────────────────────────────────────────────┤
│ Engine State (120 bytes)                                    │
│   Header, TimingState, PicState, KeyboardState              │
└─────────────────────────────────────────────────────────────┘
```

### Integrity

- CRC32 checksum over all data after header
- All section offsets validated against checksummed region
- Frame dimensions validated against maximum bounds (80×50)
- Engine state size verified at write time

### Determinism Invariant

```
Obs(Deserialize(Serialize(S))) = Obs(S)
```

Observable state after load equals observable state before save. This is verified by the TLA+ specification and integration tests.

---

## Quick Start

### Building

```bash
cmake -B build -G Ninja -DLEGENDS_BUILD_TESTS=ON
cmake --build build
ctest --test-dir build --output-on-failure
```

### Embedding

```c
#include <legends/legends_embed.h>

int main() {
    legends_handle handle;
    legends_config_t config = LEGENDS_CONFIG_INIT;

    legends_create(&config, &handle);

    // Run for 1 second
    for (int i = 0; i < 100; i++) {
        legends_step_ms(handle, 10, NULL);
    }

    // Save state
    size_t size;
    legends_save_state(handle, NULL, 0, &size);
    void* buffer = malloc(size);
    legends_save_state(handle, buffer, size, &size);

    // Continue execution
    legends_text_input(handle, "DIR\n");
    legends_step_ms(handle, 500, NULL);

    // Restore to checkpoint
    legends_load_state(handle, buffer, size);

    free(buffer);
    legends_destroy(handle);
    return 0;
}
```

---

## API Reference

### Lifecycle

| Function | Description |
|----------|-------------|
| `legends_create(config, handle_out)` | Create emulator instance |
| `legends_destroy(handle)` | Release instance and resources |
| `legends_reset(handle)` | Reset to initial state |
| `legends_get_api_version(major, minor, patch)` | Query library version |
| `legends_get_config(handle, config_out)` | Read active config |

### Stepping

| Function | Description |
|----------|-------------|
| `legends_step_ms(handle, ms, result)` | Advance by milliseconds |
| `legends_step_cycles(handle, cycles, result)` | Advance by CPU cycles |
| `legends_get_emu_time(handle, time_us)` | Query emulated time |
| `legends_get_total_cycles(handle, cycles)` | Query cycle counter |

### State Management

| Function | Description |
|----------|-------------|
| `legends_save_state(handle, buf, size, size_out)` | Serialize state |
| `legends_load_state(handle, buf, size)` | Restore state |
| `legends_get_state_hash(handle, hash_out)` | SHA-256 of observable state |
| `legends_verify_determinism(handle, cycles, result)` | Round-trip test |

### Input

| Function | Description |
|----------|-------------|
| `legends_key_event(handle, scancode, pressed)` | Inject key event |
| `legends_key_event_ext(handle, scancode, pressed, flags)` | Inject key event with modifier flags |
| `legends_text_input(handle, text)` | Type string |
| `legends_mouse_event(handle, dx, dy, buttons)` | Inject mouse event |

### Capture

| Function | Description |
|----------|-------------|
| `legends_capture_text(handle, cells, cols, rows)` | Read text mode screen |
| `legends_capture_rgb(handle, buf, stride, w, h)` | Read graphics as RGB24 |
| `legends_is_frame_dirty(handle, dirty_out)` | Check if display changed since last capture |
| `legends_get_cursor(handle, cursor_out)` | Get text cursor position and shape |

### Diagnostics

| Function | Description |
|----------|-------------|
| `legends_get_last_error(handle, buf, size)` | Get last error message string |
| `legends_set_log_callback(handle, callback, userdata)` | Register log message callback |

---

## Error Codes

| Code | Value | Description |
|------|-------|-------------|
| `LEGENDS_OK` | 0 | Success |
| `LEGENDS_ERR_NULL_HANDLE` | -1 | Null handle passed |
| `LEGENDS_ERR_NULL_POINTER` | -2 | Null pointer argument |
| `LEGENDS_ERR_NOT_INITIALIZED` | -4 | Instance not initialized |
| `LEGENDS_ERR_REENTRANT_CALL` | -5 | Step called from within callback |
| `LEGENDS_ERR_BUFFER_TOO_SMALL` | -6 | Buffer too small |
| `LEGENDS_ERR_INVALID_STATE` | -8 | Invalid state data |
| `LEGENDS_ERR_VERSION_MISMATCH` | -9 | Save state version mismatch |
| `LEGENDS_ERR_OUT_OF_MEMORY` | -11 | Allocation failed |
| `LEGENDS_ERR_WRONG_THREAD` | -14 | Called from wrong thread |

---

## Project Structure

```
ProjectLegends/
├── engine/                     # DOSBox-X core (GPL-2.0-only)
│   ├── include/dosbox/         # Engine headers
│   │   ├── dosbox_context.h    # Context structure
│   │   ├── dosbox_library.h    # Library mode API
│   │   └── engine_state.h      # Serialization format
│   ├── src/
│   │   ├── misc/dosbox_library.cpp  # Library implementation
│   │   └── misc/cpu_bridge.cpp      # CPU execution bridge
│   └── tests/
│
├── include/legends/            # Public API (GPL-2.0-only)
│   └── legends_embed.h
│
├── include/legends_ipc/        # IPC protocol headers (MIT)
│
├── src/legends/                # Legends layer (GPL-2.0-only)
│   └── legends_embed_api.cpp
│
├── src/legends_ipc/            # IPC serialization library (MIT)
│
├── src/legends_proxy/          # IPC proxy for legends_embed.h (MIT)
│
├── src/engine_host/            # Engine host process (GPL-2.0-only)
│
├── src/pal/                    # Platform backends (GPL-2.0-only)
│   ├── headless/
│   ├── sdl2/
│   └── sdl3/
│
├── tests/
│
├── spec/
│   ├── CONTRACT.md             # API contract
│   └── tla/                    # TLA+ specifications
│
├── wit/                       # WIT interface for Wasm component
│   └── legends-emulator.wit   # Core emulator WIT package
│
├── docs/
│   └── design/
│       └── GPL2_PROCESS_ISOLATION_DESIGN.md  # TDD-LIC-001
│
├── wasm.md                    # Wasm sandbox requirements
├── ARCHITECTURE.md
├── COPYING                     # GNU GPL v2 license text
├── LICENSE                     # Multi-component license overview
├── NOTICE                      # Copyright attributions + SPDX
├── TODO.md
└── README.md
```

---

## Platform Abstraction

| Interface | Purpose |
|-----------|---------|
| `IWindow` | Window management |
| `IContext` | Rendering context |
| `IAudioSink` | Push-based audio output |
| `IHostClock` | Wall clock for throttling |
| `IInputSource` | Event polling |

**Backends:** Headless (no dependencies), SDL2, SDL3

---

## Testing

```bash
# Build with tests
cmake -B build -G Ninja -DLEGENDS_BUILD_TESTS=ON
cmake --build build

# Run all tests
./build/legends_unit_tests

# Run specific test suites
./build/legends_unit_tests --gtest_filter="*SaveState*"
./build/legends_unit_tests --gtest_filter="*Determinism*"
```

---

## License

Project Legends is a multi-component project with two license scopes:

- **Engine & core** (`engine/`, `src/legends/`, `src/engine_host/`) — **GPL-2.0-only**, consistent with DOSBox-X
- **IPC protocol** (`include/legends_ipc/`, `src/legends_ipc/`) — **MIT**, enabling non-GPL applications to communicate with the engine host

Under the process isolation architecture, the GPL-licensed engine runs in a
separate process (`legends_engine_host`) and communicates with the application
shell via the MIT-licensed IPC protocol. See
[`docs/design/GPL2_PROCESS_ISOLATION_DESIGN.md`](docs/design/GPL2_PROCESS_ISOLATION_DESIGN.md)
for the full technical design.

SPDX expression: `GPL-2.0-only AND MIT`

- [`COPYING`](COPYING) — Full GNU GPL v2 license text
- [`LICENSE`](LICENSE) — Multi-component license overview
- [`NOTICE`](NOTICE) — Copyright attributions and third-party dependencies

---

## Acknowledgments

- DOSBox Team — Original DOSBox emulator
- DOSBox-X Team — Extended platform support

---

*Copyright 2026 Charles Hoskinson*
