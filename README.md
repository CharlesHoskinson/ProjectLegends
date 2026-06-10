# Project Legends

**Embeddable x86 Emulation Framework**

[![Build Status](https://img.shields.io/badge/build-passing-brightgreen)]()
[![License](https://img.shields.io/badge/license-GPL--2.0-blue)]()
[![C++ Standard](https://img.shields.io/badge/C%2B%2B-23-blue)]()
[![Tests](https://github.com/CharlesHoskinson/projectLegends/actions/workflows/ci.yml/badge.svg)](https://github.com/CharlesHoskinson/projectLegends/actions/workflows/ci.yml)
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
- Planned Wasm sandbox support (headless Wasmtime/WASI target for sandboxed execution)
- Stable C ABI for FFI from Rust, Python, or other languages

---

## Architecture

```
Graphify audit snapshot: 39,172 raw nodes, 818,069 raw edges,
5,640 ProjectLegends enrichment nodes, 8,010 enrichment links.

+---------------------------+        +-----------------------------+
| External embedders        |        | Project Legends app shell   |
| C / Rust / Python / tests |        | UI, config, save, AI, PAL   |
+-------------+-------------+        +--------------+--------------+
              | C ABI                               | RuntimeHost calls
              |                                     | (52 app call sites)
              v                                     v
+------------------------------------------------------------------+
| Public runtime surface                                            |
| include/legends/legends_embed.h: 50 legends_* C APIs              |
| src/app/runtime_host.*: 32 RuntimeHost methods                    |
+------------------------------+-----------------------------------+
                               |
        +----------------------+----------------------+
        |                                             |
        v                                             v
+-------------------------------+       +-------------------------------+
| In-process runtime            |       | IPC/proxy runtime             |
| InProcessEngineRuntime        |       | IpcEngineRuntime              |
| direct legends_* dispatch     |       | legends_proxy/proxy_api.cpp   |
+---------------+---------------+       +---------------+---------------+
                |                                       |
                |                                       v
                |                       +-------------------------------+
                |                       | legends_ipc message layer     |
                |                       | 108 msg types, 89 structs     |
                |                       +---------------+---------------+
                |                                       |
                |                                       v
                |                       +-------------------------------+
                |                       | engine_host dispatcher        |
                |                       | 43 dispatcher cases           |
                |                       +---------------+---------------+
                |                                       |
                +-----------------------+---------------+
                                        |
                                        v
+------------------------------------------------------------------+
| Legends core                                                      |
| src/legends/legends_embed_api.cpp                                 |
| MachineContext, HandleRegistry, EventQueue, save/load, capture,   |
| determinism, input, audio, MIDI, printer, IPX, Glide, PC-98       |
+------------------------------+-----------------------------------+
                               |
                               v
+------------------------------------------------------------------+
| DOSBox-X engine bridge                                            |
| dosbox_lib_*(), CPU, memory, VGA, PIT/PIC, DMA, DOS/BIOS, devices |
+------------------------------------------------------------------+

+-------------------------------+       +-------------------------------+
| Platform Abstraction Layer    |       | Quality and architecture gates|
| Headless, SDL2, SDL3          |       | OpenSpec, Graphify, CMake DAG |
| Window, context, audio, input |       | capability truth, CI, tests   |
+-------------------------------+       +-------------------------------+

RuntimeHost bypass invariant:
  Application may call legends_create and legends_destroy directly for
  lifecycle ownership. All other app-layer legends_* calls must route
  through RuntimeHost and are checked by Graphify.
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

<!-- BEGIN GENERATED: legends-api-table -->
Generated from `include/legends/legends_embed.h` (50 `LEGENDS_API` functions).

| Function | Description |
|----------|-------------|
| `legends_get_api_version` | Get API version. |
| `legends_create` | Create emulator instance. |
| `legends_destroy` | Destroy emulator instance. |
| `legends_force_destroy` | Force-destroy the active instance (test cleanup). |
| `legends_reset` | Soft reset the emulator. |
| `legends_get_config` | Get current configuration. |
| `legends_step_ms` | Step emulation by milliseconds of emulated time. |
| `legends_step_cycles` | Step emulation by exact CPU cycles. |
| `legends_get_emu_time` | Get current emulated time. |
| `legends_get_total_cycles` | Get total CPU cycles executed since creation/reset. |
| `legends_capture_text` | Capture text-mode screen. |
| `legends_capture_rgb` | Capture graphics framebuffer as RGB24. |
| `legends_is_frame_dirty` | Check if framebuffer changed since last capture. |
| `legends_get_cursor` | Get cursor position. |
| `legends_key_event` | Inject keyboard scancode (Set 1 / AT scancodes). |
| `legends_key_event_ext` | Inject extended scancode (E0-prefixed keys). |
| `legends_text_input` | Type UTF-8 text string (convenience wrapper). |
| `legends_mouse_event` | Inject mouse movement and button event. |
| `legends_capture_audio` | Capture audio samples from the emulator. |
| `legends_is_audio_active` | Check if audio subsystem is active. |
| `legends_save_state` | Save complete machine state. |
| `legends_load_state` | Load machine state from buffer. |
| `legends_get_state_hash` | Get SHA-256 hash of current machine state. |
| `legends_verify_determinism` | Verify determinism via round-trip test. |
| `legends_get_last_error` | Get human-readable error message for last error. |
| `legends_mount_drive` | Mount a host directory or image file to a DOS drive letter. |
| `legends_unmount_drive` | Unmount a DOS drive letter. |
| `legends_start_video_capture` | Start video capture to an AVI file. |
| `legends_stop_video_capture` | Stop video capture and finalize the AVI file. |
| `legends_is_video_capturing` | Check if video capture is active. |
| `legends_joystick_event` | Inject joystick axis + button event. |
| `legends_midi_set_device` | Set MIDI output device type. |
| `legends_midi_set_soundfont` | Set SoundFont path for FluidSynth. |
| `legends_midi_set_romdir` | Set ROM directory for MT-32 emulation. |
| `legends_capture_midi_audio` | Capture MIDI synthesizer audio. |
| `legends_printer_set_output` | Set printer output file path. |
| `legends_printer_is_active` | Check if printer is active (has pending data). |
| `legends_printer_flush` | Flush printer buffer to output file. |
| `legends_set_ttf_font` | Set TrueType font for text mode rendering. |
| `legends_ipx_enable` | Enable or disable IPX networking. |
| `legends_ipx_connect` | Connect to an IPX server. |
| `legends_ipx_disconnect` | Disconnect from IPX server. |
| `legends_ipx_is_connected` | Check if connected to IPX server. |
| `legends_glide_enable` | Enable or disable 3dfx Glide emulation. |
| `legends_glide_set_resolution` | Set Glide rendering resolution. |
| `legends_set_machine_pc98` | Enable or disable NEC PC-98 machine mode. |
| `legends_is_pc98_mode` | Check if PC-98 mode is active. |
| `legends_set_log_callback` | Set log callback for debug output. |
| `legends_register_event_callback` | Register an event callback. |
| `legends_has_capability` | Query whether a named capability is available. |
<!-- END GENERATED: legends-api-table -->

## Error Codes

<!-- BEGIN GENERATED: legends-error-table -->
Generated from `include/legends/legends_embed.h` (15 public status codes).

| Code | Value | Description |
|------|-------|-------------|
| `LEGENDS_OK` | 0 | Success |
| `LEGENDS_ERR_NULL_HANDLE` | -1 | Null handle passed |
| `LEGENDS_ERR_NULL_POINTER` | -2 | Null pointer argument |
| `LEGENDS_ERR_ALREADY_CREATED` | -3 | Single instance violation |
| `LEGENDS_ERR_NOT_INITIALIZED` | -4 | Instance not initialized |
| `LEGENDS_ERR_REENTRANT_CALL` | -5 | Step called from within callback |
| `LEGENDS_ERR_BUFFER_TOO_SMALL` | -6 | Buffer too small |
| `LEGENDS_ERR_INVALID_CONFIG` | -7 | Invalid configuration |
| `LEGENDS_ERR_INVALID_STATE` | -8 | Invalid state data |
| `LEGENDS_ERR_VERSION_MISMATCH` | -9 | API or save-state version mismatch |
| `LEGENDS_ERR_IO_FAILED` | -10 | I/O operation failed |
| `LEGENDS_ERR_OUT_OF_MEMORY` | -11 | Allocation failed |
| `LEGENDS_ERR_NOT_SUPPORTED` | -12 | Operation not supported |
| `LEGENDS_ERR_INTERNAL` | -13 | Internal error |
| `LEGENDS_ERR_WRONG_THREAD` | -14 | Called from non-owner thread |
<!-- END GENERATED: legends-error-table -->

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
├── docs/
│   └── design/
│       └── GPL2_PROCESS_ISOLATION_DESIGN.md  # TDD-LIC-001
│
├── ARCHITECTURE.md
├── COPYING                     # GNU GPL v2 license text
├── LICENSE                     # Multi-component license overview
├── NOTICE                      # Copyright attributions + SPDX
├── TODO.md
└── README.md
```

Planned Wasm artifacts are not present at HEAD: `git log --all -- wasm.md
"wit/legends-emulator.wit"` returns no history for `wasm.md` or the WIT file.
The Wasm design remains tracked in [ARCHITECTURE.md](ARCHITECTURE.md).

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
