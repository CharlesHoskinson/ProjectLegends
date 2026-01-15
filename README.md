# Project Legends

**A Modern Embeddable x86 Emulation Framework for AI-Driven Computing**

[![Build Status](https://img.shields.io/badge/build-passing-brightgreen)]()
[![License](https://img.shields.io/badge/license-GPL--2.0-blue)]()
[![C++ Standard](https://img.shields.io/badge/C%2B%2B-23-blue)]()
[![Tests](https://img.shields.io/badge/tests-4000%2B%20passing-brightgreen)]()
[![TLA+ Verified](https://img.shields.io/badge/TLA%2B-verified-green)]()

---

## Overview

Project Legends is a modernized, embeddable x86 emulation framework designed for deterministic execution and AI integration. Built on a fully refactored DOSBox-X engine, it provides a clean C API boundary for embedding DOS/x86 emulation into modern applications.

**Key Features:**

- **Deterministic Execution**: Bit-perfect reproducibility: `f(config, trace, schedule) -> hash`
- **LLM Integration**: Structured I/O optimized for language model interaction
- **Vision Model Support**: Screen capture with semantic annotations (COCO/YOLO export)
- **Platform Abstraction**: Clean separation from SDL2/SDL3 via PAL layer
- **Formal Verification**: TLA+ specifications with TLC model checking
- **Contract Gates**: 23 mechanically enforceable architectural invariants
- **Library-First Design**: No threads spawned, no globals leaked, host controls everything

---

## Engine Architecture

The engine is a fully refactored DOSBox-X core (~900k lines) transformed into an embeddable library:

```
┌─────────────────────────────────────────────────────────────────────────────────────┐
│                          Host Application (Rust/Python/C++)                          │
│                          LLM Agents, Game Bots, Testing Harnesses                    │
└─────────────────────────────────────────────────────────────────────────────────────┘
                                            │
                                            ▼ (Stable C ABI - 23 Contract Gates)
┌─────────────────────────────────────────────────────────────────────────────────────┐
│                              legends_embed.h (C API Boundary)                        │
│    Lifecycle │ Stepping │ Capture │ Input │ Save/Load │ LLM │ Vision                │
└─────────────────────────────────────────────────────────────────────────────────────┘
                                            │
              ┌─────────────────────────────┴─────────────────────────────┐
              ▼                                                           ▼
┌───────────────────────────────────────┐     ┌───────────────────────────────────────┐
│         AIBox Layer (C++23)           │     │    Platform Abstraction Layer (PAL)   │
│  ┌─────────────┐  ┌─────────────┐     │     │  ┌─────────────────────────────────┐  │
│  │ FFI Core    │  │ FFI LLM     │     │     │  │ IWindow, IContext, IAudioSink  │  │
│  │ FFI Vision  │  │ FFI Events  │     │     │  │ IHostClock, IInputSource       │  │
│  ├─────────────┤  ├─────────────┤     │     │  └─────────────────────────────────┘  │
│  │DOSBoxContext│  │HandleRegistry│    │     │        │         │         │          │
│  │ContextGuard │  │ EventBus    │     │     │   Headless    SDL2      SDL3          │
│  └─────────────┘  └─────────────┘     │     └───────────────────────────────────────┘
└───────────────────────────────────────┘
                    │
                    ▼ (Context-Based State - No Leaked Globals)
┌─────────────────────────────────────────────────────────────────────────────────────┐
│                     Refactored DOSBox-X Core (900k lines)                            │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐                 │
│  │     CPU     │  │   Hardware  │  │  DOS/BIOS   │  │    GUI      │                 │
│  │ x86 decode  │  │ PIC,PIT,DMA │  │ INT 21h/10h │  │ Menu system │                 │
│  │ Protected   │  │ VGA, SB16  │  │ File system │  │ Mapper      │                 │
│  └─────────────┘  └─────────────┘  └─────────────┘  └─────────────┘                 │
└─────────────────────────────────────────────────────────────────────────────────────┘
```

### Global State Migration

The original DOSBox-X used extensive global variables. Over 21 PRs, these have been systematically migrated to `DOSBoxContext`:

| Status | Count | Description |
|--------|-------|-------------|
| **Migrated** | 49 | Moved to DOSBoxContext (74%) |
| **Pending** | 17 | Remaining for multi-instance (26%) |
| **Total** | 66 | Tracked in `globals_registry.yaml` |

The `globals_registry.yaml` file tracks every global with:
- Migration status (pending → in_progress → migrated)
- Target context location
- PR that performed migration
- Determinism relevance flag

This enables CI to prevent regressions during the migration.

### Engine Statistics

| Metric | Value |
|--------|-------|
| Source files | 1,139 |
| Lines of code | ~1.1M |
| New AIBox layer | ~47k lines |
| Engine tests | 2,493 |
| Embedding tests | 1,533 |
| **Total tests** | **4,000+** |

---

## FFI Modules

The engine exposes four FFI modules for host integration:

### ffi_core.h - Lifecycle and Memory

```c
aibox_handle_t aibox_create(const char* config);
int aibox_init(aibox_handle_t handle);
int aibox_step(aibox_handle_t handle, uint32_t ms);
int aibox_destroy(aibox_handle_t handle);
int aibox_memory_read(aibox_handle_t h, uint32_t addr, void* buf, size_t len);
int aibox_memory_write(aibox_handle_t h, uint32_t addr, const void* buf, size_t len);
```

### ffi_llm.h - LLM Integration

```c
int aibox_llm_get_frame(aibox_handle_t h, int format, char* buf, size_t len, size_t* out);
int aibox_llm_execute_batch(aibox_handle_t h, const char* json_actions);
int aibox_llm_type(aibox_handle_t h, const char* text, uint32_t flags);
int aibox_llm_estimate_tokens(aibox_handle_t h, size_t* count);
```

### ffi_vision.h - Screenshot and Overlays

```c
int aibox_vision_capture_rgb(aibox_handle_t h, uint8_t* buf, size_t len, uint16_t* w, uint16_t* h);
int aibox_vision_add_overlay(aibox_handle_t h, const aibox_bbox_t* bbox);
int aibox_vision_export_coco(aibox_handle_t h, char* json, size_t len);
int aibox_vision_export_yolo(aibox_handle_t h, char* txt, size_t len);
```

### ffi_events.h - Event System

```c
int aibox_event_subscribe(aibox_handle_t h, int event_type, aibox_callback_t cb);
int aibox_event_unsubscribe(aibox_handle_t h, int subscription_id);
int aibox_event_poll(aibox_handle_t h);
```

---

## Contract Gates

The architecture is enforced by 23 mechanically verifiable gates:

| Category | Gates | Enforcement |
|----------|-------|-------------|
| **Link/ABI** | 1a-1c | Symbol verification, C compilation, version handshake |
| **Lifecycle** | 2a-2c | 100x create/destroy loop, misuse safety, single-instance |
| **Side-Effects** | 3a-3c | No exit/abort, log callback routing, no env access |
| **Determinism** | 4a-4c | State hash API, trace reproducibility, round-trip preservation |
| **Capture** | 5a-5c | Consistent dimensions, RGB24 format, backend independence |
| **Input** | 6a-6b | AT scancode set 1, replay determinism |
| **Audio** | 7a-7c | Push model, queue queryable, no callback into core |
| **Threading** | 8a-8c | Single-threaded core, PAL isolation, wrong thread returns error |

See [`spec/CONTRACT.md`](spec/CONTRACT.md) for complete specification.

---

## Key Invariants (TLA+ Verified)

> **"TLA+ Verified" badge scope:** TLA+ verifies the lifecycle, threading, audio, and save/load invariants defined in [`spec/CONTRACT.md`](spec/CONTRACT.md). It does not verify full x86 instruction semantics.

### Determinism
```
f(config, input_trace, step_schedule) -> state_hash
```

### Round-Trip Preservation
```
Obs(Deserialize(Serialize(S))) = Obs(S)
```

### Thread Isolation
```
coreOwner in {"None", "Main"} AND forall t in palThreads: t != coreOwner
```

| Specification | States | Status |
|--------------|--------|--------|
| `LifecycleMinimal.tla` | 85 | PASSED |
| `PALMinimal.tla` | 99 | PASSED |
| `ThreadingMinimal.tla` | 1,474 | PASSED |
| `SaveStateTest.tla` | 8 | PASSED |

---

## Quick Start

### Building

```bash
# Configure and build
cmake -B build -G Ninja -DLEGENDS_BUILD_TESTS=ON
cmake --build build

# Run tests
ctest --test-dir build --output-on-failure

# Build with SDL2 backend
cmake -B build -G Ninja -DPAL_BACKEND_SDL2=ON
cmake --build build
```

### Embedding Example

```c
#include <legends/legends_embed.h>

#define CHECK(call) do { if ((call) != LEGENDS_OK) return 1; } while(0)

int main() {
    legends_handle handle;
    legends_config_t config = LEGENDS_CONFIG_INIT;
    config.deterministic = 1;

    CHECK(legends_create(&config, &handle));

    // Run for 1 second
    for (int i = 0; i < 100; i++) {
        CHECK(legends_step_ms(handle, 10, NULL));
    }

    // Type a command
    CHECK(legends_text_input(handle, "DIR\n"));
    CHECK(legends_step_ms(handle, 500, NULL));

    legends_destroy(handle);
    return 0;
}
```

---

## Project Structure

```
ProjectLegends/
├── engine/                     # Refactored DOSBox-X core (900k lines)
│   ├── include/
│   │   ├── aibox/              # AIBox FFI headers
│   │   │   ├── ffi_core.h      # Lifecycle, memory, stepping
│   │   │   ├── ffi_llm.h       # LLM frame serialization
│   │   │   ├── ffi_vision.h    # Screenshot, overlays
│   │   │   └── ffi_events.h    # Event subscription
│   │   └── dosbox/             # DOSBox abstraction
│   │       ├── dosbox_context.h    # Master context struct
│   │       ├── instance_handle.h   # Handle management
│   │       └── platform/           # Platform interfaces
│   ├── src/
│   │   ├── aibox/              # AIBox implementation
│   │   ├── cpu/                # x86 CPU emulation
│   │   ├── dos/                # DOS kernel
│   │   ├── hardware/           # PIC, PIT, DMA, VGA, Sound
│   │   ├── gui/                # Menu system, mapper
│   │   └── ...
│   ├── tests/                  # 2,493 engine tests
│   ├── globals_registry.yaml   # Global state tracking
│   └── CMakeLists.txt
│
├── include/
│   ├── legends/                # Embedding API headers
│   │   └── legends_embed.h     # Main C API
│   └── pal/                    # Platform Abstraction Layer
│
├── src/
│   ├── legends/                # Embedding implementation
│   └── pal/                    # PAL backends (headless/SDL2/SDL3)
│
├── tests/                      # 1,533 embedding tests
│   ├── unit/
│   └── integration/
│
├── spec/
│   ├── CONTRACT.md             # 23 contract gates
│   ├── VERIFICATION_REPORT.md  # TLA+ results
│   └── tla/                    # TLA+ specifications
│
└── TODO.md                     # Development roadmap
```

---

## Error Codes

| Code | Value | Description |
|------|-------|-------------|
| `LEGENDS_OK` | 0 | Success |
| `LEGENDS_ERR_NULL_HANDLE` | -1 | Null handle provided |
| `LEGENDS_ERR_NULL_POINTER` | -2 | Null pointer argument |
| `LEGENDS_ERR_ALREADY_CREATED` | -3 | Instance already exists |
| `LEGENDS_ERR_NOT_INITIALIZED` | -4 | Instance not initialized |
| `LEGENDS_ERR_REENTRANT_CALL` | -5 | Step called from within callback |
| `LEGENDS_ERR_BUFFER_TOO_SMALL` | -6 | Buffer too small |
| `LEGENDS_ERR_INVALID_CONFIG` | -7 | Invalid configuration |
| `LEGENDS_ERR_INVALID_STATE` | -8 | Invalid save state |
| `LEGENDS_ERR_VERSION_MISMATCH` | -9 | API version mismatch |
| `LEGENDS_ERR_IO_FAILED` | -10 | I/O operation failed |
| `LEGENDS_ERR_OUT_OF_MEMORY` | -11 | Memory allocation failed |
| `LEGENDS_ERR_NOT_SUPPORTED` | -12 | Operation not supported |
| `LEGENDS_ERR_INTERNAL` | -13 | Internal error |
| `LEGENDS_ERR_WRONG_THREAD` | -14 | Called from non-owner thread |

---

## Platform Abstraction Layer (PAL)

The PAL provides platform services without leaking SDL dependencies:

| Interface | Purpose |
|-----------|---------|
| `IWindow` | Window creation, resize, fullscreen |
| `IContext` | Software surface / OpenGL context |
| `IAudioSink` | Push-based audio (no callbacks into core) |
| `IHostClock` | Wall time for throttling (not emulated time) |
| `IInputSource` | Event polling, mouse capture |

**Backends:** Headless (no deps), SDL2, SDL3

---

## License

Project Legends is licensed under the GNU General Public License v2.0, consistent with its DOSBox-X heritage.

---

## Acknowledgments

- **DOSBox Team**: Original DOSBox emulator
- **DOSBox-X Team**: Extended platform support
- **TLA+ Community**: Formal methods tooling

---

**Project Legends** - Bringing deterministic x86 emulation to the AI era.

*Copyright (c) 2024-2025 Charles Hoskinson*
