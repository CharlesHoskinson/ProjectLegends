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

The project emerged from a fundamental observation: existing emulators were designed as standalone applications, not libraries. They spawn threads, access global state, call `exit()` on errors, and generally behave as if they own the process. This architecture makes them unsuitable for embedding into larger applications, particularly AI agents that need to run thousands of emulator instances, save and restore state at arbitrary points, and guarantee bit-perfect reproducibility across runs.

Project Legends solves this by treating the emulator as a pure function. Given a configuration, an input trace, and a stepping schedule, the engine produces a deterministic output. No hidden state, no threading surprises, no environmental dependencies. The host application controls everything: when to step, when to capture, when to inject input. This inversion of control transforms an unwieldy application into a predictable building block.

The refactoring effort touched nearly every file in the original DOSBox-X codebase. Global variables were systematically migrated into a context structure. Platform dependencies were abstracted behind clean interfaces. The event loop was replaced with explicit stepping. What remains is an engine that can be safely embedded into Rust services, Python notebooks, or any application that can call a C API.

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

The engine is a fully refactored DOSBox-X core (~900k lines) transformed into an embeddable library. The transformation required careful surgical work to preserve compatibility with thousands of DOS applications while fundamentally changing how the emulator interfaces with the outside world.

At the top level, host applications interact with the engine through a stable C ABI defined in `legends_embed.h`. This boundary enforces 23 contract gates that guarantee safe, predictable behavior. Below this sits the AIBox layer, which provides high-level services like LLM frame serialization and vision overlays. The Platform Abstraction Layer (PAL) handles all platform-specific operations through clean interfaces, allowing the same engine to run headless in a server, with SDL2 on a desktop, or with SDL3 for modern features.

The core engine itself retains the battle-tested DOSBox-X emulation code: accurate x86 CPU emulation, hardware device simulation (VGA, Sound Blaster, DMA, timers), and a complete DOS kernel implementation. The key difference is that all mutable state now lives in the `DOSBoxContext` structure, passed explicitly through the call stack rather than accessed through global variables.

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

The original DOSBox-X used extensive global variables, a common pattern in C/C++ applications from the 1990s and 2000s. These globals made the code simpler to write initially but created fundamental barriers to embedding: you cannot have two instances because they would share state, you cannot serialize state because it is scattered across the address space, and you cannot reason about side effects because any function might touch any global.

The migration process involved identifying every global variable, understanding its role in the emulation, and moving it into the appropriate location within `DOSBoxContext`. Some globals represented CPU state, others represented hardware device state, and still others tracked runtime configuration. Each migration required updating all call sites to pass the context explicitly, a mechanical but extensive transformation spanning hundreds of files.

Over 21 PRs, these have been systematically migrated to `DOSBoxContext`:

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

The engine exposes four FFI modules for host integration. Each module provides a focused set of operations, allowing host applications to link only what they need and keeping the API surface manageable.

The FFI layer uses a C ABI for maximum compatibility. Rust applications use bindgen-generated bindings, Python uses ctypes or cffi, and any language with C FFI support can integrate. All functions follow consistent conventions: opaque handles for instance management, output parameters for complex returns, and integer error codes for all fallible operations.

Memory ownership follows clear rules. Buffers passed to the engine are borrowed for the duration of the call. Strings returned by the engine are valid until the next call that might mutate them. Handles must be explicitly destroyed. These rules are documented in the headers and enforced by the contract gates.

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

The architecture is enforced by 23 mechanically verifiable gates. Unlike informal coding guidelines that drift over time, contract gates are concrete tests that run in CI on every commit. If a gate fails, the build fails. This mechanical enforcement prevents the gradual erosion of architectural invariants that plagues large codebases.

Each gate corresponds to a specific property that the engine must maintain. Some gates verify ABI stability: symbols are exported correctly, headers compile as pure C, version handshakes prevent mismatched builds. Other gates verify runtime behavior: no calls to `exit()` or `abort()`, no access to environment variables, no spawning of threads. Still others verify the determinism contract: identical inputs produce identical outputs, serialization round-trips preserve observable state.

The gates are designed to be self-documenting. Reading the test code tells you exactly what property is being enforced and how to verify it. When a gate fails, the failure message points directly to the violated invariant. This makes the architecture legible to new contributors and maintainable over time.

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

Beyond the contract gates, certain critical invariants are verified using TLA+, a formal specification language designed by Leslie Lamport. TLA+ allows us to model the system's behavior as a state machine and exhaustively check all reachable states for violations. This catches subtle bugs that testing might miss, particularly in concurrent and stateful systems.

The specifications focus on the properties most critical to embedding: lifecycle state transitions, threading constraints, audio callback isolation, and save/load round-trip preservation. Each specification was developed alongside the implementation, serving as both documentation and verification. The TLC model checker explores thousands of states to confirm that the invariants hold.

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

Getting started with Project Legends requires a modern C++ toolchain. The codebase uses C++23 features extensively, including `std::expected`, `std::format`, and `std::span`, so GCC 13+ or Clang 16+ is required. CMake handles the build configuration, with Ninja recommended for fast incremental builds.

The default build produces a headless library with no external dependencies, suitable for server deployments and automated testing. For interactive use, enable the SDL2 or SDL3 backend to get windowed rendering, audio output, and input handling. The same engine code runs in all configurations; only the PAL backend differs.

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

The repository is organized to separate concerns cleanly. The `engine/` directory contains the refactored DOSBox-X core, including all CPU, hardware, and DOS emulation code. This is where the heavy lifting happens: x86 instruction decoding, VGA rendering, Sound Blaster emulation, and thousands of other details required to run DOS software.

The top-level `include/` and `src/` directories contain the embedding layer and PAL implementations. This code is much smaller than the engine but equally important: it defines the public API, implements the contract gates, and provides platform backends. Keeping this separate from the engine makes it clear what is internal implementation versus public interface.

The `spec/` directory contains formal specifications and documentation. The TLA+ files define the system's invariants precisely enough for machine verification. The CONTRACT.md file documents all 23 gates in human-readable form. Together, these form the authoritative reference for the engine's behavior.

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

All API functions return integer error codes rather than throwing exceptions or aborting. This design ensures that error handling remains in the host's control: the host decides whether an error is fatal, recoverable, or ignorable. The engine never calls `exit()` or `abort()`, even on internal errors.

Error codes are organized into ranges by category. Codes 0-99 cover common errors like null handles and invalid parameters. Codes in the hundreds indicate subsystem-specific failures: 100s for hardware emulation, 200s for LLM operations, 300s for vision capture. This organization helps debugging by immediately indicating which subsystem encountered the problem.

Each error code has a corresponding human-readable message available through `aibox_error_message()`. For the most recent error on a specific handle, `aibox_last_error()` returns a detailed message that may include context like the invalid parameter value or the resource that was exhausted.

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

The Platform Abstraction Layer decouples the engine from specific windowing and audio libraries. This decoupling serves multiple purposes. First, it allows the engine to run headless without linking against SDL at all, critical for server deployments and containerized workloads. Second, it enables support for multiple SDL versions without conditional compilation scattered throughout the codebase. Third, it provides a clean boundary for future backends like WebAssembly or native platform APIs.

Each PAL interface defines a minimal contract. `IWindow` handles window creation and resizing. `IContext` provides either a software surface or an OpenGL context for rendering. `IAudioSink` accepts audio samples in a push model, avoiding the callback complexity that causes threading issues. `IHostClock` provides wall time for throttling, carefully separated from the emulated time that determines CPU cycles. `IInputSource` polls for keyboard and mouse events.

The headless backend implements all interfaces with no-op or buffer-based stubs. The SDL2 and SDL3 backends provide full implementations using their respective APIs. Switching backends requires only a different link-time dependency and CMake option; no engine code changes are needed.

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

Project Legends is licensed under the GNU General Public License v2.0, consistent with its DOSBox-X heritage. This license requires that derivative works also be distributed under GPL-2.0, ensuring that improvements to the emulation engine benefit the entire community.

For applications that embed Project Legends, the GPL-2.0 applies to the combined work. Host applications that link against the engine must be GPL-2.0 compatible. If you require different licensing terms for commercial embedding, please contact the project maintainers to discuss options.

---

## Acknowledgments

Project Legends builds on decades of work by the emulation community. The foundation is DOSBox, originally created by the DOSBox Team to run classic DOS games on modern systems. Their careful attention to compatibility and accuracy made thousands of applications playable again.

DOSBox-X extended this work with support for additional hardware, improved DOS compatibility, and enhanced debugging features. Many of the advanced features in Project Legends, particularly the VGA and Sound Blaster emulation, trace directly to DOSBox-X contributions.

The formal verification approach was inspired by the TLA+ community and Leslie Lamport's work on temporal logic. The availability of the TLC model checker made it practical to verify complex invariants that would be difficult to test exhaustively.

- **DOSBox Team**: Original DOSBox emulator
- **DOSBox-X Team**: Extended platform support
- **TLA+ Community**: Formal methods tooling

---

**Project Legends** - Bringing deterministic x86 emulation to the AI era.

*Copyright (c) 2024-2025 Charles Hoskinson*
