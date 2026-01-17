# Project Legends Architecture

This document describes the architectural design of Project Legends, an embeddable x86 emulation framework.

---

## Table of Contents

1. [High-Level Architecture](#high-level-architecture)
2. [Layer Details](#layer-details)
3. [Data Flow](#data-flow)
4. [State Serialization](#state-serialization)
5. [Platform Abstraction Layer](#platform-abstraction-layer)
6. [Threading Model](#threading-model)
7. [Determinism Guarantees](#determinism-guarantees)
8. [File Organization](#file-organization)
9. [Module Graph (Sprint 3)](#module-graph-sprint-3)

---

## High-Level Architecture

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           HOST APPLICATION                                   │
│                                                                              │
│    ┌──────────────┐    ┌──────────────┐    ┌──────────────┐                 │
│    │  LLM Agent   │    │  Game Bot    │    │  Test Harness│                 │
│    └──────┬───────┘    └──────┬───────┘    └──────┬───────┘                 │
│           └───────────────────┴───────────────────┘                          │
│                               │                                              │
└───────────────────────────────┼──────────────────────────────────────────────┘
                                │
                                ▼ Stable C ABI
┌─────────────────────────────────────────────────────────────────────────────┐
│                         LEGENDS EMBED API                                    │
│                         legends_embed.h                                      │
│                                                                              │
│  ┌─────────────────────────────────────────────────────────────────────────┐│
│  │                        API Function Categories                           ││
│  ├─────────────┬─────────────┬─────────────┬─────────────┬─────────────────┤│
│  │  Lifecycle  │  Stepping   │   Capture   │    Input    │   Save/Load     ││
│  ├─────────────┼─────────────┼─────────────┼─────────────┼─────────────────┤│
│  │ create()    │ step_ms()   │capture_text │ key_event() │ save_state()    ││
│  │ destroy()   │ step_cycles │capture_rgb()│ text_input()│ load_state()    ││
│  │ reset()     │ get_cycles()│             │mouse_event()│ get_state_hash()││
│  └─────────────┴─────────────┴─────────────┴─────────────┴─────────────────┘│
└─────────────────────────────────────────────────────────────────────────────┘
                                │
              ┌─────────────────┴─────────────────┐
              │                                    │
              ▼                                    ▼
┌─────────────────────────────────┐  ┌────────────────────────────────────────┐
│        LEGENDS CORE (C++23)     │  │   PLATFORM ABSTRACTION LAYER (PAL)     │
│                                 │  │                                         │
│  ┌───────────────────────────┐  │  │  ┌─────────────────────────────────┐   │
│  │     Handle Registry       │  │  │  │          Interfaces             │   │
│  │  - Single instance rule   │  │  │  │                                 │   │
│  │  - Handle validation      │  │  │  │  IWindow      - Window mgmt     │   │
│  └───────────────────────────┘  │  │  │  IContext     - Rendering       │   │
│                                 │  │  │  IAudioSink   - Audio output    │   │
│  ┌───────────────────────────┐  │  │  │  IHostClock   - Wall-clock time │   │
│  │     Machine Context       │  │  │  │  IInputSource - Event polling   │   │
│  │  - CPU state wrapper      │  │  │  └─────────────────────────────────┘   │
│  │  - Memory access          │  │  │                    │                   │
│  │  - Device state           │  │  │      ┌────────────┼────────────┐      │
│  └───────────────────────────┘  │  │      ▼            ▼            ▼      │
│                                 │  │ ┌──────────┐ ┌──────────┐ ┌──────────┐│
│  ┌───────────────────────────┐  │  │ │ Headless │ │   SDL2   │ │   SDL3   ││
│  │     DOSBox Library        │  │  │ │  (none)  │ │ callback │ │  stream  ││
│  │  dosbox_lib_step_cycles() │  │  │ └──────────┘ └──────────┘ └──────────┘│
│  │  dosbox_lib_save_state()  │  │  └────────────────────────────────────────┘
│  │  dosbox_lib_load_state()  │  │
│  └───────────────────────────┘  │
└───────────────┬─────────────────┘
                │
                ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                        DOSBOX-X CORE ENGINE                                  │
│                                                                              │
│  ┌────────────────┐  ┌────────────────┐  ┌────────────────┐                 │
│  │      CPU       │  │    Hardware    │  │    DOS/BIOS    │                 │
│  │                │  │                │  │                │                 │
│  │  Normal_Loop() │  │  PIC (8259)    │  │  INT 21h       │                 │
│  │  x86 decode    │  │  PIT (8254)    │  │  INT 10h       │                 │
│  │  Prot/Real mode│  │  DMA, VGA, SB  │  │  File system   │                 │
│  │  PIC_RunQueue()│  │  Keyboard ctrl │  │  Memory mgmt   │                 │
│  └────────────────┘  └────────────────┘  └────────────────┘                 │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Layer Details

### Layer 1: Host Application

The topmost layer is the user's application that embeds Project Legends.

**Responsibilities:**
- Create and own the emulator instance
- Provide configuration at creation
- Drive emulation via stepping
- Consume output (screen, audio, state)
- Handle input from user or AI

### Layer 2: C API Boundary

The stable ABI layer defined in `legends_embed.h`.

**Properties:**
- Pure C interface (no C++ types exposed)
- Single-instance per process (V1 constraint)
- All errors returned as codes
- No `exit()` or `abort()` reachable

### Layer 3: Legends Core

Modern C++ implementation providing:

**Handle Registry:** Enforces single-instance rule, validates handles.

**Machine Context:** Wraps DOSBox-X CPU state, provides safe memory access.

**DOSBox Library Bridge:** Connects to engine via `dosbox_lib_*()` functions for stepping and state management.

### Layer 4: Platform Abstraction Layer

See [Platform Abstraction Layer](#platform-abstraction-layer) section.

### Layer 5: DOSBox-X Core Engine

The original DOSBox-X codebase with modifications for library embedding.

**Components:**
- CPU: x86 instruction execution, mode switching
- Hardware: PIC, PIT, DMA, VGA, Sound Blaster
- DOS/BIOS: INT handlers, file system, device drivers

---

## Data Flow

### Stepping Flow

```
Host App                    Legends Core                 DOSBox-X Core
    │                            │                            │
    │  legends_step_ms(h, 100)   │                            │
    │ ─────────────────────────► │                            │
    │                            │  dosbox_lib_step_cycles()  │
    │                            │ ─────────────────────────► │
    │                            │                            │
    │                            │     Execute x86 code       │
    │                            │     PIC_RunQueue()         │
    │                            │                            │
    │                            │  ◄───────────────────────  │
    │                            │                            │
    │  step_result_t             │                            │
    │ ◄───────────────────────── │                            │
```

### Save/Load Flow

```
Host App                    Legends Core                 DOSBox-X Core
    │                            │                            │
    │  legends_save_state()      │                            │
    │ ─────────────────────────► │                            │
    │                            │  Save legends state        │
    │                            │  (time, PIC, DMA, events)  │
    │                            │                            │
    │                            │  dosbox_lib_save_state()   │
    │                            │ ─────────────────────────► │
    │                            │     Serialize engine state │
    │                            │  ◄───────────────────────  │
    │                            │                            │
    │                            │  Compute CRC32             │
    │                            │  Write combined buffer     │
    │                            │                            │
    │  buffer + size             │                            │
    │ ◄───────────────────────── │                            │
```

---

## State Serialization

### Format Overview

```
┌─────────────────────────────────────────────────────────────┐
│ SaveStateHeader (96 bytes)                                  │
│   magic: 0x4C454753 ("LEGS")                                │
│   version: 2                                                │
│   total_size, checksum                                      │
│   section offsets and sizes                                 │
├─────────────────────────────────────────────────────────────┤
│ Legends Layer Sections                                      │
│   TimeState      - cycles, emu_time_us                      │
│   CPUState       - interrupt flag, halted                   │
│   PICState       - IRR, IMR, ISR for both PICs              │
│   DMAState       - 8 channels                               │
│   EventQueue     - pending events with deadlines            │
│   InputState     - key and mouse queues                     │
│   FrameState     - text buffer, cursor, graphics pixels     │
├─────────────────────────────────────────────────────────────┤
│ Engine State (120 bytes)                                    │
│   EngineStateHeader   - magic, version, offsets             │
│   EngineStateTiming   - total_cycles, virtual_ticks         │
│   EngineStatePic      - PIC ticks, IRQ masks                │
│   EngineStateKeyboard - scancode state, buffer              │
└─────────────────────────────────────────────────────────────┘
```

### Integrity Verification

The save format includes multiple integrity checks:

1. **Header validation**: Magic number and version check
2. **Size validation**: `total_size >= sizeof(header)` and `total_size <= buffer_size`
3. **CRC32 checksum**: Computed over all data after header
4. **Section bounds**: All offsets validated against checksummed region
5. **Content validation**: Frame dimensions checked against maximum bounds

### Security Considerations

- All section offsets validated against `verified_size` (checksummed region)
- Prevents reading beyond integrity-verified data
- Prevents integer overflow in offset calculations
- Frame dimensions capped at 80×50 to prevent buffer overflows

---

## Platform Abstraction Layer

### Design Principles

1. **Platform services, not framebuffer owner**: PAL provides window/context resources; existing OUTPUT layer owns pixels.

2. **Push model audio**: Emulation produces samples and pushes to PAL sink. SDL2 callback only reads ring buffer; SDL3 uses `SDL_AudioStream`.

3. **Host clock vs emulated time**: `IHostClock` provides wall time for throttling. Emulated time advances only via stepping.

4. **Compile firewall**: SDL headers only in `src/pal/sdl2/` and `src/pal/sdl3/`. Core library contains no SDL symbols.

### Interfaces

```cpp
namespace pal {

class IWindow {
    Result create(const WindowConfig& config);
    void destroy();
    Result resize(uint32_t width, uint32_t height);
    Result setFullscreen(bool fullscreen);
    Result present();
};

class IAudioSink {
    Result open(const AudioConfig& config);
    void close();
    Result pushSamples(const int16_t* samples, uint32_t frame_count);
    uint32_t getQueuedFrames() const;
};

class IHostClock {
    uint64_t getTicksMs() const;
    uint64_t getTicksUs() const;
    void sleepMs(uint32_t ms);
};

class IInputSource {
    uint32_t poll(InputEvent* events, uint32_t max_events);
};

} // namespace pal
```

### Backend Comparison

| Feature | Headless | SDL2 | SDL3 |
|---------|----------|------|------|
| Window | Memory buffer | SDL_Window | SDL_Window |
| Audio | Discarded | Callback | SDL_AudioStream |
| Timing | Virtual clock | SDL_GetTicks | SDL_GetTicks |
| Dependencies | None | SDL2 | SDL3 |
| Use case | Testing, CI | Desktop | Desktop (future) |

---

## Threading Model

### Core is Single-Threaded

```
┌─────────────────────────────────────────────────────────────────────────┐
│                          APPLICATION THREAD                              │
│                                                                          │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌───────────┐ │
│  │  create  │──►│   step   │──►│  capture │──►│   save   │──►│  destroy  │ │
│  └──────────┘  └──────────┘  └──────────┘  └──────────┘  └───────────┘ │
│                                                                          │
│  All API calls from the SAME thread (the "owner thread")                 │
│  Wrong-thread calls return LEGENDS_ERR_WRONG_THREAD                      │
└─────────────────────────────────────────────────────────────────────────┘
                                    │
                                    │ owns
                                    ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                            LEGENDS CORE                                  │
│                                                                          │
│  CPU execution, hardware emulation, DOS services                         │
│  ALL state access is single-threaded                                     │
└─────────────────────────────────────────────────────────────────────────┘
                                    │
                                    │ uses (PAL threads never call back)
                                    ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                              PAL LAYER                                   │
│                                                                          │
│  Audio thread (SDL2 callback): NEVER calls core, only reads ring buffer │
│  SDL3: No callbacks (pure push model via SDL_AudioStream)                │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Determinism Guarantees

### Core Guarantee

```
f(config, input_trace, step_schedule) → state_hash
```

Given identical configuration, input trace, and step schedule, the resulting state hash is bit-identical.

### Round-Trip Invariant

```
Obs(Deserialize(Serialize(S))) = Obs(S)
```

Observable state after load equals observable state before save. This invariant is verified by TLA+ specification and integration tests.

### Observable State

The `get_state_hash()` function computes SHA-256 over observable state:

**Included:**
- Time: total_cycles, emu_time_us
- Event queue: pending events with deadlines
- CPU: interrupt flag, halted state
- PIC: IRR, IMR, ISR for master and slave

**Excluded (host-only):**
- PAL state (window handles, audio device)
- Host clock values
- Performance counters
- Log buffers

### Verification

| Property | Test | Specification |
|----------|------|---------------|
| Trace determinism | `IdenticalTracesProduceIdenticalHash` | Determinism.tla |
| Round-trip | `TLAPlusObservationInvariant` | SaveStateTest.tla |
| Step granularity | `MultipleBranchingDeterminism` | - |

---

## File Organization

```
ProjectLegends/
├── include/
│   ├── legends/                    # Public API headers
│   │   ├── legends_embed.h         # Main C API
│   │   ├── handle_registry.h       # Handle management
│   │   └── machine_context.h       # CPU/memory wrapper
│   │
│   └── pal/                        # Platform interfaces
│       ├── window.h
│       ├── audio_sink.h
│       ├── host_clock.h
│       └── input_source.h
│
├── src/
│   ├── legends/                    # Core implementation
│   │   ├── legends_embed_api.cpp   # C API implementation
│   │   └── machine_context.cpp
│   │
│   └── pal/                        # PAL backends
│       ├── headless/
│       ├── sdl2/
│       └── sdl3/
│
├── engine/
│   ├── include/dosbox/
│   │   ├── dosbox_context.h        # Context structure
│   │   ├── dosbox_library.h        # Library mode API
│   │   ├── engine_state.h          # Serialization format
│   │   └── cpu_bridge.h            # CPU execution bridge
│   │
│   └── src/misc/
│       ├── dosbox_library.cpp      # Library implementation
│       └── cpu_bridge.cpp          # CPU bridge (stub)
│
├── tests/
│   └── unit/
│       ├── test_legends_embed.cpp
│       └── test_dosbox_library.cpp
│
├── spec/
│   ├── CONTRACT.md
│   └── tla/
│       ├── SaveStateTest.tla
│       └── Determinism.tla
│
├── README.md
├── ARCHITECTURE.md
└── TODO.md
```

---

## Module Graph (Sprint 3)

This section documents the static library DAG and module boundaries established in Sprint 3.

### Module Definitions

| Module | Public Headers | Private Sources | Library Target | Tier |
|--------|---------------|-----------------|----------------|------|
| legends | include/legends/ | src/legends/ | legends_core | A (strict) |
| pal | include/pal/ | src/pal/ | legends_pal | A (strict) |
| engine | engine/include/dosbox/, engine/include/aibox/ | engine/src/, engine/include/ | aibox_core | B (legacy) |

### Dependency Rules

1. **legends_core** may depend on **aibox_core** only
2. **legends_pal** has no module dependencies (leaf node)
3. **aibox_core** has no module dependencies (leaf node)
4. Cross-module includes MUST use public header paths only
5. No `../src/` includes in public headers

### Include Path Convention

- Public: `#include "legends/foo.h"` or `#include "dosbox/bar.h"`
- Private: `#include "internal/baz.h"` (within same module only)

### DAG Visualization

```
legends_core ──→ aibox_core
legends_pal  ──→ (none)
aibox_core   ──→ (none)
```

### CI Enforcement

The module DAG is enforced by:
- `cmake/ModuleManifest.cmake` - Module definitions
- `cmake/ModuleDAG.cmake` - Dependency verification at configure time
- `scripts/check_includes.py` - Include rule verification
- `.github/workflows/module-dag.yml` - CI workflow

### Cross-Module Service Interfaces

The formal contract between `legends_core` and `aibox_core` is defined in
`engine/include/dosbox/engine_services.h`. This header:

1. Re-exports `dosbox_library.h` functions (the C API)
2. Provides `EngineServiceTable` struct for dependency injection
3. Documents the complete integration surface
4. Includes `EngineHandle` RAII wrapper for C++ code

**Production Usage:**
```cpp
#include "dosbox/engine_services.h"

auto err = dosbox_lib_create(&config, &handle);  // Direct C API (preferred)
// OR
auto services = dosbox::EngineServiceTable::defaults();  // Via service table
```

**Test Usage (Mocking):**
```cpp
#include "dosbox/engine_services.h"

auto mocks = dosbox::EngineServiceTable::null_table();
mocks.create = [](auto*, auto*) { return DOSBOX_LIB_OK; };
mocks.step_cycles = my_mock_step;

// Pass mocks to code under test
my_function(mocks);
```

**Service Categories:**

| Category | Functions | Purpose |
|----------|-----------|---------|
| Lifecycle | get_version, create, init, destroy, reset | Context management |
| Execution | step_ms, step_cycles, get_emu_time, get_total_cycles | Emulation stepping |
| State | get_state_hash, save_state, load_state | Persistence |
| Input | inject_key, inject_mouse | User input injection |
| Error | get_last_error, set_log_callback | Error handling |
| Hardware | get_pic_state | Hardware state inspection |

### Build Metrics

#### Methodology

Metrics collected using `scripts/measure_rebuild.py`:
- Clean build: Full rebuild from scratch
- Incremental: Touch file, rebuild, measure time
- Each test repeated for consistency

#### Results (Sprint 3 Post-Refactoring)

| Metric | Time | Target | Status |
|--------|------|--------|--------|
| Clean build | 26.6s | - | Baseline |
| legends_embed.h change | 1.45s | <10s | Pass |
| dosbox_library.h change | 2.68s | <10s | Pass |
| builtin.h change | 0.42s | <10s | Pass |
| render.h change | 0.43s | <10s | Pass |
| Single .cpp change | 1.45s | <5s | Pass |

*Measured on Windows with MSVC, headless build, 2026-01-17*

#### Targets Met

- Header change rebuild: **<3s** (target was <10s)
- Single .cpp change: **<2s** (target was <5s)
- Module isolation working: refactored headers trigger minimal rebuilds

---

## Summary

Project Legends provides:

1. **Layered architecture** with clear boundaries and responsibilities
2. **Stable C ABI** for embedding from any language
3. **Platform independence** via PAL abstraction
4. **Deterministic execution** verified by specification and tests
5. **Full state serialization** with integrity verification

The architecture enables deterministic replay, automated testing with checkpoints, and cross-platform deployment without code changes.
