# Project Legends

**A Modern Embeddable x86 Emulation Framework for AI-Driven Computing**

[![Build Status](https://img.shields.io/badge/build-passing-brightgreen)]()
[![License](https://img.shields.io/badge/license-GPL--2.0-blue)]()
[![C++ Standard](https://img.shields.io/badge/C%2B%2B-23-blue)]()
[![Tests](https://img.shields.io/badge/tests-1533%20passing-brightgreen)]()
[![TLA+ Verified](https://img.shields.io/badge/TLA%2B-verified-green)]()

---

## Overview

Project Legends is a modernized, embeddable x86 emulation framework designed for deterministic execution and AI integration. Built on the foundation of DOSBox-X, it provides a clean C API boundary for embedding DOS/x86 emulation into modern applications, with a particular focus on:

- **Deterministic Execution**: Bit-perfect reproducibility: `f(config, trace, schedule) -> hash`
- **LLM Integration**: Structured I/O optimized for language model interaction
- **Vision Model Support**: Screen capture with semantic annotations
- **Platform Abstraction**: Clean separation from SDL2/SDL3 via PAL layer
- **Formal Verification**: TLA+ specifications with TLC model checking
- **Contract Gates**: 23 mechanically enforceable architectural invariants

---

## Architecture

```
                              ┌─────────────────────────────────────────────────────────────────────────────┐
                              │                     Host Application (Rust/Python/C++)                      │
                              │                     LLM Agents, Game Bots, Testing Harnesses                 │
                              └─────────────────────────────────────────────────────────────────────────────┘
                                                                  │
                                                                  ▼ (Stable C ABI - 23 Contract Gates)
┌──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│                                          legends_embed.h (C API Boundary)                                             │
│  ┌────────────────────┐  ┌────────────────────┐  ┌────────────────────┐  ┌────────────────────┐  ┌──────────────────┐ │
│  │     Lifecycle      │  │     Stepping       │  │      Capture       │  │       Input        │  │    Save/Load     │ │
│  │  legends_create()  │  │ legends_step_ms()  │  │legends_capture_*() │  │legends_key_event() │  │legends_save_*()  │ │
│  │ legends_destroy()  │  │legends_step_cycles │  │ legends_is_dirty() │  │legends_text_input()│  │legends_load_*()  │ │
│  │  legends_reset()   │  │legends_get_time()  │  │legends_get_cursor()│  │legends_mouse_*()   │  │legends_get_hash()│ │
│  └────────────────────┘  └────────────────────┘  └────────────────────┘  └────────────────────┘  └──────────────────┘ │
└──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
                                                                  │
                       ┌──────────────────────────────────────────┴──────────────────────────────────────────┐
                       │                                                                                      │
                       ▼                                                                                      ▼
┌─────────────────────────────────────────────────────────────┐     ┌─────────────────────────────────────────────────────────────┐
│              Legends Core (Modern C++23)                     │     │              Platform Abstraction Layer (PAL)                │
│  ┌───────────────────┐  ┌───────────────────────────────┐   │     │  ┌───────────────────────────────────────────────────────┐  │
│  │  MachineContext   │  │      LLM Frame Layer          │   │     │  │  IWindow - create/resize/fullscreen/present           │  │
│  │  Event Bus        │  │  llm_frame.h, llm_actions.h   │   │     │  │  IContext - software surface / OpenGL context         │  │
│  │  Handle Registry  │  │  llm_diff.h, llm_serializer.h │   │     │  │  IAudioSink - push samples (NO callbacks into core)   │  │
│  └───────────────────┘  └───────────────────────────────┘   │     │  │  IHostClock - wall time (NOT emulated time)           │  │
│  ┌───────────────────────────────────────────────────────┐  │     │  │  IInputSource - poll events, mouse capture            │  │
│  │              Vision Capture Layer                      │  │     │  └───────────────────────────────────────────────────────┘  │
│  │  vision_capture.h, vision_framebuffer.h                │  │     │                              │                              │
│  │  vision_overlay.h, vision_annotations.h                │  │     │          ┌──────────────────┼──────────────────┐           │
│  └───────────────────────────────────────────────────────┘  │     │          ▼                  ▼                  ▼           │
└──────────────────────────────────────────────┬──────────────┘     │   ┌──────────────┐  ┌──────────────┐  ┌──────────────┐     │
                                               │                     │   │   Headless   │  │     SDL2     │  │     SDL3     │     │
                                               │                     │   │   Backend    │  │   Backend    │  │   Backend    │     │
                                               │                     │   │ (in-memory)  │  │(SDL_Window)  │  │(SDL_Window)  │     │
                                               │                     │   │ Virtual clock│  │SDL_Callback  │  │SDL_AudioStream    │
                                               │                     │   └──────────────┘  └──────────────┘  └──────────────┘     │
                                               │                     └─────────────────────────────────────────────────────────────┘
                                               │
                                               ▼ (Compile Firewall - No SDL headers leak)
┌──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│                                    Legacy DOSBox-X Core (903k lines, Minimal Patches)                                            │
│  ┌───────────────────────────────┐  ┌───────────────────────────────┐  ┌───────────────────────────────────────────────────────┐ │
│  │            CPU                │  │          Hardware             │  │                    DOS/BIOS                           │ │
│  │  Normal_Loop(), cpudecoder()  │  │  PIC, PIT, DMA, VGA, SB16     │  │  INT 21h, INT 10h, INT 13h, INT 16h                   │ │
│  │  x86 instruction execution    │  │  PIC_RunQueue(), mixer        │  │  File system, video modes, disk I/O                  │ │
│  └───────────────────────────────┘  └───────────────────────────────┘  └───────────────────────────────────────────────────────┘ │
└──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
```

### Layer Responsibilities

| Layer | Responsibility | Key Files |
|-------|---------------|-----------|
| **Host Application** | Owns the emulator lifecycle, provides config, consumes output | User code |
| **C API Boundary** | Stable ABI, version handshake, single-instance enforcement | `legends_embed.h` |
| **Legends Core** | Modern C++23 wrapper, event bus, LLM/Vision layers | `src/legends/` |
| **PAL** | Platform services: window, audio, clock, input | `src/pal/` |
| **DOSBox-X Core** | x86 emulation, hardware, DOS | Legacy code |

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

### Determinism
```
f(config, input_trace, step_schedule) -> state_hash
```
Same inputs always produce same outputs. Verified by `IdenticalTracesProduceIdenticalHash` test.

### Round-Trip Preservation
```
Obs(Deserialize(Serialize(S))) = Obs(S)
```
Save/load preserves observable state. Verified by `SaveLoadRoundTripPreservesState` test and TLA+ model checking.

### Audio Push Model
```
currentThread = "AudioCallback" => lastCaller != "Core"
```
Audio callbacks never drive emulation. Verified by `PALMinimal.tla` specification.

### Thread Isolation
```
coreOwner in {"None", "Main"} AND forall t in palThreads: t != coreOwner
```
Core is single-threaded; PAL threads never access core. Verified by `ThreadingMinimal.tla`.

---

## TLA+ Specifications

| Specification | States | Invariants | Status |
|--------------|--------|------------|--------|
| `LifecycleMinimal.tla` | 85 | AtMostOneInstance, MisuseSafe, HandleConsistency | PASSED |
| `PALMinimal.tla` | 99 | AudioPushModel, ThreadSafety, AudioQueueBounded | PASSED |
| `ThreadingMinimal.tla` | 1,474 | CoreSingleThreaded, PALIsolation, NoDataRaces | PASSED |
| `SaveStateTest.tla` | 8 | ObservationPreserved, EventCountPreserved, TimePreserved | PASSED |

Full specifications in [`spec/tla/`](spec/tla/). Verification report: [`spec/VERIFICATION_REPORT.md`](spec/VERIFICATION_REPORT.md).

---

## Quick Start

### Embedding Example

```c
#include <legends/legends_embed.h>

int main() {
    // Create emulator instance
    legends_handle handle;
    legends_config_t config = LEGENDS_CONFIG_INIT;
    config.deterministic = 1;
    legends_create(&config, &handle);

    // Run for 1 second of emulated time
    for (int i = 0; i < 100; i++) {
        legends_step_ms(handle, 10, NULL);
    }

    // Capture screen
    size_t cell_count;
    legends_capture_text(handle, NULL, 0, &cell_count, NULL);
    legends_text_cell_t* cells = malloc(cell_count * sizeof(legends_text_cell_t));
    legends_capture_text(handle, cells, cell_count, &cell_count, NULL);

    // Type a command
    legends_text_input(handle, "DIR\n");
    legends_step_ms(handle, 500, NULL);

    // Save state
    size_t state_size;
    legends_save_state(handle, NULL, 0, &state_size);
    uint8_t* state = malloc(state_size);
    legends_save_state(handle, state, state_size, &state_size);

    // Verify determinism
    int is_deterministic;
    legends_verify_determinism(handle, 10000, &is_deterministic);
    assert(is_deterministic);

    // Cleanup
    legends_destroy(handle);
    free(cells);
    free(state);
}
```

### Building

```bash
# Headless only (no SDL required)
cmake -B build -DLEGENDS_BUILD_TESTS=ON
cmake --build build
ctest --test-dir build

# With SDL2 backend
cmake -B build -DPAL_BACKEND_SDL2=ON -DLEGENDS_BUILD_TESTS=ON
cmake --build build

# With SDL3 backend
cmake -B build -DPAL_BACKEND_SDL3=ON -DLEGENDS_BUILD_TESTS=ON
cmake --build build

# Run TLA+ model checking
java -jar tla2tools.jar -config spec/tla/LifecycleMinimal.cfg spec/tla/LifecycleMinimal.tla
```

### Developer Build Acceleration

For fast iteration during development:

```bash
# Use Ninja + compiler cache (fastest)
cmake -B build -G Ninja -DCMAKE_CXX_COMPILER_LAUNCHER=ccache
cmake --build build -j$(nproc)

# CMake presets (if CMakePresets.json exists)
cmake --preset headless-dev
cmake --build --preset headless-dev

# Unity build for legacy core (reduces compile units)
cmake -B build -DCMAKE_UNITY_BUILD=ON

# Precompiled headers
cmake -B build -DLEGENDS_USE_PCH=ON
```

**Recommended setup:**
1. Install Ninja: `apt install ninja-build` / `brew install ninja`
2. Install ccache: `apt install ccache` / `brew install ccache`
3. Configure once, rebuild fast: `cmake --build build` after changes

---

## Platform Abstraction Layer (PAL)

The PAL provides platform services (NOT rendering primitives):

```
┌─────────────────────────────────────────────────────────────────────────────────────────┐
│                         PAL Interfaces (include/pal/)                                    │
├──────────────────┬──────────────────┬──────────────────┬──────────────────┬─────────────┤
│     IWindow      │     IContext     │    IAudioSink    │   IHostClock     │IInputSource │
├──────────────────┼──────────────────┼──────────────────┼──────────────────┼─────────────┤
│ create()         │ createSoftware() │ open()           │ getTicksMs()     │ poll()      │
│ resize()         │ createOpenGL()   │ pushSamples()    │ getTicksUs()     │ setCapture()│
│ setFullscreen()  │ lockSurface()    │ getQueuedFrames()│ sleepMs()        │ setRelative │
│ present()        │ makeCurrent()    │ pause()          │ sleepUs()        │             │
│ getDisplayInfo() │ swapBuffers()    │ setVolume()      │                  │             │
└──────────────────┴──────────────────┴──────────────────┴──────────────────┴─────────────┘
                                              │
              ┌───────────────────────────────┼───────────────────────────────┐
              ▼                               ▼                               ▼
       ┌─────────────┐                 ┌─────────────┐                 ┌─────────────┐
       │  Headless   │                 │    SDL2     │                 │    SDL3     │
       ├─────────────┤                 ├─────────────┤                 ├─────────────┤
       │ Memory buf  │                 │ SDL_Window  │                 │ SDL_Window  │
       │ Virtual clk │                 │ SDL_Surface │                 │ SDL_Texture │
       │ Event inject│                 │ SDL_Audio   │                 │ AudioStream │
       │ No deps     │                 │ Callback    │                 │ Push model  │
       └─────────────┘                 └─────────────┘                 └─────────────┘
```

### Key Design Decisions

1. **PAL = Platform Services, NOT Framebuffer Owner**
   - PAL provides window/context resources
   - Existing `OUTPUT_*` layer owns pixels
   - No duplicate rendering abstractions

2. **Audio = Push Model (NOT Callback-Driven)**
   - Emulation produces samples -> pushes to PAL
   - SDL2 callback only reads ring buffer
   - SDL3 uses `SDL_AudioStream` (pure push)

3. **Host Clock vs Emulated Time**
   - `IHostClock`: Wall time for throttling/UI
   - Emulated time: Advanced ONLY by `stepMs()`/`stepCycles()`
   - Never confused

---

## API Reference

### Lifecycle Functions

| Function | Description |
|----------|-------------|
| `legends_get_api_version()` | Get API version for ABI checks |
| `legends_create()` | Create emulator instance (single per process) |
| `legends_destroy()` | Destroy instance and free resources |
| `legends_reset()` | Soft reset (preserves config) |
| `legends_get_config()` | Query current configuration |

### Stepping Functions

| Function | Description |
|----------|-------------|
| `legends_step_ms()` | Step by emulated milliseconds |
| `legends_step_cycles()` | Step by exact CPU cycles |
| `legends_get_emu_time()` | Get current emulated time |
| `legends_get_total_cycles()` | Get total cycles executed |

### Capture Functions

| Function | Description |
|----------|-------------|
| `legends_capture_text()` | Capture text mode screen (CP437 + attributes) |
| `legends_capture_rgb()` | Capture RGB24 framebuffer (pre-scaler) |
| `legends_is_frame_dirty()` | Check if frame changed since last capture |
| `legends_get_cursor()` | Get cursor position and visibility |

### Input Functions

| Function | Description |
|----------|-------------|
| `legends_key_event()` | Inject AT scancode (set 1) |
| `legends_key_event_ext()` | Inject extended scancode (E0 prefix) |
| `legends_text_input()` | Type UTF-8 text string |
| `legends_mouse_event()` | Inject mouse movement/buttons |

### State Functions

| Function | Description |
|----------|-------------|
| `legends_save_state()` | Serialize complete state |
| `legends_load_state()` | Restore from serialized state |
| `legends_get_state_hash()` | SHA-256 of observable state |
| `legends_verify_determinism()` | Round-trip determinism test |

---

## Error Codes

| Code | Value | Description |
|------|-------|-------------|
| `LEGENDS_OK` | 0 | Success |
| `LEGENDS_ERR_NULL_HANDLE` | -1 | Null handle provided |
| `LEGENDS_ERR_NULL_POINTER` | -2 | Null pointer argument |
| `LEGENDS_ERR_ALREADY_CREATED` | -3 | Instance already exists |
| `LEGENDS_ERR_NOT_INITIALIZED` | -4 | Instance not initialized |
| `LEGENDS_ERR_ALREADY_RUNNING` | -5 | Already running |
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

## Project Structure

```
ProjectLegends/
├── include/
│   ├── legends/                # Embeddable API headers
│   │   ├── legends_embed.h     # Main C API (23 contract gates)
│   │   ├── llm_frame.h         # LLM-optimized output
│   │   ├── llm_actions.h       # Semantic action descriptors
│   │   ├── vision_capture.h    # Screen capture
│   │   └── vision_overlay.h    # Annotation rendering
│   │
│   └── pal/                    # Platform Abstraction Layer
│       ├── platform.h          # Backend factory
│       ├── window.h            # Window interface
│       ├── context.h           # Rendering context
│       ├── audio_sink.h        # Audio output (push model)
│       ├── host_clock.h        # Host timing
│       └── input_source.h      # Input events
│
├── src/
│   ├── legends/                # Core implementation
│   └── pal/                    # PAL backends
│       ├── headless/           # In-memory (no deps)
│       ├── sdl2/               # SDL2 backend
│       └── sdl3/               # SDL3 backend
│
├── tests/
│   └── unit/                   # 1500+ unit tests
│       ├── test_contract_gates.cpp  # 23 contract gate tests
│       ├── test_legends_abi.c       # Pure C compilation
│       └── ...
│
├── spec/
│   ├── CONTRACT.md             # Contract specification
│   ├── VERIFICATION_REPORT.md  # TLA+ verification results
│   └── tla/                    # TLA+ specifications
│       ├── LifecycleMinimal.tla
│       ├── PALMinimal.tla
│       ├── ThreadingMinimal.tla
│       ├── SaveStateTest.tla
│       └── ...
│
└── .github/workflows/          # CI configuration
    └── pal-ci.yml              # Contract gate enforcement
```

---

## CI Pipeline

| Job | Purpose |
|-----|---------|
| `headless-tests` | Headless backend on Ubuntu |
| `sdl2-tests` | SDL2 backend on Ubuntu |
| `sdl3-tests` | SDL3 backend (built from source) |
| `contract-gates` | Run contract gate tests + symbol verification |
| `asan-lifecycle` | 100x create/destroy under AddressSanitizer |
| `abi-c-compile` | Pure C11 compilation verification |
| `sdl-firewall` | Verify SDL headers isolated to `src/pal/` |
| `windows-build` | Windows headless build |

---

## Contributing

1. Fork the repository
2. Create a feature branch
3. Write tests (contract gates for architectural changes)
4. Update TLA+ specs for critical changes
5. Ensure all tests pass
6. Submit a pull request

### Code Style

- C++23 with modern idioms
- `gsl-lite` for contracts (violations return errors, never terminate host)
- TLA+ specs for critical invariants
- No singletons (explicit ownership)
- Function names in diagrams are abbreviated (e.g., `create()` = `legends_create()`)

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

*Copyright (c) 2024-2025 Charles Hoskinson and Contributors*
