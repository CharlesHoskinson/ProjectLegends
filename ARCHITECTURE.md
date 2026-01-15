# Project Legends Architecture

This document provides a comprehensive architectural overview of Project Legends,
a modernized, embeddable x86 emulation framework.

---

## Table of Contents

1. [High-Level Architecture](#high-level-architecture)
2. [Layer Details](#layer-details)
3. [Data Flow](#data-flow)
4. [Platform Abstraction Layer (PAL)](#platform-abstraction-layer-pal)
5. [Threading Model](#threading-model)
6. [Determinism Guarantees](#determinism-guarantees)
7. [Formal Verification](#formal-verification)
8. [File Organization](#file-organization)

---

## High-Level Architecture

```
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│                                           HOST APPLICATION                                                       │
│                                                                                                                  │
│    ┌──────────────────┐    ┌──────────────────┐    ┌──────────────────┐    ┌──────────────────┐                 │
│    │   LLM Agent      │    │   Game Bot       │    │  Testing Harness │    │   Rust/Python    │                 │
│    │   (GPT/Claude)   │    │   (Speedrun)     │    │   (CI/CD)        │    │   FFI Wrapper    │                 │
│    └────────┬─────────┘    └────────┬─────────┘    └────────┬─────────┘    └────────┬─────────┘                 │
│             │                       │                       │                       │                            │
│             └───────────────────────┴───────────────────────┴───────────────────────┘                            │
│                                                 │                                                                 │
└─────────────────────────────────────────────────┼─────────────────────────────────────────────────────────────────┘
                                                  │
                                                  ▼ Stable C ABI (22 Contract Gates)
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│                                         LEGENDS EMBED API                                                        │
│                                         legends_embed.h                                                          │
│                                                                                                                  │
│  ┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────┐│
│  │                                      API Function Categories                                                 ││
│  ├───────────────┬───────────────┬───────────────┬───────────────┬───────────────┬─────────────────────────────┤│
│  │   Lifecycle   │   Stepping    │    Capture    │     Input     │  Save/Load    │         Query               ││
│  ├───────────────┼───────────────┼───────────────┼───────────────┼───────────────┼─────────────────────────────┤│
│  │ create()      │ step_ms()     │capture_text() │ key_event()   │ save_state()  │ get_api_version()           ││
│  │ destroy()     │ step_cycles() │capture_rgb()  │ key_event_ext │ load_state()  │ get_config()                ││
│  │ reset()       │ get_emu_time()│is_frame_dirty │ text_input()  │ get_hash()    │ get_last_error()            ││
│  │               │ get_cycles()  │get_cursor()   │ mouse_event() │ verify_det()  │                             ││
│  └───────────────┴───────────────┴───────────────┴───────────────┴───────────────┴─────────────────────────────┘│
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
                                                  │
                       ┌──────────────────────────┴──────────────────────────┐
                       │                                                      │
                       ▼                                                      ▼
┌──────────────────────────────────────────────────────┐  ┌──────────────────────────────────────────────────────┐
│              LEGENDS CORE (C++23)                     │  │        PLATFORM ABSTRACTION LAYER (PAL)              │
│                                                       │  │                                                       │
│  ┌─────────────────────────────────────────────────┐ │  │  ┌─────────────────────────────────────────────────┐ │
│  │              Handle Registry                     │ │  │  │                  Interfaces                     │ │
│  │  - Single instance enforcement                   │ │  │  │                                                 │ │
│  │  - Handle validation                             │ │  │  │  IWindow        - Window management             │ │
│  │  - Resource tracking                             │ │  │  │  IContext       - Rendering context            │ │
│  └─────────────────────────────────────────────────┘ │  │  │  IAudioSink     - Audio output (push)          │ │
│                                                       │  │  │  IHostClock     - Wall-clock timing            │ │
│  ┌─────────────────────────────────────────────────┐ │  │  │  IInputSource   - Input event polling          │ │
│  │              Machine Context                     │ │  │  │                                                 │ │
│  │  - CPU state wrapper                             │ │  │  └─────────────────────────────────────────────────┘ │
│  │  - Memory access                                 │ │  │                          │                           │
│  │  - Device state                                  │ │  │      ┌──────────────────┼──────────────────┐        │
│  └─────────────────────────────────────────────────┘ │  │      ▼                  ▼                  ▼        │
│                                                       │  │ ┌──────────┐      ┌──────────┐      ┌──────────┐   │
│  ┌─────────────────────────────────────────────────┐ │  │ │ Headless │      │   SDL2   │      │   SDL3   │   │
│  │              Event Bus                           │ │  │ ├──────────┤      ├──────────┤      ├──────────┤   │
│  │  - Frame events                                  │ │  │ │ Memory   │      │ Window   │      │ Window   │   │
│  │  - Input events                                  │ │  │ │ Virtual  │      │ Callback │      │ Stream   │   │
│  │  - State change notifications                    │ │  │ │ Clock    │      │ Audio    │      │ Audio    │   │
│  └─────────────────────────────────────────────────┘ │  │ │ No deps  │      │ Events   │      │ Events   │   │
│                                                       │  │ └──────────┘      └──────────┘      └──────────┘   │
│  ┌─────────────────────────────────────────────────┐ │  │                                                       │
│  │              LLM Frame Layer                     │ │  └──────────────────────────────────────────────────────┘
│  │  - llm_frame.h: Screen abstraction              │ │
│  │  - llm_actions.h: Semantic actions              │ │
│  │  - llm_diff.h: Delta encoding                   │ │
│  │  - llm_serializer.h: JSON output                │ │
│  └─────────────────────────────────────────────────┘ │
│                                                       │
│  ┌─────────────────────────────────────────────────┐ │
│  │              Vision Capture Layer                │ │
│  │  - vision_capture.h: RGB capture                │ │
│  │  - vision_framebuffer.h: FB access              │ │
│  │  - vision_overlay.h: Annotations                │ │
│  │  - vision_annotations.h: Semantic markup        │ │
│  └─────────────────────────────────────────────────┘ │
└──────────────────────────────────────┬───────────────┘
                                       │
                                       ▼ Compile Firewall (No SDL leakage)
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│                                    LEGACY DOSBOX-X CORE                                                          │
│                                    903,199 lines / 664 source files                                              │
│                                                                                                                  │
│  ┌────────────────────────────────┐  ┌────────────────────────────────┐  ┌────────────────────────────────────┐ │
│  │            CPU                 │  │          Hardware              │  │            DOS/BIOS                │ │
│  │                                │  │                                │  │                                    │ │
│  │  Normal_Loop()                 │  │  PIC (8259)                    │  │  INT 21h - DOS services            │ │
│  │  cpudecoder_x86()              │  │  PIT (8254)                    │  │  INT 10h - Video BIOS              │ │
│  │  x86 instruction decode        │  │  DMA (8237)                    │  │  INT 13h - Disk BIOS               │ │
│  │  Protected/Real mode           │  │  VGA (CRTC, DAC, Sequencer)    │  │  INT 16h - Keyboard BIOS           │ │
│  │  V86 mode                      │  │  Sound Blaster 16              │  │  File system                       │ │
│  │                                │  │  UART (Serial)                 │  │  Memory management                 │ │
│  │  PIC_RunQueue()                │  │  Keyboard controller           │  │  Device drivers                    │ │
│  │  Event scheduler               │  │  Floppy/HDD controller         │  │                                    │ │
│  └────────────────────────────────┘  └────────────────────────────────┘  └────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
```

---

## Layer Details

### Layer 1: Host Application

The topmost layer is the user's application that embeds Project Legends.

**Responsibilities:**
- Create and own the emulator instance
- Provide configuration
- Drive emulation via stepping
- Consume output (screen, audio, state)
- Handle input from user/AI

**Examples:**
- LLM agents that play DOS games
- Automated testing harnesses
- Speedrun bots
- Python/Rust bindings

### Layer 2: C API Boundary (`legends_embed.h`)

The stable ABI layer enforced by 22 contract gates.

**Key Properties:**
- Pure C interface (no C++ types exposed)
- Version handshake at creation
- Single-instance per process
- All errors returned as codes (no exceptions)
- No exit/abort reachable

**API Categories:**

| Category | Functions | Purpose |
|----------|-----------|---------|
| Lifecycle | `create`, `destroy`, `reset` | Instance management |
| Stepping | `step_ms`, `step_cycles` | Advance emulation |
| Capture | `capture_text`, `capture_rgb` | Read screen |
| Input | `key_event`, `text_input`, `mouse_event` | Inject input |
| State | `save_state`, `load_state`, `get_hash` | Serialization |

### Layer 3: Legends Core (C++23)

Modern C++ wrapper providing:

**Handle Registry:**
- Enforces single-instance rule
- Validates handles on every API call
- Tracks resource ownership

**Machine Context:**
- Wraps DOSBox-X CPU state
- Provides safe memory access
- Manages device state

**Event Bus:**
- Frame completion events
- Input injection events
- State change notifications

**LLM Frame Layer:**
- `llm_frame.h`: Abstract screen as structured data
- `llm_actions.h`: Semantic action descriptors
- `llm_diff.h`: Efficient delta compression
- `llm_serializer.h`: JSON output for LLMs

**Vision Capture Layer:**
- `vision_capture.h`: RGB24 screen capture
- `vision_framebuffer.h`: Direct FB access
- `vision_overlay.h`: Annotation rendering
- `vision_annotations.h`: Semantic markup

### Layer 4: Platform Abstraction Layer (PAL)

See [Platform Abstraction Layer section](#platform-abstraction-layer-pal) for details.

### Layer 5: Legacy DOSBox-X Core

The original DOSBox-X codebase with minimal patches.

**Components:**
- CPU: x86 instruction execution, mode switching
- Hardware: PIC, PIT, DMA, VGA, Sound Blaster
- DOS/BIOS: INT handlers, file system, device drivers

**Statistics:**
- 903,199 lines of code
- 664 source files
- Minimal modifications for embedding

---

## Data Flow

### Stepping Flow

```
Host App                    Legends Core                 DOSBox-X Core
    │                            │                            │
    │  legends_step_ms(h, 100)   │                            │
    │ ─────────────────────────► │                            │
    │                            │  Normal_Loop(cycles)       │
    │                            │ ─────────────────────────► │
    │                            │                            │
    │                            │     Execute x86 code       │
    │                            │     PIC_RunQueue()         │
    │                            │     Update hardware        │
    │                            │                            │
    │                            │  ◄───────────────────────  │
    │                            │                            │
    │  step_result_t             │                            │
    │ ◄───────────────────────── │                            │
    │                            │                            │
```

### Capture Flow

```
Host App                    Legends Core                 DOSBox-X Core
    │                            │                            │
    │  legends_capture_text()    │                            │
    │ ─────────────────────────► │                            │
    │                            │  Read VGA text memory      │
    │                            │ ─────────────────────────► │
    │                            │                            │
    │                            │  ◄─── CP437 + attributes   │
    │                            │                            │
    │  legends_text_cell_t[]     │                            │
    │ ◄───────────────────────── │                            │
    │                            │                            │
```

### Audio Flow (Push Model)

```
DOSBox-X Core              Legends Core                 PAL (SDL2/SDL3)
    │                            │                            │
    │  MIXER produces samples    │                            │
    │ ─────────────────────────► │                            │
    │                            │  Ring buffer               │
    │                            │ ─────────────────────────► │
    │                            │                            │
    │                            │   pushSamples()            │
    │                            │ ─────────────────────────► │
    │                            │                            │
    │                            │      Audio device          │
    │                            │ ──────────────────────────►│
```

Note: Audio callback (SDL2) only reads from ring buffer. It never calls into core.

---

## Platform Abstraction Layer (PAL)

### Design Principles

1. **Platform Services, NOT Framebuffer Owner**
   - PAL provides window/context resources
   - Existing `OUTPUT_*` layer owns pixels
   - No duplicate rendering abstractions

2. **Push Model Audio (NOT Callback-Driven)**
   - Emulation produces samples
   - Pushes to PAL sink
   - SDL2 callback only reads ring buffer
   - SDL3 uses `SDL_AudioStream` (pure push)

3. **Host Clock vs Emulated Time**
   - `IHostClock`: Wall time for throttling/UI
   - Emulated time: Advanced ONLY by stepping
   - Never confused

4. **Compile Firewall (SDL Isolation)**
   - SDL headers only included in `src/pal/sdl2/` and `src/pal/sdl3/`
   - Core library contains no SDL symbols
   - **CI Enforcement:** `sdl-firewall` job verifies:
     ```bash
     # No SDL includes outside PAL
     grep -r "SDL\.h\|SDL2\|SDL3" src/ include/ --include="*.cpp" --include="*.h" \
       | grep -v "src/pal/" && exit 1

     # No SDL symbols in core library
     nm -g build/lib/libprojectlegends_core.a | grep "SDL_" && exit 1
     ```

### Interfaces

```cpp
namespace pal {

// Window management
class IWindow {
    Result create(const WindowConfig& config);
    void destroy();
    Result resize(uint32_t width, uint32_t height);
    Result setFullscreen(bool fullscreen);
    Result present();
    uint32_t getDisplayCount() const;
    Result getDisplayInfo(uint32_t index, DisplayInfo& info) const;
};

// Rendering context
class IContext {
    Result createSoftware(uint32_t width, uint32_t height, PixelFormat fmt);
    Result createOpenGL(int major, int minor, bool core_profile);
    Result lockSurface(SoftwareContext& ctx);
    void unlockSurface();
    Result makeCurrent();
    void swapBuffers();
};

// Audio output (push model)
class IAudioSink {
    Result open(const AudioConfig& config);
    void close();
    Result pushSamples(const int16_t* samples, uint32_t frame_count);
    uint32_t getQueuedFrames() const;
    Result pause(bool pause);
    Result setVolume(float volume);
};

// Host timing (NOT emulated time)
class IHostClock {
    uint64_t getTicksMs() const;
    uint64_t getTicksUs() const;
    void sleepMs(uint32_t ms);
    void sleepUs(uint64_t us);
};

// Input events
class IInputSource {
    uint32_t poll(InputEvent* events, uint32_t max_events);
    Result setMouseCapture(bool capture);
    Result setRelativeMouseMode(bool relative);
};

} // namespace pal
```

### Backend Comparison

| Feature | Headless | SDL2 | SDL3 |
|---------|----------|------|------|
| Window | Memory buffer | `SDL_Window` | `SDL_Window` |
| Rendering | Software only | Surface/GL | Texture/GL/GPU |
| Audio | Discarded | Callback | `SDL_AudioStream` |
| Timing | Virtual clock | `SDL_GetTicks` | `SDL_GetTicks` |
| Dependencies | None | SDL2 | SDL3 |
| Use case | Testing, CI | Desktop | Desktop (future) |

---

## Threading Model

### Core is Single-Threaded

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                              APPLICATION THREAD                                  │
│                                                                                  │
│    ┌──────────────┐    ┌──────────────┐    ┌──────────────┐    ┌──────────────┐ │
│    │legends_create│───►│legends_step  │───►│legends_capture───►│legends_destroy│
│    └──────────────┘    └──────────────┘    └──────────────┘    └──────────────┘ │
│                                                                                  │
│    All API calls must be from the SAME thread (the "owner thread")               │
│    Wrong-thread calls return LEGENDS_ERR_WRONG_THREAD (not UB)                   │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
                                       │
                                       │ owns
                                       ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│                              LEGENDS CORE                                        │
│                                                                                  │
│    ┌──────────────────────────────────────────────────────────────────────────┐ │
│    │                          DOSBox-X Core                                    │ │
│    │                                                                           │ │
│    │   CPU execution, hardware emulation, DOS services                         │ │
│    │   ALL state access is single-threaded                                     │ │
│    │                                                                           │ │
│    └──────────────────────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────────────────────────┘
                                       │
                                       │ uses (but PAL threads never call back)
                                       ▼
┌─────────────────────────────────────────────────────────────────────────────────┐
│                              PAL LAYER                                           │
│                                                                                  │
│    ┌──────────────────────┐    ┌──────────────────────┐                         │
│    │    Audio Thread      │    │    (SDL2 only)       │                         │
│    │    (SDL2 callback)   │    │                      │                         │
│    │                      │    │  Only READS from     │                         │
│    │  NEVER calls core    │    │  ring buffer         │                         │
│    │  NEVER calls API     │    │                      │                         │
│    └──────────────────────┘    └──────────────────────┘                         │
│                                                                                  │
│    SDL3: No audio callbacks (uses SDL_AudioStream push model)                    │
│                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────┘
```

### TLA+ Verified Invariants

| Invariant | Specification | Meaning |
|-----------|---------------|---------|
| `CoreSingleThreaded` | `coreOwner \in {"None", "Main"}` | Only main thread owns core |
| `PALIsolation` | `\A t \in palThreads : t # coreOwner` | PAL threads never access core |
| `AudioPushModel` | `currentThread = "Audio" => lastCaller # "Core"` | Audio never calls core |

---

## Determinism Guarantees

### The Core Guarantee

```
f(config, input_trace, step_schedule) -> state_hash
```

Given identical:
1. Configuration (`legends_config_t`)
2. Input trace (sequence of key/mouse events)
3. Step schedule (sequence of `step_ms`/`step_cycles` calls)

The resulting state hash is **bit-identical**.

### Round-Trip Invariant

```
Obs(Deserialize(Serialize(S))) = Obs(S)
```

Observable state after load equals observable state before save.

### Observable State Definition

The `get_state_hash()` function computes SHA-256 over **observable state**, defined as:

**Included (affects emulation behavior):**
- CPU: All registers, flags, mode, instruction pointer, segment descriptors
- Memory: Conventional RAM, EMS pages, XMS blocks, UMB regions
- Paging: Page tables, CR3, if protected mode
- PIC: IRR, IMR, ISR for master and slave 8259
- PIT: All channel counters, modes, latches, output states
- DMA: Channel state, masks, page registers
- VGA: All registers, VRAM, DAC palette, timing state
- Keyboard: Buffer contents, LED state, controller mode
- Event Queue: All pending timer/interrupt events with deadlines

**Excluded (host-only, no emulation effect):**
- PAL state: Window handles, audio device handles
- Host clock values
- Performance counters
- Log buffers
- Capture buffers (derived from VRAM)

### Verified By

| Property | C++ Test | TLA+ Specification |
|----------|----------|-------------------|
| Trace determinism | `IdenticalTracesProduceIdenticalHash` | `Determinism.tla` |
| Round-trip | `SaveLoadRoundTripPreservesState` | `SaveStateTest.tla` |
| Input replay | `InputReplayProducesIdenticalHash` | - |

---

## Formal Verification

### TLA+ Specifications

| Specification | Purpose | States | Invariants |
|--------------|---------|--------|------------|
| `LifecycleMinimal.tla` | Instance lifecycle | 85 | AtMostOneInstance, MisuseSafe |
| `PALMinimal.tla` | Audio push model | 99 | AudioPushModel, ThreadSafety |
| `ThreadingMinimal.tla` | Thread isolation | 1,474 | CoreSingleThreaded, PALIsolation |
| `SaveStateTest.tla` | Save/load round-trip | 8 | ObservationPreserved |

### Model Checking Results

All specifications pass TLC model checking:

```
LifecycleMinimal: 85 states generated, 24 distinct - PASSED
PALMinimal: 99 states generated, 29 distinct - PASSED
ThreadingMinimal: 1,474 states generated, 303 distinct - PASSED
SaveStateTest: 8 states generated, 3 distinct - PASSED
```

### Traceability

Each TLA+ invariant maps to a C++ test:

| TLA+ Invariant | C++ Test | File:Line |
|----------------|----------|-----------|
| `AtMostOneInstance` | `SingleInstanceEnforced` | test_contract_gates.cpp:90 |
| `MisuseSafe` | `MisuseSafe_StepWithoutCreate` | test_contract_gates.cpp:69 |
| `AudioPushModel` | `PushModelNoCallback` | test_contract_gates.cpp:421 |
| `CoreSingleThreaded` | `CoreIsSingleThreaded` | test_contract_gates.cpp:447 |
| `ObservationPreserved` | `SaveLoadRoundTripPreservesState` | test_contract_gates.cpp:201 |

---

## File Organization

```
ProjectLegends/
├── include/
│   ├── legends/                    # Public API headers
│   │   ├── legends_embed.h         # Main C API (stable ABI)
│   │   ├── llm_frame.h             # LLM-optimized screen
│   │   ├── llm_actions.h           # Semantic actions
│   │   ├── llm_diff.h              # Delta compression
│   │   ├── llm_serializer.h        # JSON serialization
│   │   ├── vision_capture.h        # RGB capture
│   │   ├── vision_framebuffer.h    # Framebuffer access
│   │   ├── vision_overlay.h        # Annotation rendering
│   │   ├── vision_annotations.h    # Semantic markup
│   │   ├── machine_context.h       # CPU/memory wrapper
│   │   ├── event_bus.h             # Event system
│   │   ├── handle_registry.h       # Handle management
│   │   └── ...
│   │
│   └── pal/                        # Platform Abstraction Layer
│       ├── platform.h              # Backend factory
│       ├── types.h                 # Common types
│       ├── window.h                # IWindow interface
│       ├── context.h               # IContext interface
│       ├── audio_sink.h            # IAudioSink interface
│       ├── host_clock.h            # IHostClock interface
│       └── input_source.h          # IInputSource interface
│
├── src/
│   ├── legends/                    # Core implementation
│   │   ├── embed_api.cpp           # C API implementation
│   │   ├── machine_context.cpp     # Machine context
│   │   ├── event_bus.cpp           # Event system
│   │   ├── handle_registry.cpp     # Handle management
│   │   ├── llm_*.cpp               # LLM layer
│   │   └── vision_*.cpp            # Vision layer
│   │
│   └── pal/                        # PAL backends
│       ├── headless/               # No-dependency backend
│       │   ├── window_headless.cpp
│       │   ├── context_headless.cpp
│       │   ├── audio_sink_headless.cpp
│       │   ├── host_clock_headless.cpp
│       │   ├── input_source_headless.cpp
│       │   └── platform_headless.cpp
│       │
│       ├── sdl2/                   # SDL2 backend
│       │   ├── window_sdl2.cpp
│       │   ├── context_sdl2.cpp
│       │   ├── audio_sink_sdl2.cpp
│       │   ├── host_clock_sdl2.cpp
│       │   ├── input_source_sdl2.cpp
│       │   └── platform_sdl2.cpp
│       │
│       └── sdl3/                   # SDL3 backend
│           ├── window_sdl3.cpp
│           ├── context_sdl3.cpp
│           ├── audio_sink_sdl3.cpp
│           ├── host_clock_sdl3.cpp
│           ├── input_source_sdl3.cpp
│           └── platform_sdl3.cpp
│
├── tests/
│   └── unit/
│       ├── test_contract_gates.cpp # 22 contract gate tests
│       ├── test_legends_abi.c      # Pure C compilation
│       ├── test_lifecycle.cpp      # Lifecycle tests
│       ├── test_stepping.cpp       # Stepping tests
│       ├── test_capture.cpp        # Capture tests
│       ├── test_input.cpp          # Input tests
│       ├── test_saveload.cpp       # State tests
│       ├── test_pal_*.cpp          # PAL tests
│       └── ...
│
├── spec/
│   ├── CONTRACT.md                 # Contract specification
│   ├── VERIFICATION_REPORT.md      # TLA+ verification results
│   └── tla/
│       ├── Types.tla               # Core type definitions
│       ├── LifecycleMinimal.tla    # Lifecycle model
│       ├── PALMinimal.tla          # PAL model
│       ├── ThreadingMinimal.tla    # Threading model
│       ├── SaveStateTest.tla       # Save/load model
│       ├── EmuKernel.tla           # Emulation kernel
│       ├── Scheduler.tla           # Event scheduler
│       ├── PIC.tla                 # Interrupt controller
│       ├── DMA.tla                 # DMA controller
│       └── *.cfg                   # TLC configurations
│
├── .github/workflows/
│   └── pal-ci.yml                  # CI configuration
│
├── README.md                       # Project overview
├── ARCHITECTURE.md                 # This document
├── CMakeLists.txt                  # Build configuration
└── LICENSE                         # GPL-2.0
```

---

## Summary

Project Legends provides:

1. **Clean Architecture**: 5-layer design with clear responsibilities
2. **Stable ABI**: 22 contract gates enforce correctness
3. **Platform Independence**: PAL enables SDL2/SDL3/Headless
4. **Formal Verification**: TLA+ specifications with TLC model checking
5. **Determinism**: Bit-perfect reproducibility guaranteed
6. **Embeddability**: No singletons, explicit ownership

The architecture enables:
- AI agents to play DOS games deterministically
- Automated testing with save/load checkpoints
- Cross-platform deployment without code changes
- Future SDL3 migration without touching core
