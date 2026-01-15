# DOSBox-X Library Refactoring - Comprehensive Changelog

**Date:** 2026-01-15
**Scope:** Complete refactoring of DOSBox-X into embeddable library for ProjectLegends
**Total PRs:** 23
**Files Changed:** 1,364+ files, ~1.2M lines of code

---

## Executive Summary

Transformed DOSBox-X from a standalone GUI application into a pure embeddable library with:
- Stable C ABI for FFI integration
- Deterministic stepping for AI agent control
- Headless operation (no SDL dependency in core)
- State hashing for verification
- Token-efficient frame serialization for LLMs

---

## Phase 0: Foundation (PRs 1-4)

### PR #1: Library Contract Document
**Commit:** `b3bf31e`
**Files:**
- `LIBRARY_CONTRACT.md` - V1 contract defining:
  - Single instance per process model
  - No background threads in library mode
  - Deterministic time via `step_*()` calls only
  - No `exit()`, `abort()`, or `printf()` in library mode
  - All output through callbacks or return values

### PR #2: Error Model (FAIL/PANIC/TRAP)
**Commit:** `bff230c`
**Files:**
- `include/dosbox/error_model.h` - Three-level error taxonomy
- `src/misc/error_model.cpp` - Implementation

**Error Levels:**
| Level | Macro | Behavior |
|-------|-------|----------|
| FAIL | `DOSBOX_FAIL(code, msg)` | Returns error, continues |
| PANIC | `DOSBOX_PANIC(msg)` | Context → Failed state |
| TRAP | `DOSBOX_TRAP(msg)` | Calls host handler (rare) |

### PR #3: Logging Infrastructure
**Commit:** `b5f22ff`
**Files:**
- `include/dosbox/logging.h` - Per-context logging API
- `src/misc/logging.cpp` - Implementation

**Features:**
- Context-owned callbacks (no stdout/stderr)
- `log_raw()` fast path for hot loops
- Transitional `current_context()` macros

### PR #4: Boundary Containment (safe_call)
**Commit:** `7e3013c`
**Files:**
- `include/dosbox/safe_call.h` - Exception-safe FFI wrapper
- `src/misc/safe_call.cpp` - Implementation

**Guarantees:**
- No exception escapes public API boundary
- All C++ exceptions converted to error codes
- Host application protected from crashes

---

## Phase 1: Triage-Based Cleanup (PRs 5-8)

### PR #5: Global Registry Baseline
**Commit:** `ef8641d`
**Files:**
- `globals_registry.yaml` - YAML tracking 45+ globals
- `scripts/check_globals_registry.py` - CI enforcement

**Registry Fields:**
```yaml
- name: sdl
  type: SDL_Block
  file: src/gui/sdlmain.cpp
  target_context: DOSBoxContext.sdl
  migration_status: pending|in_progress|migrated
  thread_safety: main_thread_only
  determinism_relevant: true
```

### PR #6: Library Boundary Exit/Printf (Bucket A)
**Commit:** `96eebcb`
**Scope:** ~20 critical files (API-reachable paths)

**Changes:**
- `E_Exit()` → `DOSBOX_FAIL()` for recoverable errors
- `E_Exit()` → `DOSBOX_PANIC()` for invariant violations
- Remove `printf()` from API call paths

### PR #7: State Hash API
**Commit:** `9fc5f43`
**Files:**
- `include/dosbox/state_hash.h` - SHA-256 state hashing
- `src/misc/state_hash.cpp` - Implementation

**API:**
```c
int dosbox_get_state_hash(dosbox_handle h, uint8_t out[32], int full_mode);
```

### PR #8: Misuse-Resilient Handle System
**Commit:** `ac60299`
**Files:**
- `include/dosbox/instance_handle.h` - Generation-counted handles
- `src/misc/instance_handle.cpp` - Handle registry

**State Machine:**
```
Created → Initialized → Running → Shutdown → Destroyed
```

**Protection Against:**
- Null handle access
- Double destroy
- Use after destroy
- Wrong state operations

---

## Phase 2: Context Migration (PRs 9-14)

### PR #9: DOSBoxContext Structure
**Commit:** `ddfe5f4`
**Files:**
- `include/dosbox/dosbox_context.h` - Master context struct
- `src/misc/dosbox_context.cpp` - Implementation

**Context Structure:**
```cpp
struct DOSBoxContext {
    TimingState timing;
    CPUState cpu;
    MixerState mixer;
    VGAState vga;
    PICState pic;
    KeyboardState keyboard;
    InputState input;
    // ... subsystem state
};
```

### PR #10: Migrate Timing State
**Commit:** `305d1ed`
**Migrated Globals:**
- `SDL_ticks_last` → `DOSBoxContext.timing.ticks_last`
- `ticksLocked` → `DOSBoxContext.timing.locked`
- `ticksRemain` → `DOSBoxContext.timing.remain`

### PR #11: Migrate CPU State
**Commit:** `ab9f9b3`
**Migrated Globals:**
- CPU registers → `DOSBoxContext.cpu`
- Segment descriptors → `DOSBoxContext.cpu.segments`
- Flags → `DOSBoxContext.cpu.flags`

### PR #12: Migrate Mixer State
**Commit:** `2bc0970`
**Migrated Globals:**
- `mixer` → `DOSBoxContext.mixer`
- Audio channels → `DOSBoxContext.mixer.channels`
- Sample rate → `DOSBoxContext.mixer.sample_rate`

**Thread Safety:** Ring buffer for audio callback access

### PR #13: Migrate VGA/Display State
**Commit:** `d71315c`
**Migrated Globals:**
- `vga` → `DOSBoxContext.vga`
- CRTC registers → `DOSBoxContext.vga.crtc`
- Attribute controller → `DOSBoxContext.vga.attr`

### PR #14: Batch Remaining (PIC, Keyboard, Input)
**Commit:** `950572d`
**Migrated Globals:**
- PIC state → `DOSBoxContext.pic`
- Keyboard buffer → `DOSBoxContext.keyboard`
- Mouse state → `DOSBoxContext.input`

---

## Phase 3: SDL Abstraction (PRs 15-21)

### PR #15: Platform Interface Definitions
**Commit:** `9d1436a`
**Files:**
- `include/dosbox/platform/platform.h` - Base abstraction
- `include/dosbox/platform/display.h` - IDisplay interface
- `include/dosbox/platform/audio.h` - IAudio interface
- `include/dosbox/platform/input.h` - IInput interface
- `include/dosbox/platform/timing.h` - ITiming interface

**IDisplay Interface:**
```cpp
class IDisplay {
    virtual void upload_frame(span<const uint8_t> pixels, const FrameInfo& info) = 0;
    virtual void present() = 0;
    virtual void set_mode(uint16_t w, uint16_t h, PixelFormat fmt, bool fs) = 0;
};
```

**IAudio Interface (Producer/Consumer):**
```cpp
class IAudio {
    virtual size_t push_samples(span<const int16_t> samples) = 0;
    virtual size_t get_queued_samples() const = 0;
};
```

### PR #16: Headless Platform Backend
**Commit:** `9d46e26`
**Files:**
- `include/dosbox/platform/headless.h` - Headless backend
- `src/platform/headless/headless_display.cpp`
- `src/platform/headless/buffer_audio.cpp`
- `src/platform/headless/thread_safe_input.cpp`

**Behavior:**
- Display: Accepts frames, stores for capture
- Audio: Accepts samples, discards (or buffers)
- Input: Returns no events (or synthetic from API)

### PR #17: sdlmain.cpp Slice A - Timing
**Commit:** `68a58fe`
**Changes:**
- Replace `SDL_GetTicks()` → `ITiming::get_ticks()`
- Replace `SDL_Delay()` → `ITiming::delay()`
- No SDL timing calls in core

### PR #18: sdlmain.cpp Slice B - Display/Window
**Commit:** `37368cb`
**Changes:**
- Replace `SDL_CreateWindow()` → `IDisplay::create()`
- Replace `SDL_UpdateTexture()` → `IDisplay::upload_frame()`
- Replace `SDL_RenderPresent()` → `IDisplay::present()`

### PR #19: sdlmain.cpp Slice C - Input/Events
**Commit:** `74dc33a`
**Changes:**
- Replace `SDL_PollEvent()` → `IInput::poll()`
- Replace `SDL_GetKeyboardState()` → `IInput::get_key_state()`
- Replace `SDL_GetMouseState()` → `IInput::get_mouse_state()`

### PR #20: sdlmain.cpp Slice D - Audio
**Commit:** `4bb09ca`
**Changes:**
- Replace `SDL_OpenAudioDevice()` → `IAudio::open()`
- Replace `SDL_QueueAudio()` → `IAudio::push_samples()`
- Enforce producer/consumer model

### PR #21: SDL Compile Firewall
**Commit:** `5afd5d6`
**Files:**
- `cmake/CompileFirewall.cmake` - Symbol verification
- CI gate: `nm -g libdosbox_core.a | grep SDL_` must be empty

**Verification:**
```bash
# Must return empty
nm -g libaibox_core.a | grep -E "SDL_|main|exit|abort"
```

---

## Phase 4: Integration & Verification (PRs 22-23)

### PR #22: ProjectLegends Bridge
**Commit:** `c1c7734`
**Files:**
- `include/dosbox/dosbox_library.h` - Stable C ABI
- `include/dosbox/error_mapping.h` - Error translation
- `src/misc/dosbox_library.cpp` - Implementation
- `tests/unit/test_dosbox_library.cpp` - 20+ unit tests

**Public API:**
```c
// Lifecycle
dosbox_lib_error_t dosbox_lib_create(const dosbox_lib_config_t* cfg,
                                      dosbox_lib_handle_t* out);
dosbox_lib_error_t dosbox_lib_init(dosbox_lib_handle_t handle);
dosbox_lib_error_t dosbox_lib_destroy(dosbox_lib_handle_t handle);

// Execution
dosbox_lib_error_t dosbox_lib_step_ms(dosbox_lib_handle_t handle,
                                       uint32_t ms,
                                       dosbox_lib_step_result_t* result);

// State
dosbox_lib_error_t dosbox_lib_save_state(dosbox_lib_handle_t handle,
                                          void* buffer, size_t* size);
dosbox_lib_error_t dosbox_lib_load_state(dosbox_lib_handle_t handle,
                                          const void* buffer, size_t size);
dosbox_lib_error_t dosbox_lib_get_state_hash(dosbox_lib_handle_t handle,
                                              uint8_t hash[32]);
```

### PR #23: Determinism Test Suite
**Commit:** `22335e6`
**Files:**
- `tests/determinism/determinism_harness.h` - Test infrastructure
- `tests/determinism/test_determinism.cpp` - 25+ test cases
- `tests/determinism/CMakeLists.txt` - Build config

**Test Categories:**
1. **State Hash Consistency** - Same inputs → same hash
2. **Replay Verification** - Recorded trace reproduces state
3. **Save/Load Round-Trip** - Save → step → load → step = same hash
4. **Headless vs SDL Differential** - Both backends produce identical state
5. **Misuse Resilience** - Invalid inputs return errors, not crashes

---

## Final Integration: ProjectLegends Commit

**Commit:** `a1b50e0` (in projectlegends repo)
**Title:** feat: Integrate DOSBox-X engine as embeddable library (PR #22 bridge)

**Changes:**
1. **engine/** - Entire DOSBox-X library vendored (1,364 files)
2. **CMakeLists.txt** - Added:
   ```cmake
   set(AIBOX_BUILD_TESTS OFF)
   set(AIBOX_HEADLESS ON)
   set(AIBOX_LIBRARY_MODE ON)
   add_subdirectory(engine)
   target_link_libraries(legends_core PRIVATE aibox_core)
   ```
3. **src/legends/legends_embed_api.cpp** - Bridge integration:
   ```cpp
   #include "dosbox/dosbox_library.h"
   #include "dosbox/error_mapping.h"

   dosbox_lib_handle_t g_engine_handle{nullptr};

   // legends_create() → dosbox_lib_create() + dosbox_lib_init()
   // legends_destroy() → dosbox_lib_destroy()
   ```

---

## File Counts by Category

| Category | Files | Lines |
|----------|-------|-------|
| Headers (include/aibox/) | 25 | ~3,000 |
| Headers (include/dosbox/) | 15 | ~2,000 |
| Source (src/aibox/) | 12 | ~4,000 |
| Source (src/misc/) | 8 | ~2,500 |
| Source (src/platform/) | 6 | ~1,500 |
| Unit Tests | 46 | ~8,000 |
| Determinism Tests | 3 | ~1,200 |
| Documentation | 5 | ~1,500 |
| Build/CI Config | 8 | ~800 |
| **Total New/Modified** | **128** | **~24,500** |
| **Vendored (engine/)** | **1,364** | **~1,185,000** |

---

## API Surface Summary

### C FFI Functions (Stable ABI)

**Core Lifecycle:**
- `dosbox_lib_create()` / `dosbox_lib_destroy()`
- `dosbox_lib_init()` / `dosbox_lib_shutdown()`
- `dosbox_lib_reset()`

**Execution:**
- `dosbox_lib_step_ms()` - Deterministic stepping
- `dosbox_lib_step_cycles()` - Precise cycle control

**State Management:**
- `dosbox_lib_save_state()` / `dosbox_lib_load_state()`
- `dosbox_lib_get_state_hash()`

**Input Injection:**
- `dosbox_lib_key_event()`
- `dosbox_lib_mouse_event()`
- `dosbox_lib_type_string()`

**Frame Capture:**
- `dosbox_lib_get_frame()` - Raw framebuffer
- `dosbox_lib_get_text_frame()` - Text-mode serialization

**Error Handling:**
- `dosbox_lib_get_last_error()`
- `dosbox_lib_error_string()`

---

## Determinism Guarantees

### Tier 1 (Guaranteed)
Same binary + same OS + same CPU + same inputs = **identical state hashes**

### Requirements Met:
- [x] No uninitialized memory reads
- [x] No host time dependencies in emulation
- [x] No random sources in determinism-relevant code
- [x] Audio produced during stepping, not callbacks
- [x] Display frames produced during stepping

---

## CI/CD Gates

| Gate | Description | Status |
|------|-------------|--------|
| A | No exit/abort reachable from public API | Enforced |
| B | No SDL symbols in core library | Enforced |
| C | ASan 100-cycle soak passes | Enforced |
| D | State hash stable across runs | Enforced |
| E | Global registry migration tracked | Enforced |
| F | No pointer hazards in Error struct | Enforced |
| G | Audio callback never calls emulation | Enforced |

---

## Architecture Diagram

```
┌─────────────────────────────────────────────────────────────────┐
│                    Host Application (Rust/Python/C)             │
│  ┌─────────────┐  ┌─────────────┐  ┌───────────────────────┐   │
│  │ LLM Agent   │  │ GPU Render  │  │ Game-Specific Logic   │   │
│  └─────────────┘  └─────────────┘  └───────────────────────┘   │
├─────────────────────────────────────────────────────────────────┤
│                    ProjectLegends (legends_embed.h)             │
│  legends_create() → legends_step_ms() → legends_destroy()       │
├─────────────────────────────────────────────────────────────────┤
│                    DOSBox Bridge (dosbox_library.h)             │
│  dosbox_lib_create() → dosbox_lib_step_ms() → dosbox_lib_destroy│
├─────────────────────────────────────────────────────────────────┤
│                    AIBox Layer (C++23)                          │
│  ┌─────────────┐  ┌─────────────┐  ┌───────────────────────┐   │
│  │ ffi_core    │  │ ffi_llm     │  │ ffi_vision            │   │
│  └─────────────┘  └─────────────┘  └───────────────────────┘   │
├─────────────────────────────────────────────────────────────────┤
│                    Platform Abstraction Layer                   │
│  ┌─────────────┐  ┌─────────────┐  ┌───────────────────────┐   │
│  │ IDisplay    │  │ IAudio      │  │ IInput / ITiming      │   │
│  └─────────────┘  └─────────────┘  └───────────────────────┘   │
├─────────────────────────────────────────────────────────────────┤
│                    DOSBox-X Core                                │
│  CPU │ Memory │ VGA │ DOS Kernel │ Hardware Devices             │
├─────────────────────────────────────────────────────────────────┤
│                    DOS Guest Application                        │
└─────────────────────────────────────────────────────────────────┘
```

