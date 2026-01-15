# SDL Usage Audit for AIBox Library Mode

This document tracks SDL symbol usage across the DOSBox-X codebase and documents
the compile firewall that ensures the core library remains SDL-free.

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         Host Application                                     │
│                    (ProjectLegends, Test Harness)                           │
└────────────────────────────────┬────────────────────────────────────────────┘
                                 │
                                 ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                      aibox_core (Pure C++ Library)                          │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐    │
│  │   Timing     │  │   Display    │  │    Input     │  │    Audio     │    │
│  │  Interface   │  │  Interface   │  │  Interface   │  │  Interface   │    │
│  │  (ITiming)   │  │  (IDisplay)  │  │   (IInput)   │  │   (IAudio)   │    │
│  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘    │
│         │                 │                 │                 │             │
│  NO SDL │ SYMBOLS         │ ALLOWED         │ IN THIS         │ LAYER       │
└─────────┼─────────────────┼─────────────────┼─────────────────┼─────────────┘
          │                 │                 │                 │
          ▼                 ▼                 ▼                 ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                        Platform Backends                                     │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐    │
│  │VirtualTiming │  │HeadlessDisp. │  │ThreadSafeInp │  │ BufferAudio  │    │
│  │(Deterministic│  │(Frame Capture│  │(Event Queue) │  │(Ring Buffer) │    │
│  └──────────────┘  └──────────────┘  └──────────────┘  └──────────────┘    │
│                                                                              │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐    │
│  │  HostTiming  │  │  SDL2Display │  │  SDL2Input   │  │  SDL2Audio   │    │
│  │ (Real Clock) │  │  (Window)    │  │  (Events)    │  │  (Playback)  │    │
│  └──────────────┘  └──────────────┘  └──────────────┘  └──────────────┘    │
│                                                                              │
│  SDL SYMBOLS ALLOWED IN THIS LAYER (frontend only)                          │
└─────────────────────────────────────────────────────────────────────────────┘
```

## SDL Symbol Categories

### Category A: Core Library (NO SDL)

These directories are part of `aibox_core` and must have ZERO SDL dependencies:

| Directory | Purpose | SDL Status |
|-----------|---------|------------|
| `src/misc/` | Error model, logging, context | ✅ SDL-free |
| `src/aibox/` | Vision, LLM serialization | ✅ SDL-free |
| `src/platform/headless/` | Headless backends | ✅ SDL-free |
| `include/aibox/` | Public API headers | ✅ SDL-free |
| `include/dosbox/` | DOSBox interface headers | ✅ SDL-free |

### Category B: Headless Stubs (SDL Replacement)

`src/aibox/headless_stub.cpp` provides SDL-compatible function signatures that
use the platform abstraction layer:

| SDL Function | Stub Implementation |
|-------------|---------------------|
| `SDL_GetTicks()` | Returns `aibox::headless::GetTicks()` via timing provider |
| `SDL_Delay(ms)` | No-op in deterministic mode, real delay via timing provider |
| `GFX_Init()` | No-op |
| `GFX_EndUpdate()` | Calls `display->present()` if provider set |
| `GFX_SetSize()` | Calls `display->set_mode()` if provider set |
| `GFX_Events()` | No-op (input via `IInput::poll_event()`) |
| `MAPPER_Init()` | No-op |
| `MAPPER_Run()` | No-op |
| `MAPPER_Check()` | No-op |

### Category C: Frontend (SDL Allowed)

These files are NOT part of `aibox_core` and can use SDL directly:

| File | SDL Usage | Notes |
|------|-----------|-------|
| `src/gui/sdlmain.cpp` | Full SDL2 | Main event loop, window management |
| `src/gui/sdl_mapper.cpp` | SDL events | Keyboard/joystick mapping |
| `src/gui/sdl_gui.cpp` | SDL rendering | GUI dialogs |
| `src/gui/render.cpp` | SDL textures | Rendering pipeline |
| `src/output/*.cpp` | SDL/OpenGL | Output backends |
| `src/hardware/mixer.cpp` | SDL audio | Audio callbacks (with care) |

### Category D: Third-Party Libraries (SDL Isolated)

These are isolated third-party code that may use SDL internally:

| Directory | Usage |
|-----------|-------|
| `src/libs/gui_tk/` | GUI toolkit (SDL events) |
| `src/libs/fluidsynth/` | FluidSynth SDL audio |
| `src/libs/decoders/` | SDL_sound audio decoding |

## Platform Abstraction Mapping

### Timing (PR #17)

```cpp
// Before (SDL):
Uint32 ticks = SDL_GetTicks();
SDL_Delay(ms);

// After (Platform):
uint64_t ticks = timing->get_ticks();
timing->delay(ms);  // Only if !is_deterministic()
```

### Display (PR #18)

```cpp
// Before (SDL):
SDL_UpdateTexture(texture, NULL, pixels, pitch);
SDL_RenderCopy(renderer, texture, NULL, NULL);
SDL_RenderPresent(renderer);

// After (Platform):
display->upload_frame(pixels, info);
display->present();
```

### Input (PR #19)

```cpp
// Before (SDL):
SDL_Event event;
while (SDL_PollEvent(&event)) {
    handle_event(event);
}

// After (Platform):
while (auto event = input->poll_event()) {
    handle_event(*event);
}
```

### Audio (PR #20)

```cpp
// Before (SDL):
SDL_QueueAudio(device, samples, size);

// After (Platform):
audio->push_samples(samples);
```

## Compile Firewall Verification

The build system includes a post-build check that verifies no forbidden SDL
symbols appear in `aibox_core`:

```cmake
# cmake/CompileFirewall.cmake
aibox_verify_no_sdl_in_core(aibox_core)
```

### Forbidden Symbols (must not appear in aibox_core)

- `SDL_Init`, `SDL_Quit`
- `SDL_CreateWindow`, `SDL_DestroyWindow`
- `SDL_CreateRenderer`, `SDL_DestroyRenderer`
- `SDL_PollEvent`, `SDL_PushEvent`
- `SDL_OpenAudio`, `SDL_CloseAudio`, `SDL_PauseAudio`
- `SDL_QueueAudio`, `SDL_GetQueuedAudioSize`
- `SDL_CreateTexture`, `SDL_UpdateTexture`
- `SDL_RenderCopy`, `SDL_RenderPresent`

### Allowed Symbols (provided by headless stubs)

- `SDL_GetTicks` (replaced by `aibox::headless::GetTicks()`)
- `SDL_Delay` (replaced by no-op or timing provider delay)

## Migration Status

| SDL Subsystem | Abstracted | Tested | Notes |
|---------------|------------|--------|-------|
| Timing | ✅ PR #17 | ✅ | VirtualTiming for determinism |
| Display | ✅ PR #18 | ✅ | HeadlessDisplay for frame capture |
| Input | ✅ PR #19 | ✅ | ThreadSafeInput for event injection |
| Audio | ✅ PR #20 | ✅ | BufferAudio for sample capture |
| Window Mgmt | ✅ Stubbed | ✅ | GFX_* stubs in headless mode |
| Event Loop | ✅ Stubbed | ✅ | GFX_Events() no-op |

## Verification Commands

### Check aibox_core for SDL symbols (Unix):
```bash
nm -g libaibox_core.a | grep SDL_ | grep -v "SDL_GetTicks\|SDL_Delay"
# Should return empty
```

### Check aibox_core for SDL symbols (Windows):
```powershell
dumpbin /symbols aibox_core.lib | Select-String "SDL_" | Where-Object { $_ -notmatch "SDL_GetTicks|SDL_Delay" }
# Should return empty
```

### Run headless build:
```bash
cmake -B build -DAIBOX_HEADLESS=ON
cmake --build build
ctest --test-dir build -L unit
```
