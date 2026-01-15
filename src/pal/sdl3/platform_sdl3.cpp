// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// Platform Abstraction Layer - SDL3 Platform Initialization

#include "pal/platform.h"
#include <SDL3/SDL.h>

namespace pal {

// Forward declarations for SDL3 factory functions
std::unique_ptr<IWindow> createWindowSDL3();
std::unique_ptr<IContext> createContextSDL3(IWindow& window);
std::unique_ptr<IAudioSink> createAudioSinkSDL3();
std::unique_ptr<IHostClock> createHostClockSDL3();
std::unique_ptr<IInputSource> createInputSourceSDL3();

namespace sdl3 {

/// Initialize SDL3 subsystems
Result initializeSDL3() {
    // Initialize SDL3 with VIDEO, AUDIO, and JOYSTICK
    // Note: SDL3 removed SDL_INIT_TIMER - timing functions are always available
    SDL_InitFlags flags = SDL_INIT_VIDEO | SDL_INIT_AUDIO | SDL_INIT_JOYSTICK;

    if (!SDL_Init(flags)) {
        return Result::NotSupported;
    }

    return Result::Success;
}

/// Shutdown SDL3
void shutdownSDL3() {
    SDL_Quit();
}

} // namespace sdl3
} // namespace pal
