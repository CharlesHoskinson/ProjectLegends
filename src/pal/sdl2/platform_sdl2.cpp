// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// Platform Abstraction Layer - SDL2 Platform Initialization

#include "pal/platform.h"
#include <SDL.h>

namespace pal {

// Forward declarations for SDL2 factory functions
std::unique_ptr<IWindow> createWindowSDL2();
std::unique_ptr<IContext> createContextSDL2(IWindow& window);
std::unique_ptr<IAudioSink> createAudioSinkSDL2();
std::unique_ptr<IHostClock> createHostClockSDL2();
std::unique_ptr<IInputSource> createInputSourceSDL2();

namespace sdl2 {

/// Initialize SDL2 subsystems
Result initializeSDL2() {
    // Initialize SDL2 with VIDEO, AUDIO, TIMER, and JOYSTICK
    Uint32 flags = SDL_INIT_VIDEO | SDL_INIT_AUDIO | SDL_INIT_TIMER | SDL_INIT_JOYSTICK;

    if (SDL_Init(flags) != 0) {
        return Result::NotSupported;
    }

    return Result::Success;
}

/// Shutdown SDL2
void shutdownSDL2() {
    SDL_Quit();
}

} // namespace sdl2
} // namespace pal
