// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// Platform Abstraction Layer - Platform Factory Implementation

#include "pal/platform.h"
#include <atomic>

namespace pal {

// Forward declarations for headless factory functions
std::unique_ptr<IWindow> createWindowHeadless();
std::unique_ptr<IContext> createContextHeadless(IWindow& window);
std::unique_ptr<IAudioSink> createAudioSinkHeadless();
std::unique_ptr<IHostClock> createHostClockHeadless();
std::unique_ptr<IInputSource> createInputSourceHeadless();

// Forward declarations for SDL2 factory functions (when available)
#if defined(PAL_HAS_SDL2)
std::unique_ptr<IWindow> createWindowSDL2();
std::unique_ptr<IContext> createContextSDL2(IWindow& window);
std::unique_ptr<IAudioSink> createAudioSinkSDL2();
std::unique_ptr<IHostClock> createHostClockSDL2();
std::unique_ptr<IInputSource> createInputSourceSDL2();
namespace sdl2 {
    Result initializeSDL2();
    void shutdownSDL2();
}
#endif

// Forward declarations for SDL3 factory functions (when available)
#if defined(PAL_HAS_SDL3)
std::unique_ptr<IWindow> createWindowSDL3();
std::unique_ptr<IContext> createContextSDL3(IWindow& window);
std::unique_ptr<IAudioSink> createAudioSinkSDL3();
std::unique_ptr<IHostClock> createHostClockSDL3();
std::unique_ptr<IInputSource> createInputSourceSDL3();
namespace sdl3 {
    Result initializeSDL3();
    void shutdownSDL3();
}
#endif

namespace {

// Global platform state
std::atomic<bool> g_initialized{false};
std::atomic<Backend> g_active_backend{Backend::None};

} // anonymous namespace

// ═══════════════════════════════════════════════════════════════════════════
// Platform Implementation
// ═══════════════════════════════════════════════════════════════════════════

Result Platform::initialize(Backend backend) {
    if (g_initialized.load()) {
        return Result::AlreadyInitialized;
    }

    switch (backend) {
        case Backend::Headless:
#if defined(PAL_HAS_HEADLESS) || !defined(PAL_HAS_SDL2) && !defined(PAL_HAS_SDL3)
            // Headless always available, or default when no SDL
            g_active_backend.store(Backend::Headless);
            g_initialized.store(true);
            return Result::Success;
#else
            return Result::NotSupported;
#endif

        case Backend::SDL2:
#if defined(PAL_HAS_SDL2)
            {
                Result result = sdl2::initializeSDL2();
                if (result != Result::Success) {
                    return result;
                }
                g_active_backend.store(Backend::SDL2);
                g_initialized.store(true);
                return Result::Success;
            }
#else
            return Result::NotSupported;
#endif

        case Backend::SDL3:
#if defined(PAL_HAS_SDL3)
            {
                Result result = sdl3::initializeSDL3();
                if (result != Result::Success) {
                    return result;
                }
                g_active_backend.store(Backend::SDL3);
                g_initialized.store(true);
                return Result::Success;
            }
#else
            return Result::NotSupported;
#endif

        case Backend::None:
        default:
            return Result::InvalidParameter;
    }
}

void Platform::shutdown() {
    if (!g_initialized.load()) {
        return;
    }

    Backend backend = g_active_backend.load();

    switch (backend) {
        case Backend::SDL2:
#if defined(PAL_HAS_SDL2)
            sdl2::shutdownSDL2();
#endif
            break;

        case Backend::SDL3:
#if defined(PAL_HAS_SDL3)
            sdl3::shutdownSDL3();
#endif
            break;

        case Backend::Headless:
        case Backend::None:
        default:
            // Nothing to clean up
            break;
    }

    g_active_backend.store(Backend::None);
    g_initialized.store(false);
}

bool Platform::isInitialized() {
    return g_initialized.load();
}

Backend Platform::getActiveBackend() {
    return g_active_backend.load();
}

const char* Platform::getBackendName() {
    return toString(g_active_backend.load());
}

// ═══════════════════════════════════════════════════════════════════════════
// Factory Methods
// ═══════════════════════════════════════════════════════════════════════════

std::unique_ptr<IWindow> Platform::createWindow() {
    if (!g_initialized.load()) {
        return nullptr;
    }

    switch (g_active_backend.load()) {
        case Backend::Headless:
            return createWindowHeadless();

#if defined(PAL_HAS_SDL2)
        case Backend::SDL2:
            return createWindowSDL2();
#endif

#if defined(PAL_HAS_SDL3)
        case Backend::SDL3:
            return createWindowSDL3();
#endif

        default:
            return nullptr;
    }
}

std::unique_ptr<IContext> Platform::createContext(IWindow& window) {
    if (!g_initialized.load()) {
        return nullptr;
    }

    switch (g_active_backend.load()) {
        case Backend::Headless:
            return createContextHeadless(window);

#if defined(PAL_HAS_SDL2)
        case Backend::SDL2:
            return createContextSDL2(window);
#endif

#if defined(PAL_HAS_SDL3)
        case Backend::SDL3:
            return createContextSDL3(window);
#endif

        default:
            return nullptr;
    }
}

std::unique_ptr<IAudioSink> Platform::createAudioSink() {
    if (!g_initialized.load()) {
        return nullptr;
    }

    switch (g_active_backend.load()) {
        case Backend::Headless:
            return createAudioSinkHeadless();

#if defined(PAL_HAS_SDL2)
        case Backend::SDL2:
            return createAudioSinkSDL2();
#endif

#if defined(PAL_HAS_SDL3)
        case Backend::SDL3:
            return createAudioSinkSDL3();
#endif

        default:
            return nullptr;
    }
}

std::unique_ptr<IHostClock> Platform::createHostClock() {
    if (!g_initialized.load()) {
        return nullptr;
    }

    switch (g_active_backend.load()) {
        case Backend::Headless:
            return createHostClockHeadless();

#if defined(PAL_HAS_SDL2)
        case Backend::SDL2:
            return createHostClockSDL2();
#endif

#if defined(PAL_HAS_SDL3)
        case Backend::SDL3:
            return createHostClockSDL3();
#endif

        default:
            return nullptr;
    }
}

std::unique_ptr<IInputSource> Platform::createInputSource() {
    if (!g_initialized.load()) {
        return nullptr;
    }

    switch (g_active_backend.load()) {
        case Backend::Headless:
            return createInputSourceHeadless();

#if defined(PAL_HAS_SDL2)
        case Backend::SDL2:
            return createInputSourceSDL2();
#endif

#if defined(PAL_HAS_SDL3)
        case Backend::SDL3:
            return createInputSourceSDL3();
#endif

        default:
            return nullptr;
    }
}

} // namespace pal
