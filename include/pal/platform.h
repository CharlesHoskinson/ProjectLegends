// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// Platform Abstraction Layer - Platform Factory

#pragma once

#include "pal/types.h"
#include "pal/window.h"
#include "pal/context.h"
#include "pal/audio_sink.h"
#include "pal/host_clock.h"
#include "pal/input_source.h"
#include <memory>

namespace pal {

/// Available PAL backends
enum class Backend {
    None = 0,
    SDL2,       // SDL 2.x backend
    SDL3,       // SDL 3.x backend
    Headless    // No display/audio - for testing and LLM mode
};

/// Platform initialization and factory
///
/// Initialize once at startup, create services via factory methods.
/// All services are created as unique_ptr - caller owns lifetime.
class Platform {
public:
    // ═══════════════════════════════════════════════════════════════════════
    // Initialization
    // ═══════════════════════════════════════════════════════════════════════

    /// Initialize the platform with specified backend
    /// @param backend The backend to use
    /// @return Success, NotSupported (backend not available), AlreadyInitialized
    static Result initialize(Backend backend);

    /// Shutdown the platform and release all resources
    static void shutdown();

    /// Check if platform is initialized
    static bool isInitialized();

    /// Get the active backend
    static Backend getActiveBackend();

    /// Get the active backend name as string
    static const char* getBackendName();

    // ═══════════════════════════════════════════════════════════════════════
    // Factory Methods
    // ═══════════════════════════════════════════════════════════════════════

    /// Create a window instance
    /// @return New window, or nullptr if not initialized
    static std::unique_ptr<IWindow> createWindow();

    /// Create a rendering context for a window
    /// @param window The window to create context for
    /// @return New context, or nullptr if not initialized
    static std::unique_ptr<IContext> createContext(IWindow& window);

    /// Create an audio sink
    /// @return New audio sink, or nullptr if not initialized
    static std::unique_ptr<IAudioSink> createAudioSink();

    /// Create a host clock
    /// @return New host clock, or nullptr if not initialized
    static std::unique_ptr<IHostClock> createHostClock();

    /// Create an input source
    /// @return New input source, or nullptr if not initialized
    static std::unique_ptr<IInputSource> createInputSource();
};

/// Convert Backend to string for debugging
constexpr const char* toString(Backend backend) noexcept {
    switch (backend) {
        case Backend::None:     return "None";
        case Backend::SDL2:     return "SDL2";
        case Backend::SDL3:     return "SDL3";
        case Backend::Headless: return "Headless";
    }
    return "Unknown";
}

} // namespace pal
