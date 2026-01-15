// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// Platform Abstraction Layer - Window Interface

#pragma once

#include "pal/types.h"
#include <cstdint>

namespace pal {

/// Configuration for window creation
struct WindowConfig {
    uint32_t width = 640;
    uint32_t height = 480;
    const char* title = "DOSBox-X";
    bool fullscreen = false;
    bool resizable = true;
    bool vsync = true;
};

/// Information about a display/monitor
struct DisplayInfo {
    uint32_t width = 0;
    uint32_t height = 0;
    float refresh_rate = 60.0f;
    float dpi_scale = 1.0f;
    const char* name = "";
};

/// Window management interface
///
/// Provides window creation, property management, display enumeration,
/// and presentation. PAL provides the window; OUTPUT_* owns pixel production.
class IWindow {
public:
    virtual ~IWindow() = default;

    // ═══════════════════════════════════════════════════════════════════════
    // Lifecycle
    // ═══════════════════════════════════════════════════════════════════════

    /// Create window with given configuration
    /// @return Success, InvalidParameter (bad dimensions), AlreadyExists
    virtual Result create(const WindowConfig& config) = 0;

    /// Destroy window and release resources (safe to call if not created)
    virtual void destroy() = 0;

    /// Check if window has been created
    virtual bool isCreated() const = 0;

    // ═══════════════════════════════════════════════════════════════════════
    // Properties
    // ═══════════════════════════════════════════════════════════════════════

    /// Resize window to new dimensions
    /// @return Success, InvalidParameter (zero dimensions), NotInitialized
    virtual Result resize(uint32_t width, uint32_t height) = 0;

    /// Enter or exit fullscreen mode
    /// @return Success, NotSupported, NotInitialized
    virtual Result setFullscreen(bool fullscreen) = 0;

    /// Set window title
    /// @return Success, InvalidParameter (null title), NotInitialized
    virtual Result setTitle(const char* title) = 0;

    /// Check if window is in fullscreen mode
    virtual bool isFullscreen() const = 0;

    /// Get current window size
    virtual void getSize(uint32_t& width, uint32_t& height) const = 0;

    // ═══════════════════════════════════════════════════════════════════════
    // Display Enumeration
    // ═══════════════════════════════════════════════════════════════════════

    /// Get number of available displays (always >= 1)
    virtual uint32_t getDisplayCount() const = 0;

    /// Get information about a display
    /// @return Success, InvalidParameter (bad index)
    virtual Result getDisplayInfo(uint32_t index, DisplayInfo& info) const = 0;

    // ═══════════════════════════════════════════════════════════════════════
    // Presentation
    // ═══════════════════════════════════════════════════════════════════════

    /// Present the current frame (swap buffers / flip surface)
    /// @return Success, NotInitialized
    virtual Result present() = 0;

    /// Enable or disable vertical sync
    /// @return Success, NotSupported
    virtual Result setVsync(bool vsync) = 0;

    // ═══════════════════════════════════════════════════════════════════════
    // Native Handle
    // ═══════════════════════════════════════════════════════════════════════

    /// Get native window handle (SDL_Window*, HWND, etc.)
    /// @return Non-null if created, nullptr otherwise
    virtual void* getNativeHandle() const = 0;
};

} // namespace pal
