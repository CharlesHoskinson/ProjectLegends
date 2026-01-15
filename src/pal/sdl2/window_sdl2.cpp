// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// Platform Abstraction Layer - SDL2 Window Implementation

#include "pal/window.h"
#include <SDL.h>
#include <memory>
#include <string>

namespace pal {
namespace sdl2 {

/// SDL2 window wrapper
class WindowSDL2 : public IWindow {
public:
    WindowSDL2() = default;
    ~WindowSDL2() override { destroy(); }

    // ═══════════════════════════════════════════════════════════════════════
    // Lifecycle
    // ═══════════════════════════════════════════════════════════════════════

    Result create(const WindowConfig& config) override {
        if (window_) {
            return Result::AlreadyExists;
        }
        if (config.width == 0 || config.height == 0) {
            return Result::InvalidParameter;
        }

        // Build SDL window flags
        Uint32 flags = SDL_WINDOW_SHOWN;
        if (config.resizable) {
            flags |= SDL_WINDOW_RESIZABLE;
        }
        if (config.fullscreen) {
            flags |= SDL_WINDOW_FULLSCREEN_DESKTOP;
        }

        // Create the window
        window_ = SDL_CreateWindow(
            config.title ? config.title : "DOSBox-X",
            SDL_WINDOWPOS_CENTERED,
            SDL_WINDOWPOS_CENTERED,
            static_cast<int>(config.width),
            static_cast<int>(config.height),
            flags
        );

        if (!window_) {
            return Result::NotSupported;
        }

        width_ = config.width;
        height_ = config.height;
        fullscreen_ = config.fullscreen;
        vsync_ = config.vsync;

        return Result::Success;
    }

    void destroy() override {
        if (window_) {
            SDL_DestroyWindow(window_);
            window_ = nullptr;
        }
        width_ = 0;
        height_ = 0;
        fullscreen_ = false;
    }

    bool isCreated() const override {
        return window_ != nullptr;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Properties
    // ═══════════════════════════════════════════════════════════════════════

    Result resize(uint32_t width, uint32_t height) override {
        if (!window_) {
            return Result::NotInitialized;
        }
        if (width == 0 || height == 0) {
            return Result::InvalidParameter;
        }

        SDL_SetWindowSize(window_, static_cast<int>(width), static_cast<int>(height));
        width_ = width;
        height_ = height;

        return Result::Success;
    }

    Result setFullscreen(bool fullscreen) override {
        if (!window_) {
            return Result::NotInitialized;
        }

        Uint32 flags = fullscreen ? SDL_WINDOW_FULLSCREEN_DESKTOP : 0;
        if (SDL_SetWindowFullscreen(window_, flags) != 0) {
            return Result::NotSupported;
        }

        fullscreen_ = fullscreen;
        return Result::Success;
    }

    Result setTitle(const char* title) override {
        if (!window_) {
            return Result::NotInitialized;
        }
        if (title == nullptr) {
            return Result::InvalidParameter;
        }

        SDL_SetWindowTitle(window_, title);
        return Result::Success;
    }

    bool isFullscreen() const override {
        return fullscreen_;
    }

    void getSize(uint32_t& width, uint32_t& height) const override {
        if (window_) {
            int w, h;
            SDL_GetWindowSize(window_, &w, &h);
            width = static_cast<uint32_t>(w);
            height = static_cast<uint32_t>(h);
        } else {
            width = width_;
            height = height_;
        }
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Display Enumeration
    // ═══════════════════════════════════════════════════════════════════════

    uint32_t getDisplayCount() const override {
        int count = SDL_GetNumVideoDisplays();
        return count > 0 ? static_cast<uint32_t>(count) : 1;
    }

    Result getDisplayInfo(uint32_t index, DisplayInfo& info) const override {
        int count = SDL_GetNumVideoDisplays();
        if (static_cast<int>(index) >= count) {
            return Result::InvalidParameter;
        }

        SDL_DisplayMode mode;
        if (SDL_GetCurrentDisplayMode(static_cast<int>(index), &mode) != 0) {
            return Result::NotSupported;
        }

        info.width = static_cast<uint32_t>(mode.w);
        info.height = static_cast<uint32_t>(mode.h);
        info.refresh_rate = static_cast<float>(mode.refresh_rate);
        info.dpi_scale = 1.0f;  // SDL2 doesn't have easy DPI access

        // Get display name
        const char* name = SDL_GetDisplayName(static_cast<int>(index));
        info.name = name ? name : "Unknown Display";

        return Result::Success;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Presentation
    // ═══════════════════════════════════════════════════════════════════════

    Result present() override {
        if (!window_) {
            return Result::NotInitialized;
        }

        // For software rendering, update the window surface
        // For OpenGL, swapping is done via the context
        if (SDL_UpdateWindowSurface(window_) != 0) {
            // This may fail if using OpenGL - that's OK
            // The context's swapBuffers() handles that case
        }

        return Result::Success;
    }

    Result setVsync(bool vsync) override {
        vsync_ = vsync;
        // VSync is set per-context for OpenGL
        // For software rendering, it's controlled by the display
        return Result::Success;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Native Handle
    // ═══════════════════════════════════════════════════════════════════════

    void* getNativeHandle() const override {
        return window_;
    }

private:
    SDL_Window* window_ = nullptr;
    uint32_t width_ = 0;
    uint32_t height_ = 0;
    bool fullscreen_ = false;
    bool vsync_ = true;
};

} // namespace sdl2

// Factory function
std::unique_ptr<IWindow> createWindowSDL2() {
    return std::make_unique<sdl2::WindowSDL2>();
}

} // namespace pal
