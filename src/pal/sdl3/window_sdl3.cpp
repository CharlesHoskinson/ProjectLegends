// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// Platform Abstraction Layer - SDL3 Window Implementation

#include "pal/window.h"
#include <SDL3/SDL.h>
#include <memory>
#include <string>

namespace pal {
namespace sdl3 {

/// SDL3 window wrapper
class WindowSDL3 : public IWindow {
public:
    WindowSDL3() = default;
    ~WindowSDL3() override { destroy(); }

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

        // Build SDL3 window flags
        SDL_WindowFlags flags = 0;
        if (config.resizable) {
            flags |= SDL_WINDOW_RESIZABLE;
        }
        if (config.fullscreen) {
            flags |= SDL_WINDOW_FULLSCREEN;
        }

        // SDL3: CreateWindow has no x,y parameters - uses SDL_WINDOWPOS_CENTERED by default
        window_ = SDL_CreateWindow(
            config.title ? config.title : "DOSBox-X",
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

        if (!SDL_SetWindowSize(window_, static_cast<int>(width), static_cast<int>(height))) {
            return Result::NotSupported;
        }
        width_ = width;
        height_ = height;

        return Result::Success;
    }

    Result setFullscreen(bool fullscreen) override {
        if (!window_) {
            return Result::NotInitialized;
        }

        if (!SDL_SetWindowFullscreen(window_, fullscreen)) {
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

        if (!SDL_SetWindowTitle(window_, title)) {
            return Result::NotSupported;
        }
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
        int count = 0;
        SDL_DisplayID* displays = SDL_GetDisplays(&count);
        if (displays) {
            SDL_free(displays);
        }
        return count > 0 ? static_cast<uint32_t>(count) : 1;
    }

    Result getDisplayInfo(uint32_t index, DisplayInfo& info) const override {
        int count = 0;
        SDL_DisplayID* displays = SDL_GetDisplays(&count);
        if (!displays || static_cast<int>(index) >= count) {
            if (displays) SDL_free(displays);
            return Result::InvalidParameter;
        }

        SDL_DisplayID display_id = displays[index];
        SDL_free(displays);

        const SDL_DisplayMode* mode = SDL_GetCurrentDisplayMode(display_id);
        if (!mode) {
            return Result::NotSupported;
        }

        info.width = static_cast<uint32_t>(mode->w);
        info.height = static_cast<uint32_t>(mode->h);
        info.refresh_rate = mode->refresh_rate;

        // Get DPI scale
        float dpi = SDL_GetDisplayContentScale(display_id);
        info.dpi_scale = dpi > 0.0f ? dpi : 1.0f;

        // Get display name
        const char* name = SDL_GetDisplayName(display_id);
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

        // In SDL3, presentation is done via renderer
        // This is handled by the context for software rendering
        // For OpenGL, swapBuffers handles it
        return Result::Success;
    }

    Result setVsync(bool vsync) override {
        vsync_ = vsync;
        // VSync is set per-context for OpenGL
        // For software rendering with renderer, use SDL_SetRenderVSync
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

} // namespace sdl3

// Factory function
std::unique_ptr<IWindow> createWindowSDL3() {
    return std::make_unique<sdl3::WindowSDL3>();
}

} // namespace pal
