// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// Platform Abstraction Layer - SDL2 Context Implementation

#include "pal/context.h"
#include "pal/window.h"
#include <SDL.h>
#include <memory>

namespace pal {
namespace sdl2 {

/// SDL2 rendering context (software surface or OpenGL)
class ContextSDL2 : public IContext {
public:
    explicit ContextSDL2(SDL_Window* window) : window_(window) {}

    ~ContextSDL2() override { destroy(); }

    // ═══════════════════════════════════════════════════════════════════════
    // Creation
    // ═══════════════════════════════════════════════════════════════════════

    Result createSoftware(uint32_t width, uint32_t height, PixelFormat fmt) override {
        if (type_ != ContextType::None) {
            return Result::AlreadyInitialized;
        }
        if (!window_) {
            return Result::NotInitialized;
        }
        if (width == 0 || height == 0) {
            return Result::InvalidParameter;
        }
        if (fmt == PixelFormat::Unknown) {
            return Result::InvalidParameter;
        }

        // Get the window surface
        surface_ = SDL_GetWindowSurface(window_);
        if (!surface_) {
            return Result::NotSupported;
        }

        // Store requested dimensions (may differ from surface)
        requested_width_ = width;
        requested_height_ = height;
        format_ = fmt;
        type_ = ContextType::Software;

        return Result::Success;
    }

    Result createOpenGL(int major, int minor, bool core_profile) override {
        if (type_ != ContextType::None) {
            return Result::AlreadyInitialized;
        }
        if (!window_) {
            return Result::NotInitialized;
        }

        // Set OpenGL attributes
        SDL_GL_SetAttribute(SDL_GL_CONTEXT_MAJOR_VERSION, major);
        SDL_GL_SetAttribute(SDL_GL_CONTEXT_MINOR_VERSION, minor);

        if (core_profile) {
            SDL_GL_SetAttribute(SDL_GL_CONTEXT_PROFILE_MASK, SDL_GL_CONTEXT_PROFILE_CORE);
        } else {
            SDL_GL_SetAttribute(SDL_GL_CONTEXT_PROFILE_MASK, SDL_GL_CONTEXT_PROFILE_COMPATIBILITY);
        }

        SDL_GL_SetAttribute(SDL_GL_DOUBLEBUFFER, 1);
        SDL_GL_SetAttribute(SDL_GL_DEPTH_SIZE, 24);

        // Create the OpenGL context
        gl_context_ = SDL_GL_CreateContext(window_);
        if (!gl_context_) {
            return Result::NotSupported;
        }

        type_ = ContextType::OpenGL;
        return Result::Success;
    }

    void destroy() override {
        if (gl_context_) {
            SDL_GL_DeleteContext(gl_context_);
            gl_context_ = nullptr;
        }
        surface_ = nullptr;  // Surface is owned by window, don't free
        type_ = ContextType::None;
        locked_ = false;
    }

    bool isCreated() const override {
        return type_ != ContextType::None;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Software Context Operations
    // ═══════════════════════════════════════════════════════════════════════

    Result lockSurface(SoftwareContext& ctx) override {
        if (type_ != ContextType::Software) {
            return type_ == ContextType::None ? Result::NotInitialized : Result::InvalidOperation;
        }
        if (locked_) {
            return Result::AlreadyLocked;
        }

        // Refresh surface pointer (may change after resize)
        surface_ = SDL_GetWindowSurface(window_);
        if (!surface_) {
            return Result::NotSupported;
        }

        // Lock if needed
        if (SDL_MUSTLOCK(surface_)) {
            if (SDL_LockSurface(surface_) != 0) {
                return Result::NotSupported;
            }
        }

        ctx.pixels = surface_->pixels;
        ctx.pitch = static_cast<uint32_t>(surface_->pitch);
        ctx.width = static_cast<uint32_t>(surface_->w);
        ctx.height = static_cast<uint32_t>(surface_->h);
        ctx.format = sdlFormatToPixelFormat(surface_->format->format);

        locked_ = true;
        return Result::Success;
    }

    void unlockSurface() override {
        if (locked_ && surface_) {
            if (SDL_MUSTLOCK(surface_)) {
                SDL_UnlockSurface(surface_);
            }
            locked_ = false;
        }
    }

    bool isLocked() const override {
        return locked_;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // OpenGL Context Operations
    // ═══════════════════════════════════════════════════════════════════════

    Result makeCurrent() override {
        if (type_ != ContextType::OpenGL) {
            return type_ == ContextType::None ? Result::NotInitialized : Result::InvalidOperation;
        }

        if (SDL_GL_MakeCurrent(window_, gl_context_) != 0) {
            return Result::NotSupported;
        }

        return Result::Success;
    }

    void swapBuffers() override {
        if (type_ == ContextType::OpenGL && window_) {
            SDL_GL_SwapWindow(window_);
        }
    }

    void* getProcAddress(const char* name) override {
        if (type_ != ContextType::OpenGL) {
            return nullptr;
        }
        return SDL_GL_GetProcAddress(name);
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Query
    // ═══════════════════════════════════════════════════════════════════════

    ContextType getType() const override {
        return type_;
    }

private:
    static PixelFormat sdlFormatToPixelFormat(Uint32 sdl_format) {
        switch (sdl_format) {
            case SDL_PIXELFORMAT_RGB565:
                return PixelFormat::RGB565;
            case SDL_PIXELFORMAT_RGB888:
            case SDL_PIXELFORMAT_RGB24:
                return PixelFormat::RGB888;
            case SDL_PIXELFORMAT_RGBA8888:
            case SDL_PIXELFORMAT_RGBA32:
                return PixelFormat::RGBA8888;
            case SDL_PIXELFORMAT_BGRA8888:
            case SDL_PIXELFORMAT_BGRA32:
                return PixelFormat::BGRA8888;
            case SDL_PIXELFORMAT_INDEX8:
                return PixelFormat::Indexed8;
            default:
                return PixelFormat::Unknown;
        }
    }

    SDL_Window* window_ = nullptr;
    SDL_Surface* surface_ = nullptr;
    SDL_GLContext gl_context_ = nullptr;
    ContextType type_ = ContextType::None;
    bool locked_ = false;

    uint32_t requested_width_ = 0;
    uint32_t requested_height_ = 0;
    PixelFormat format_ = PixelFormat::Unknown;
};

} // namespace sdl2

// Factory function
std::unique_ptr<IContext> createContextSDL2(IWindow& window) {
    SDL_Window* sdl_window = static_cast<SDL_Window*>(window.getNativeHandle());
    return std::make_unique<sdl2::ContextSDL2>(sdl_window);
}

} // namespace pal
