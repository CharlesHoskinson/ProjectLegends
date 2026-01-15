// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// Platform Abstraction Layer - SDL3 Context Implementation
//
// Note: SDL3 deprecates SDL_GetWindowSurface(). Software rendering uses
// SDL_Renderer with a streaming texture instead.

#include "pal/context.h"
#include "pal/window.h"
#include <SDL3/SDL.h>
#include <memory>

namespace pal {
namespace sdl3 {

/// SDL3 rendering context (texture-based software or OpenGL)
class ContextSDL3 : public IContext {
public:
    explicit ContextSDL3(SDL_Window* window) : window_(window) {}

    ~ContextSDL3() override { destroy(); }

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

        // SDL3: Create software renderer
        renderer_ = SDL_CreateRenderer(window_, "software");
        if (!renderer_) {
            return Result::NotSupported;
        }

        // Determine SDL pixel format
        SDL_PixelFormat sdl_fmt = pixelFormatToSDL(fmt);

        // Create streaming texture for pixel access
        texture_ = SDL_CreateTexture(renderer_, sdl_fmt,
            SDL_TEXTUREACCESS_STREAMING,
            static_cast<int>(width), static_cast<int>(height));

        if (!texture_) {
            SDL_DestroyRenderer(renderer_);
            renderer_ = nullptr;
            return Result::OutOfMemory;
        }

        width_ = width;
        height_ = height;
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
            SDL_GL_DestroyContext(gl_context_);
            gl_context_ = nullptr;
        }
        if (texture_) {
            SDL_DestroyTexture(texture_);
            texture_ = nullptr;
        }
        if (renderer_) {
            SDL_DestroyRenderer(renderer_);
            renderer_ = nullptr;
        }
        type_ = ContextType::None;
        locked_pixels_ = nullptr;
        locked_pitch_ = 0;
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
        if (locked_pixels_) {
            return Result::AlreadyLocked;
        }

        // SDL3: Lock the texture for pixel access
        if (!SDL_LockTexture(texture_, nullptr, &locked_pixels_, &locked_pitch_)) {
            return Result::DeviceLost;
        }

        ctx.pixels = locked_pixels_;
        ctx.pitch = static_cast<uint32_t>(locked_pitch_);
        ctx.width = width_;
        ctx.height = height_;
        ctx.format = format_;

        return Result::Success;
    }

    void unlockSurface() override {
        if (!locked_pixels_ || !texture_) {
            return;
        }

        // Unlock texture
        SDL_UnlockTexture(texture_);
        locked_pixels_ = nullptr;
        locked_pitch_ = 0;

        // Present the texture to screen
        SDL_RenderClear(renderer_);
        SDL_RenderTexture(renderer_, texture_, nullptr, nullptr);
        SDL_RenderPresent(renderer_);
    }

    bool isLocked() const override {
        return locked_pixels_ != nullptr;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // OpenGL Context Operations
    // ═══════════════════════════════════════════════════════════════════════

    Result makeCurrent() override {
        if (type_ != ContextType::OpenGL) {
            return type_ == ContextType::None ? Result::NotInitialized : Result::InvalidOperation;
        }

        if (!SDL_GL_MakeCurrent(window_, gl_context_)) {
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
        return reinterpret_cast<void*>(SDL_GL_GetProcAddress(name));
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Query
    // ═══════════════════════════════════════════════════════════════════════

    ContextType getType() const override {
        return type_;
    }

private:
    static SDL_PixelFormat pixelFormatToSDL(PixelFormat fmt) {
        switch (fmt) {
            case PixelFormat::RGB565:
                return SDL_PIXELFORMAT_RGB565;
            case PixelFormat::RGB888:
                return SDL_PIXELFORMAT_RGB24;
            case PixelFormat::RGBA8888:
                return SDL_PIXELFORMAT_RGBA8888;
            case PixelFormat::BGRA8888:
                return SDL_PIXELFORMAT_BGRA8888;
            case PixelFormat::Indexed8:
                return SDL_PIXELFORMAT_INDEX8;
            default:
                return SDL_PIXELFORMAT_RGBA8888;
        }
    }

    SDL_Window* window_ = nullptr;
    SDL_Renderer* renderer_ = nullptr;
    SDL_Texture* texture_ = nullptr;
    SDL_GLContext gl_context_ = nullptr;
    ContextType type_ = ContextType::None;

    void* locked_pixels_ = nullptr;
    int locked_pitch_ = 0;

    uint32_t width_ = 0;
    uint32_t height_ = 0;
    PixelFormat format_ = PixelFormat::Unknown;
};

} // namespace sdl3

// Factory function
std::unique_ptr<IContext> createContextSDL3(IWindow& window) {
    SDL_Window* sdl_window = static_cast<SDL_Window*>(window.getNativeHandle());
    return std::make_unique<sdl3::ContextSDL3>(sdl_window);
}

} // namespace pal
