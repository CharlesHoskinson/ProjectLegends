// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// Platform Abstraction Layer - Headless Context Implementation

#include "pal/context.h"
#include "pal/window.h"
#include <cstring>
#include <memory>
#include <vector>

namespace pal {
namespace headless {

/// Headless context - memory buffer for software, stub for OpenGL
class ContextHeadless : public IContext {
public:
    ContextHeadless() = default;
    ~ContextHeadless() override { destroy(); }

    // ═══════════════════════════════════════════════════════════════════════
    // Creation
    // ═══════════════════════════════════════════════════════════════════════

    Result createSoftware(uint32_t width, uint32_t height, PixelFormat fmt) override {
        if (created_) {
            return Result::AlreadyInitialized;
        }
        if (width == 0 || height == 0) {
            return Result::InvalidParameter;
        }
        if (fmt == PixelFormat::Unknown) {
            return Result::InvalidParameter;
        }

        uint32_t bpp = bytesPerPixel(fmt);
        if (bpp == 0) {
            return Result::InvalidParameter;
        }

        // Allocate pixel buffer
        pitch_ = width * bpp;
        // Align pitch to 4 bytes for efficient access
        pitch_ = (pitch_ + 3) & ~3u;

        try {
            buffer_.resize(static_cast<size_t>(pitch_) * height);
        } catch (...) {
            return Result::OutOfMemory;
        }

        width_ = width;
        height_ = height;
        format_ = fmt;
        type_ = ContextType::Software;
        created_ = true;

        return Result::Success;
    }

    Result createOpenGL(int major, int minor, bool core_profile) override {
        if (created_) {
            return Result::AlreadyInitialized;
        }

        // Headless doesn't support real OpenGL
        // But we can pretend for testing purposes
        gl_major_ = major;
        gl_minor_ = minor;
        gl_core_ = core_profile;
        type_ = ContextType::OpenGL;
        created_ = true;

        return Result::Success;
    }

    void destroy() override {
        buffer_.clear();
        buffer_.shrink_to_fit();
        width_ = 0;
        height_ = 0;
        pitch_ = 0;
        format_ = PixelFormat::Unknown;
        type_ = ContextType::None;
        locked_ = false;
        created_ = false;
    }

    bool isCreated() const override {
        return created_;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Software Context Operations
    // ═══════════════════════════════════════════════════════════════════════

    Result lockSurface(SoftwareContext& ctx) override {
        if (!created_) {
            return Result::NotInitialized;
        }
        if (type_ != ContextType::Software) {
            return Result::InvalidOperation;
        }
        if (locked_) {
            return Result::AlreadyLocked;
        }

        ctx.pixels = buffer_.data();
        ctx.pitch = pitch_;
        ctx.width = width_;
        ctx.height = height_;
        ctx.format = format_;
        locked_ = true;

        return Result::Success;
    }

    void unlockSurface() override {
        locked_ = false;
    }

    bool isLocked() const override {
        return locked_;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // OpenGL Context Operations
    // ═══════════════════════════════════════════════════════════════════════

    Result makeCurrent() override {
        if (!created_) {
            return Result::NotInitialized;
        }
        if (type_ != ContextType::OpenGL) {
            return Result::InvalidOperation;
        }
        // No-op for headless
        return Result::Success;
    }

    void swapBuffers() override {
        // No-op for headless
    }

    void* getProcAddress(const char* name) override {
        // Headless has no real GL - return nullptr
        (void)name;
        return nullptr;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Query
    // ═══════════════════════════════════════════════════════════════════════

    ContextType getType() const override {
        return type_;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Test API
    // ═══════════════════════════════════════════════════════════════════════

    /// Get raw pixel buffer (for testing)
    const uint8_t* getPixelBuffer() const {
        return buffer_.data();
    }

    /// Get pixel buffer size (for testing)
    size_t getPixelBufferSize() const {
        return buffer_.size();
    }

private:
    bool created_ = false;
    bool locked_ = false;
    ContextType type_ = ContextType::None;

    // Software context state
    std::vector<uint8_t> buffer_;
    uint32_t width_ = 0;
    uint32_t height_ = 0;
    uint32_t pitch_ = 0;
    PixelFormat format_ = PixelFormat::Unknown;

    // OpenGL context state (for testing)
    int gl_major_ = 0;
    int gl_minor_ = 0;
    bool gl_core_ = false;
};

} // namespace headless

// Factory function (called by platform_headless.cpp)
std::unique_ptr<IContext> createContextHeadless(IWindow& /*window*/) {
    return std::make_unique<headless::ContextHeadless>();
}

} // namespace pal
