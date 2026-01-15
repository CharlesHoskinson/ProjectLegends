// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// Platform Abstraction Layer - Headless Window Implementation

#include "pal/window.h"
#include <cstring>
#include <memory>
#include <string>

namespace pal {
namespace headless {

/// Headless window - maintains virtual dimensions without OS resources
class WindowHeadless : public IWindow {
public:
    WindowHeadless() = default;
    ~WindowHeadless() override { destroy(); }

    // ═══════════════════════════════════════════════════════════════════════
    // Lifecycle
    // ═══════════════════════════════════════════════════════════════════════

    Result create(const WindowConfig& config) override {
        if (created_) {
            return Result::AlreadyExists;
        }
        if (config.width == 0 || config.height == 0) {
            return Result::InvalidParameter;
        }

        width_ = config.width;
        height_ = config.height;
        title_ = config.title ? config.title : "";
        fullscreen_ = config.fullscreen;
        vsync_ = config.vsync;
        created_ = true;

        return Result::Success;
    }

    void destroy() override {
        created_ = false;
        width_ = 0;
        height_ = 0;
        title_.clear();
        fullscreen_ = false;
    }

    bool isCreated() const override {
        return created_;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Properties
    // ═══════════════════════════════════════════════════════════════════════

    Result resize(uint32_t width, uint32_t height) override {
        if (!created_) {
            return Result::NotInitialized;
        }
        if (width == 0 || height == 0) {
            return Result::InvalidParameter;
        }

        width_ = width;
        height_ = height;
        return Result::Success;
    }

    Result setFullscreen(bool fullscreen) override {
        if (!created_) {
            return Result::NotInitialized;
        }
        fullscreen_ = fullscreen;
        return Result::Success;
    }

    Result setTitle(const char* title) override {
        if (!created_) {
            return Result::NotInitialized;
        }
        if (title == nullptr) {
            return Result::InvalidParameter;
        }
        title_ = title;
        return Result::Success;
    }

    bool isFullscreen() const override {
        return fullscreen_;
    }

    void getSize(uint32_t& width, uint32_t& height) const override {
        width = width_;
        height = height_;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Display Enumeration
    // ═══════════════════════════════════════════════════════════════════════

    uint32_t getDisplayCount() const override {
        // Headless always reports 1 virtual display
        return 1;
    }

    Result getDisplayInfo(uint32_t index, DisplayInfo& info) const override {
        if (index != 0) {
            return Result::InvalidParameter;
        }

        info.width = 1920;
        info.height = 1080;
        info.refresh_rate = 60.0f;
        info.dpi_scale = 1.0f;
        info.name = "Headless Display";

        return Result::Success;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Presentation
    // ═══════════════════════════════════════════════════════════════════════

    Result present() override {
        if (!created_) {
            return Result::NotInitialized;
        }
        // No-op for headless - nothing to present
        ++present_count_;
        return Result::Success;
    }

    Result setVsync(bool vsync) override {
        vsync_ = vsync;
        // NotSupported is a valid response for headless
        return Result::Success;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Native Handle
    // ═══════════════════════════════════════════════════════════════════════

    void* getNativeHandle() const override {
        // Return a sentinel value so tests can verify creation
        return created_ ? const_cast<WindowHeadless*>(this) : nullptr;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Test API
    // ═══════════════════════════════════════════════════════════════════════

    /// Get number of times present() was called (for testing)
    uint64_t getPresentCount() const { return present_count_; }

private:
    bool created_ = false;
    uint32_t width_ = 0;
    uint32_t height_ = 0;
    std::string title_;
    bool fullscreen_ = false;
    bool vsync_ = true;
    uint64_t present_count_ = 0;
};

} // namespace headless

// Factory function (called by platform_headless.cpp)
std::unique_ptr<IWindow> createWindowHeadless() {
    return std::make_unique<headless::WindowHeadless>();
}

} // namespace pal
