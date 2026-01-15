// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// Platform Abstraction Layer - Headless Host Clock Implementation

#include "pal/host_clock.h"
#include <atomic>
#include <memory>

namespace pal {
namespace headless {

/// Headless host clock - virtual time controlled programmatically
///
/// For testing, time does not advance automatically.
/// Use advanceTicks() or setTicks() to control time.
/// Sleep functions are non-blocking (return immediately).
class HostClockHeadless : public IHostClock {
public:
    HostClockHeadless() = default;
    ~HostClockHeadless() override { shutdown(); }

    // ═══════════════════════════════════════════════════════════════════════
    // Lifecycle
    // ═══════════════════════════════════════════════════════════════════════

    Result initialize() override {
        if (initialized_) {
            return Result::AlreadyInitialized;
        }
        ticks_us_ = 0;
        initialized_ = true;
        return Result::Success;
    }

    void shutdown() override {
        initialized_ = false;
        ticks_us_ = 0;
    }

    bool isInitialized() const override {
        return initialized_;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Time Query
    // ═══════════════════════════════════════════════════════════════════════

    uint64_t getTicksMs() const override {
        if (!initialized_) {
            return 0;
        }
        return ticks_us_ / 1000;
    }

    uint64_t getTicksUs() const override {
        if (!initialized_) {
            return 0;
        }
        return ticks_us_;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Sleep (Non-blocking in headless)
    // ═══════════════════════════════════════════════════════════════════════

    void sleepMs(uint32_t ms) override {
        // Non-blocking in headless mode
        // Optionally advance virtual time
        if (auto_advance_on_sleep_ && initialized_) {
            ticks_us_ += static_cast<uint64_t>(ms) * 1000;
        }
    }

    void sleepUs(uint64_t us) override {
        // Non-blocking in headless mode
        if (auto_advance_on_sleep_ && initialized_) {
            ticks_us_ += us;
        }
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Test API - Virtual Time Control
    // ═══════════════════════════════════════════════════════════════════════

    /// Set virtual time in microseconds
    void setTicksUs(uint64_t us) {
        ticks_us_ = us;
    }

    /// Advance virtual time by delta microseconds
    void advanceTicksUs(uint64_t delta_us) {
        ticks_us_ += delta_us;
    }

    /// Advance virtual time by delta milliseconds
    void advanceTicksMs(uint32_t delta_ms) {
        ticks_us_ += static_cast<uint64_t>(delta_ms) * 1000;
    }

    /// Enable/disable auto-advance on sleep calls
    void setAutoAdvanceOnSleep(bool enable) {
        auto_advance_on_sleep_ = enable;
    }

    /// Check if auto-advance is enabled
    bool isAutoAdvanceOnSleep() const {
        return auto_advance_on_sleep_;
    }

private:
    bool initialized_ = false;
    std::atomic<uint64_t> ticks_us_{0};
    bool auto_advance_on_sleep_ = false;
};

} // namespace headless

// Factory function (called by platform_headless.cpp)
std::unique_ptr<IHostClock> createHostClockHeadless() {
    return std::make_unique<headless::HostClockHeadless>();
}

} // namespace pal
