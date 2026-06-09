// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// Platform Abstraction Layer - SDL2 Host Clock Implementation

#include "pal/host_clock.h"
#include <SDL.h>
#include <chrono>
#include <memory>
#include <thread>

namespace pal {
namespace sdl2 {

/// SDL2 host clock using SDL_GetTicks and SDL_GetPerformanceCounter
class HostClockSDL2 : public IHostClock {
public:
    HostClockSDL2() = default;
    ~HostClockSDL2() override { shutdown(); }

    // ═══════════════════════════════════════════════════════════════════════
    // Lifecycle
    // ═══════════════════════════════════════════════════════════════════════

    Result initialize() override {
        if (initialized_) {
            return Result::AlreadyInitialized;
        }

        start_time_ = Clock::now();
        initialized_ = true;
        return Result::Success;
    }

    void shutdown() override {
        initialized_ = false;
        start_time_ = Clock::time_point{};
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
        auto elapsed = Clock::now() - start_time_;
        return static_cast<uint64_t>(
            std::chrono::duration_cast<std::chrono::milliseconds>(elapsed).count());
    }

    uint64_t getTicksUs() const override {
        if (!initialized_) {
            return 0;
        }

        auto elapsed = Clock::now() - start_time_;
        return static_cast<uint64_t>(
            std::chrono::duration_cast<std::chrono::microseconds>(elapsed).count());
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Sleep
    // ═══════════════════════════════════════════════════════════════════════

    void sleepMs(uint32_t ms) override {
        if (ms > 0) {
            std::this_thread::sleep_for(std::chrono::milliseconds(ms));
        }
    }

    void sleepUs(uint64_t us) override {
        if (us > 0) {
            std::this_thread::sleep_for(std::chrono::microseconds(us));
        }
    }

private:
    using Clock = std::chrono::steady_clock;

    bool initialized_ = false;
    Clock::time_point start_time_{};
};

} // namespace sdl2

// Factory function
std::unique_ptr<IHostClock> createHostClockSDL2() {
    return std::make_unique<sdl2::HostClockSDL2>();
}

} // namespace pal
