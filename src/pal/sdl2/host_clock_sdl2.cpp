// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// Platform Abstraction Layer - SDL2 Host Clock Implementation

#include "pal/host_clock.h"
#include <SDL.h>
#include <memory>

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

        // Get performance counter frequency for microsecond timing
        perf_frequency_ = SDL_GetPerformanceFrequency();
        if (perf_frequency_ == 0) {
            perf_frequency_ = 1000000;  // Fallback to microseconds
        }

        // Record start time
        start_ticks_ms_ = SDL_GetTicks();
        start_perf_counter_ = SDL_GetPerformanceCounter();

        initialized_ = true;
        return Result::Success;
    }

    void shutdown() override {
        initialized_ = false;
        start_ticks_ms_ = 0;
        start_perf_counter_ = 0;
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
        return SDL_GetTicks() - start_ticks_ms_;
    }

    uint64_t getTicksUs() const override {
        if (!initialized_) {
            return 0;
        }

        uint64_t current = SDL_GetPerformanceCounter();
        uint64_t elapsed = current - start_perf_counter_;

        // Convert to microseconds: elapsed * 1000000 / frequency
        // Use 128-bit math to avoid overflow on long-running sessions
        return (elapsed * 1000000ULL) / perf_frequency_;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Sleep
    // ═══════════════════════════════════════════════════════════════════════

    void sleepMs(uint32_t ms) override {
        if (ms > 0) {
            SDL_Delay(ms);
        }
    }

    void sleepUs(uint64_t us) override {
        // SDL_Delay only supports milliseconds, so we round up
        if (us > 0) {
            uint32_t ms = static_cast<uint32_t>((us + 999) / 1000);
            SDL_Delay(ms);
        }
    }

private:
    bool initialized_ = false;
    uint32_t start_ticks_ms_ = 0;
    uint64_t start_perf_counter_ = 0;
    uint64_t perf_frequency_ = 1000000;
};

} // namespace sdl2

// Factory function
std::unique_ptr<IHostClock> createHostClockSDL2() {
    return std::make_unique<sdl2::HostClockSDL2>();
}

} // namespace pal
