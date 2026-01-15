// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// Platform Abstraction Layer - SDL3 Host Clock Implementation

#include "pal/host_clock.h"
#include <SDL3/SDL.h>
#include <memory>

namespace pal {
namespace sdl3 {

/// SDL3 host clock using SDL_GetPerformanceCounter for high precision
class HostClockSDL3 : public IHostClock {
public:
    HostClockSDL3() = default;
    ~HostClockSDL3() override { shutdown(); }

    Result initialize() override {
        if (initialized_) {
            return Result::AlreadyInitialized;
        }

        // Get performance counter frequency
        perf_frequency_ = SDL_GetPerformanceFrequency();
        if (perf_frequency_ == 0) {
            return Result::NotSupported;
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
        // Use 128-bit arithmetic to avoid overflow
        return (elapsed * 1000000ULL) / perf_frequency_;
    }

    void sleepMs(uint32_t ms) override {
        SDL_Delay(ms);
    }

    void sleepUs(uint64_t us) override {
        // SDL3 has SDL_DelayNS for nanosecond precision
        SDL_DelayNS(us * 1000ULL);
    }

private:
    bool initialized_ = false;
    uint64_t start_ticks_ms_ = 0;
    uint64_t start_perf_counter_ = 0;
    uint64_t perf_frequency_ = 0;
};

} // namespace sdl3

// Factory function
std::unique_ptr<IHostClock> createHostClockSDL3() {
    return std::make_unique<sdl3::HostClockSDL3>();
}

} // namespace pal
