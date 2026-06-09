// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// Platform Abstraction Layer - SDL3 Host Clock Implementation

#include "pal/host_clock.h"
#include <SDL3/SDL.h>
#include <chrono>
#include <memory>
#include <thread>

namespace pal {
namespace sdl3 {

/// SDL3 host clock using steady_clock for driver-independent timing
class HostClockSDL3 : public IHostClock {
public:
    HostClockSDL3() = default;
    ~HostClockSDL3() override { shutdown(); }

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

} // namespace sdl3

// Factory function
std::unique_ptr<IHostClock> createHostClockSDL3() {
    return std::make_unique<sdl3::HostClockSDL3>();
}

} // namespace pal
