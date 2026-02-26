// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Application — implementation.

#include "app/application.h"

#include <cstdio>

namespace legends {

Application::Application() = default;

Application::~Application() {
    shutdown();
}

ExitCode Application::init() {
    // Initialize the SDL3 platform backend
    auto result = pal::Platform::initialize(pal::Backend::SDL3);
    if (pal::failed(result)) {
        std::fprintf(stderr, "Error: Platform::initialize(SDL3) failed: %s\n",
                     pal::toString(result));
        return ExitCode::PlatformInitFailed;
    }

    // Create window
    window_ = pal::Platform::createWindow();
    if (!window_) {
        std::fprintf(stderr, "Error: Failed to create window\n");
        return ExitCode::WindowCreateFailed;
    }

    pal::WindowConfig config;
    config.width  = 640;
    config.height = 480;
    config.title  = "Project Legends";
    result = window_->create(config);
    if (pal::failed(result)) {
        std::fprintf(stderr, "Error: Window::create() failed: %s\n",
                     pal::toString(result));
        return ExitCode::WindowCreateFailed;
    }

    // Create rendering context
    context_ = pal::Platform::createContext(*window_);
    if (!context_) {
        std::fprintf(stderr, "Error: Failed to create context\n");
        return ExitCode::ContextCreateFailed;
    }

    // Create host clock
    host_clock_ = pal::Platform::createHostClock();
    if (!host_clock_) {
        std::fprintf(stderr, "Error: Failed to create host clock\n");
        return ExitCode::ClockInitFailed;
    }
    result = host_clock_->initialize();
    if (pal::failed(result)) {
        std::fprintf(stderr, "Error: HostClock::initialize() failed: %s\n",
                     pal::toString(result));
        return ExitCode::ClockInitFailed;
    }

    // Create input source
    input_source_ = pal::Platform::createInputSource();
    if (!input_source_) {
        std::fprintf(stderr, "Error: Failed to create input source\n");
        return ExitCode::InputInitFailed;
    }
    result = input_source_->initialize();
    if (pal::failed(result)) {
        std::fprintf(stderr, "Error: InputSource::initialize() failed: %s\n",
                     pal::toString(result));
        return ExitCode::InputInitFailed;
    }

    // Create audio sink (optional — failure is non-fatal for Phase 0)
    audio_sink_ = pal::Platform::createAudioSink();

    return ExitCode::Success;
}

ExitCode Application::run() {
    running_ = true;

    while (running_) {
        if (!processEvents()) {
            break;
        }

        // Phase 0: no engine rendering — just pace the loop at ~60 fps
        if (host_clock_) {
            host_clock_->sleepMs(16);
        }
    }

    return ExitCode::Success;
}

bool Application::processEvents() {
    if (!input_source_) {
        return false;
    }

    constexpr uint32_t kMaxEvents = 64;
    pal::InputEvent events[kMaxEvents];
    uint32_t count = input_source_->poll(events, kMaxEvents);

    for (uint32_t i = 0; i < count; ++i) {
        if (events[i].type == pal::InputEventType::WindowClose) {
            running_ = false;
            return false;
        }
    }

    return running_;
}

void Application::shutdown() {
    input_source_.reset();
    audio_sink_.reset();
    host_clock_.reset();
    context_.reset();
    window_.reset();
    pal::Platform::shutdown();
}

} // namespace legends
