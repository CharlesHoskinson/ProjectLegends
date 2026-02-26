// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Application — top-level lifecycle for the interactive emulator.
// Creates PAL services, opens a window, and runs the event loop.

#pragma once

#include <pal/platform.h>
#include <legends/legends_embed.h>
#include <cstdint>
#include <memory>

namespace legends {

/// Exit codes returned by Application::init() and Application::run()
enum class ExitCode : int {
    Success = 0,
    PlatformInitFailed = 1,
    WindowCreateFailed = 2,
    ContextCreateFailed = 3,
    ClockInitFailed = 4,
    InputInitFailed = 5,
    AudioInitFailed = 6,
};

/// Top-level application class for the interactive SDL3 emulator.
///
/// Owns all PAL services and drives the main event loop.
/// Phase 0 goal: open a window and exit cleanly on close.
class Application {
public:
    Application();
    ~Application();

    Application(const Application&) = delete;
    Application& operator=(const Application&) = delete;

    /// Initialize PAL, create window and services.
    /// @return ExitCode::Success or a specific failure code
    ExitCode init();

    /// Run the main event loop until the window is closed.
    /// @return ExitCode::Success on clean exit
    ExitCode run();

private:
    /// Shut down all PAL services and destroy the window.
    void shutdown();

    /// Poll input events, handle WindowClose.
    /// @return true if the application should keep running
    bool processEvents();

    std::unique_ptr<pal::IWindow>      window_;
    std::unique_ptr<pal::IContext>     context_;
    std::unique_ptr<pal::IAudioSink>   audio_sink_;
    std::unique_ptr<pal::IHostClock>   host_clock_;
    std::unique_ptr<pal::IInputSource> input_source_;

    bool running_ = false;
};

} // namespace legends
