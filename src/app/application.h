// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Application — top-level lifecycle for the interactive emulator.
// Creates PAL services, initializes the DOSBox-X engine, and drives
// the render / audio / input loop.

#pragma once

#include <pal/platform.h>
#include <legends/legends_embed.h>
#include <cstdint>
#include <memory>
#include <vector>

namespace legends {

enum class ExitCode : int {
    Success = 0,
    PlatformInitFailed = 1,
    WindowCreateFailed = 2,
    ContextCreateFailed = 3,
    ClockInitFailed = 4,
    InputInitFailed = 5,
    AudioInitFailed = 6,
    EngineCreateFailed = 7,
    CLIParseFailed = 8,
};

class Application {
public:
    Application();
    ~Application();

    Application(const Application&) = delete;
    Application& operator=(const Application&) = delete;

    ExitCode init(int argc, char** argv);
    ExitCode run();

private:
    void shutdown();
    bool processEvents();
    void renderFrame();
    void pumpAudio();

    // ── Input helpers ────────────────────────────────────────────────────

    void setMouseCaptured(bool captured);

    // ── PAL services ─────────────────────────────────────────────────────

    std::unique_ptr<pal::IWindow>      window_;
    std::unique_ptr<pal::IContext>      context_;
    std::unique_ptr<pal::IAudioSink>    audio_sink_;
    std::unique_ptr<pal::IHostClock>    host_clock_;
    std::unique_ptr<pal::IInputSource>  input_source_;

    legends_handle engine_ = nullptr;
    bool running_ = false;

    // Reusable capture buffers (avoid per-frame allocation)
    std::vector<uint8_t>  rgb_buffer_;
    std::vector<int16_t>  audio_buffer_;

    // ── Phase 1 state ────────────────────────────────────────────────────

    // Mouse capture (Step 5)
    bool     mouse_captured_ = false;
    uint8_t  modifiers_      = 0;       // Bitmask: bit 0 = LCtrl

    // Volume control (Step 9)
    float    volume_         = 1.0f;
    float    pre_mute_vol_   = 1.0f;    // Volume before mute
    bool     muted_          = false;

    // Dynamic resolution (Step 7)
    uint16_t ctx_width_      = 640;
    uint16_t ctx_height_     = 480;
};

} // namespace legends
