// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Application — top-level lifecycle for the interactive emulator.
// Creates PAL services, initializes the DOSBox-X engine, and drives
// the render / audio / input loop.

#pragma once

#include "app/action_bus.h"
#include "app/input_mapper.h"
#include "app/mount_manager.h"
#include "app/save_manager.h"
#include "app/menu_system.h"
#include "app/video_capture.h"
#include "app/mapper_ui.h"
#include "app/save_browser.h"
#include "app/joystick_mapper.h"
#include "app/shader_renderer.h"
#include "app/ai_config.h"
#include "app/ai_http_client.h"
#include "app/ai_panel.h"
#include "app/audio_mixer.h"
#include "app/midi_config.h"
#include "app/printer_manager.h"
#include "app/ttf_renderer.h"
#include "app/ipx_config.h"
#include "app/glide_config.h"
#include "app/pc98_config.h"
#include "app/file_logger.h"
#include "app/error_reporter.h"
#include "app/crash_breadcrumb.h"
#include "app/crash_reporter.h"
#include "app/update_checker.h"
#include "app/perf_overlay.h"

#include <pal/platform.h>
#include <legends/legends_embed.h>
#include <cstdint>
#include <memory>
#include <string>
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

    [[nodiscard]] ExitCode init(int argc, char** argv);
    [[nodiscard]] ExitCode run();

private:
    void shutdown();
    [[nodiscard]] bool processEvents();
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
    uint8_t  modifiers_      = 0;       // Bitmask: see kMod* constants

    // Modifier bitmask constants
    static constexpr uint8_t kModLCtrl  = 0x01;
    static constexpr uint8_t kModRCtrl  = 0x02;
    static constexpr uint8_t kModCtrl   = kModLCtrl | kModRCtrl;
    static constexpr uint8_t kModLShift = 0x04;
    static constexpr uint8_t kModRShift = 0x08;
    static constexpr uint8_t kModShift  = kModLShift | kModRShift;
    static constexpr uint8_t kModLAlt   = 0x10;
    static constexpr uint8_t kModRAlt   = 0x20;
    static constexpr uint8_t kModAlt    = kModLAlt | kModRAlt;

    // Volume control (Step 9)
    float    volume_         = 1.0f;
    float    pre_mute_vol_   = 1.0f;    // Volume before mute
    bool     muted_          = false;

    // Dynamic resolution (Step 7)
    uint16_t ctx_width_      = 640;
    uint16_t ctx_height_     = 480;

    // ── Phase 2 state ────────────────────────────────────────────────────

    ActionBus    action_bus_;
    InputMapper  input_mapper_;
    MountManager mount_manager_;
    SaveManager  save_manager_;
    MenuSystem   menu_system_;
    VideoCapture video_capture_;
    MapperUI     mapper_ui_;
    SaveBrowser  save_browser_;
    bool         paused_        = false;
    std::string  base_title_    = "Project Legends";

    // ── Phase 3 state ────────────────────────────────────────────────────

    // Sprint 1: Fullscreen + Joystick
    bool            fullscreen_     = false;
    JoystickMapper  joystick_mapper_;

    // Sprint 2: Shaders
    ShaderRenderer  shader_renderer_;
    bool            use_opengl_     = false;

    // Sprint 3: AI Assistant
    AIConfig        ai_config_;
    AIHttpClient    ai_http_client_;
    AIPanel         ai_panel_;

    // Sprint 4: MIDI
    MIDIConfig      midi_config_;

    // Sprint 5: Printer + TTF
    PrinterManager  printer_manager_;
    TTFRenderer     ttf_renderer_;

    // Sprint 6: IPX + 3dfx
    IPXConfig       ipx_config_;
    GlideConfig     glide_config_;

    // Sprint 7: PC-98
    PC98Config      pc98_config_;

    // ── Phase 4 state ────────────────────────────────────────────────────

    FileLogger      file_logger_;
    ErrorReporter   error_reporter_;
    std::unique_ptr<UpdateChecker> update_checker_;
    PerfOverlay     perf_overlay_;  // REQ-UX-005

    void registerActionHandlers();
    void updateWindowTitle();
};

} // namespace legends
