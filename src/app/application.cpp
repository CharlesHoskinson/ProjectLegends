// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Application — full engine wiring: render, audio, input.

#include "app/application.h"
#include "app/cli_parser.h"
#include "app/config_parser.h"
#include "app/platform_dirs.h"
#include "app/scancode_map.h"

#include <algorithm>
#include <cstdio>
#include <cstring>

namespace legends {

Application::Application() = default;

Application::~Application() {
    shutdown();
}

ExitCode Application::init(int argc, char** argv) {
    // ── CLI ───────────────────────────────────────────────────────────────
    CLIOptions cli;
    if (!cli.parse(argc, argv)) {
        std::fprintf(stderr, "Error: %s\n", cli.error_message.c_str());
        CLIOptions::printUsage(argc > 0 ? argv[0] : "project_legends");
        return ExitCode::CLIParseFailed;
    }
    if (cli.show_version) {
        CLIOptions::printVersion();
        return ExitCode::Success;
    }
    if (cli.show_help) {
        CLIOptions::printUsage(argc > 0 ? argv[0] : "project_legends");
        return ExitCode::Success;
    }

    // ── Config file ──────────────────────────────────────────────────────
    ConfigParser config;
    if (!cli.conf_path.empty()) {
        if (!config.loadFile(cli.conf_path)) {
            std::fprintf(stderr, "Warning: Cannot open config file: %s\n",
                         cli.conf_path.c_str());
        }
    } else {
        config.loadDefaults(); // non-fatal if none found
    }

    // ── Platform ─────────────────────────────────────────────────────────
    auto result = pal::Platform::initialize(pal::Backend::SDL3);
    if (pal::failed(result)) {
        std::fprintf(stderr, "Error: Platform::initialize(SDL3) failed: %s\n",
                     pal::toString(result));
        return ExitCode::PlatformInitFailed;
    }

    // ── Window ───────────────────────────────────────────────────────────
    window_ = pal::Platform::createWindow();
    if (!window_) {
        std::fprintf(stderr, "Error: Failed to create window\n");
        return ExitCode::WindowCreateFailed;
    }

    pal::WindowConfig wincfg;
    wincfg.width  = 640;
    wincfg.height = 480;
    wincfg.title  = "Project Legends";
    result = window_->create(wincfg);
    if (pal::failed(result)) {
        std::fprintf(stderr, "Error: Window::create() failed: %s\n",
                     pal::toString(result));
        return ExitCode::WindowCreateFailed;
    }

    if (cli.fullscreen) {
        window_->setFullscreen(true);
    }

    // ── Software rendering context ───────────────────────────────────────
    context_ = pal::Platform::createContext(*window_);
    if (!context_) {
        std::fprintf(stderr, "Error: Failed to create context\n");
        return ExitCode::ContextCreateFailed;
    }
    result = context_->createSoftware(640, 480, pal::PixelFormat::RGB888);
    if (pal::failed(result)) {
        std::fprintf(stderr, "Error: createSoftware() failed: %s\n",
                     pal::toString(result));
        return ExitCode::ContextCreateFailed;
    }
    ctx_width_  = 640;
    ctx_height_ = 480;
    context_->setLogicalSize(640, 480);

    // ── Host clock ───────────────────────────────────────────────────────
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

    // ── Input source ─────────────────────────────────────────────────────
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

    // ── Audio sink (non-fatal) ───────────────────────────────────────────
    audio_sink_ = pal::Platform::createAudioSink();
    if (audio_sink_) {
        pal::AudioConfig acfg;
        acfg.sample_rate = 44100;
        acfg.channels    = 2;
        acfg.buffer_ms   = 50;
        auto ares = audio_sink_->open(acfg);
        if (pal::failed(ares)) {
            std::fprintf(stderr, "Warning: AudioSink::open() failed: %s (continuing without audio)\n",
                         pal::toString(ares));
            audio_sink_.reset();
        }
    }

    // ── DOSBox-X engine ──────────────────────────────────────────────────
    legends_config_t ecfg = LEGENDS_CONFIG_INIT;

    // CLI overrides > config file > defaults
    // Cycles
    if (cli.cycles != 0) {
        ecfg.cpu_cycles = cli.cycles;
    } else if (config.hasKey("cpu", "cycles")) {
        ecfg.cpu_cycles = static_cast<uint32_t>(config.getInt("cpu", "cycles", 0));
    }

    // Machine type — config file only overrides when CLI was not explicit
    {
        std::string mt = cli.machine_type;
        if (!cli.machine_type_explicit && config.hasKey("dosbox", "machine")) {
            mt = config.get("dosbox", "machine", "vga");
        }
        if (mt == "ega")       ecfg.machine_type = 1;
        else if (mt == "cga")  ecfg.machine_type = 2;
        else if (mt == "hercules") ecfg.machine_type = 3;
        else if (mt == "tandy")    ecfg.machine_type = 4;
        else                       ecfg.machine_type = 0; // vga
    }

    // Memory
    if (cli.memsize_kb != 640) {
        ecfg.memory_kb = cli.memsize_kb;
    } else if (config.hasKey("dosbox", "memsize")) {
        ecfg.memory_kb = static_cast<uint32_t>(config.getInt("dosbox", "memsize", 640));
    } else {
        ecfg.memory_kb = 640;
    }

    // Profile → deterministic flag
    ecfg.deterministic = (cli.profile == "deterministic") ? 1 : 0;

    // Config path
    std::string resolved_conf = config.getLoadedPath();
    if (!resolved_conf.empty()) {
        ecfg.config_path = resolved_conf.c_str();
    }

    legends_error_t err = legends_create(&ecfg, &engine_);
    if (err != LEGENDS_OK) {
        std::fprintf(stderr, "Error: legends_create() failed: %d\n", err);
        return ExitCode::EngineCreateFailed;
    }

    // ── Log callback ─────────────────────────────────────────────────────
    if (cli.log_enabled && engine_) {
        legends_set_log_callback(engine_,
            [](int level, const char* message, void* /*userdata*/) {
                const char* prefix = "INFO";
                if (level >= 3) prefix = "ERROR";
                else if (level >= 2) prefix = "WARN";
                else if (level >= 1) prefix = "DEBUG";
                std::fprintf(stderr, "[%s] %s\n", prefix, message);
            },
            nullptr);
    }

    return ExitCode::Success;
}

// ─────────────────────────────────────────────────────────────────────────────
// Run loop with frame pacing (Step 6)
// ─────────────────────────────────────────────────────────────────────────────

ExitCode Application::run() {
    running_ = true;

    constexpr uint64_t kTargetFrameUs = 16667; // ~60 FPS

    while (running_) {
        uint64_t frame_start = host_clock_ ? host_clock_->getTicksUs() : 0;

        if (!processEvents()) {
            break;
        }

        // Step engine ~16 ms of emulated time per frame
        legends_step_result_t step_result{};
        legends_step_ms(engine_, 16, &step_result);

        // Render framebuffer to window
        renderFrame();

        // Pump audio from engine to audio sink
        pumpAudio();

        // Frame pacing: spin-wait hybrid for accurate 60 FPS
        if (host_clock_) {
            uint64_t elapsed = host_clock_->getTicksUs() - frame_start;
            if (elapsed < kTargetFrameUs) {
                uint64_t remaining = kTargetFrameUs - elapsed;
                // OS sleep for the bulk of the wait (leave 1.5ms for spin)
                if (remaining > 2000) {
                    host_clock_->sleepUs(remaining - 1500);
                }
                // Spin-wait for the tail to hit the exact target
                while (host_clock_->getTicksUs() - frame_start < kTargetFrameUs) {
                    // spin
                }
            }
        }
    }

    return ExitCode::Success;
}

// ─────────────────────────────────────────────────────────────────────────────
// Events → engine input (Steps 4, 5, 9)
// ─────────────────────────────────────────────────────────────────────────────

// Modifier bitmask constants
static constexpr uint8_t kModLCtrl  = 0x01;
static constexpr uint8_t kModRCtrl  = 0x02;
static constexpr uint8_t kModCtrl   = kModLCtrl | kModRCtrl;

bool Application::processEvents() {
    if (!input_source_) return false;

    constexpr uint32_t kMaxEvents = 64;
    pal::InputEvent events[kMaxEvents];
    uint32_t count = input_source_->poll(events, kMaxEvents);

    for (uint32_t i = 0; i < count; ++i) {
        const auto& ev = events[i];

        switch (ev.type) {
            case pal::InputEventType::WindowClose:
                running_ = false;
                return false;

            case pal::InputEventType::KeyDown:
            case pal::InputEventType::KeyUp: {
                bool down = (ev.type == pal::InputEventType::KeyDown);

                // Track modifier state
                if (ev.key.scancode == 0xE0) { // Left Ctrl
                    if (down) modifiers_ |= kModLCtrl;
                    else      modifiers_ &= static_cast<uint8_t>(~kModLCtrl);
                }
                if (ev.key.scancode == 0xE4) { // Right Ctrl
                    if (down) modifiers_ |= kModRCtrl;
                    else      modifiers_ &= static_cast<uint8_t>(~kModRCtrl);
                }

                // ── Hotkey interception ──────────────────────────────

                if (down) {
                    // Ctrl+F10 — release mouse capture (Step 5)
                    if (ev.key.scancode == 0x43 && (modifiers_ & kModCtrl) && mouse_captured_) {
                        setMouseCaptured(false);
                        break;
                    }

                    // Volume hotkeys (Step 9) — Ctrl+Up / Ctrl+Down / Ctrl+M
                    if (modifiers_ & kModCtrl) {
                        if (ev.key.scancode == 0x52) { // Up arrow
                            volume_ = std::min(1.0f, volume_ + 0.1f);
                            muted_ = false;
                            if (audio_sink_) audio_sink_->setVolume(volume_);
                            break;
                        }
                        if (ev.key.scancode == 0x51) { // Down arrow
                            volume_ = std::max(0.0f, volume_ - 0.1f);
                            muted_ = false;
                            if (audio_sink_) audio_sink_->setVolume(volume_);
                            break;
                        }
                        if (ev.key.scancode == 0x10) { // M key (SDL scancode 0x10)
                            if (muted_) {
                                muted_ = false;
                                volume_ = pre_mute_vol_;
                            } else {
                                muted_ = true;
                                pre_mute_vol_ = volume_;
                                volume_ = 0.0f;
                            }
                            if (audio_sink_) audio_sink_->setVolume(volume_);
                            break;
                        }
                    }
                }

                // ── Forward to engine (Step 4: E0-prefix) ───────────
                if (!engine_) break;
                auto at = sdlScancodeToAT(ev.key.scancode);
                if (at.code != 0) {
                    if (at.extended) {
                        legends_key_event_ext(engine_, at.code, down ? 1 : 0);
                    } else {
                        legends_key_event(engine_, at.code, down ? 1 : 0);
                    }
                }
                break;
            }

            case pal::InputEventType::MouseMotion:
                if (engine_ && mouse_captured_) {
                    legends_mouse_event(engine_,
                        static_cast<int16_t>(ev.mouse_motion.dx),
                        static_cast<int16_t>(ev.mouse_motion.dy),
                        0);
                }
                break;

            case pal::InputEventType::MouseButtonDown:
            case pal::InputEventType::MouseButtonUp: {
                // Click to capture (Step 5)
                if (ev.type == pal::InputEventType::MouseButtonDown) {
                    if (!mouse_captured_ && ev.mouse_button.button == 1) {
                        setMouseCaptured(true);
                        break; // Don't forward this click
                    }
                    // Middle-click to release
                    if (mouse_captured_ && ev.mouse_button.button == 2) {
                        setMouseCaptured(false);
                        break;
                    }
                }

                // Only forward mouse button events when captured
                if (!engine_ || !mouse_captured_) break;
                uint8_t buttons = 0;
                if (ev.mouse_button.button == 1) buttons |= 0x01; // left
                if (ev.mouse_button.button == 3) buttons |= 0x02; // right
                if (ev.mouse_button.button == 2) buttons |= 0x04; // middle
                if (ev.type == pal::InputEventType::MouseButtonUp) buttons = 0;
                legends_mouse_event(engine_, 0, 0, buttons);
                break;
            }

            default:
                break;
        }
    }

    return running_;
}

// ─────────────────────────────────────────────────────────────────────────────
// Mouse capture helpers (Step 5)
// ─────────────────────────────────────────────────────────────────────────────

void Application::setMouseCaptured(bool captured) {
    mouse_captured_ = captured;
    if (input_source_) {
        input_source_->setMouseCapture(captured);
        input_source_->setRelativeMouseMode(captured);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Render: engine framebuffer → software context → screen (Step 7)
// ─────────────────────────────────────────────────────────────────────────────

void Application::renderFrame() {
    if (!engine_ || !context_) return;

    // Check dirty flag to avoid unnecessary blits
    int dirty = 0;
    legends_is_frame_dirty(engine_, &dirty);
    if (!dirty) return;

    // Query frame dimensions
    size_t   size_needed = 0;
    uint16_t fw = 0, fh = 0;
    legends_capture_rgb(engine_, nullptr, 0, &size_needed, &fw, &fh);
    if (size_needed == 0 || fw == 0 || fh == 0) return;

    // Resize capture buffer once (or when resolution changes)
    if (rgb_buffer_.size() < size_needed) {
        rgb_buffer_.resize(size_needed);
    }

    legends_capture_rgb(engine_, rgb_buffer_.data(),
                        rgb_buffer_.size(), &size_needed, &fw, &fh);

    // Dynamic resolution handling (Step 7): recreate context if engine
    // resolution changed
    if (fw != ctx_width_ || fh != ctx_height_) {
        context_->destroy();
        auto res = context_->createSoftware(fw, fh, pal::PixelFormat::RGB888);
        if (pal::failed(res)) return;
        ctx_width_  = fw;
        ctx_height_ = fh;
        // Step 8: Update logical presentation for aspect ratio
        context_->setLogicalSize(fw, fh);
    }

    // Lock the rendering surface
    pal::SoftwareContext sctx;
    auto res = context_->lockSurface(sctx);
    if (pal::failed(res)) return;

    // Blit RGB24 from engine into the surface.
    // After dynamic resize, context matches engine dimensions — fast path.
    const uint32_t sw = sctx.width;
    const uint32_t sh = sctx.height;
    const uint32_t bpp = pal::bytesPerPixel(sctx.format);

    if (fw == sw && fh == sh && bpp == 3) {
        // Fast path: sizes match, straight memcpy row-by-row
        for (uint32_t y = 0; y < sh; ++y) {
            std::memcpy(
                static_cast<uint8_t*>(sctx.pixels) + y * sctx.pitch,
                rgb_buffer_.data() + y * fw * 3,
                fw * 3);
        }
    } else {
        // Nearest-neighbour scale (fallback)
        for (uint32_t y = 0; y < sh; ++y) {
            uint32_t src_y = y * fh / sh;
            if (src_y >= fh) src_y = fh - 1;
            const uint8_t* src_row = rgb_buffer_.data() + src_y * fw * 3;
            uint8_t* dst_row = static_cast<uint8_t*>(sctx.pixels) + y * sctx.pitch;

            for (uint32_t x = 0; x < sw; ++x) {
                uint32_t src_x = x * fw / sw;
                if (src_x >= fw) src_x = fw - 1;
                const uint8_t* sp = src_row + src_x * 3;
                uint8_t* dp = dst_row + x * bpp;
                dp[0] = sp[0];
                dp[1] = sp[1];
                dp[2] = sp[2];
            }
        }
    }

    // unlockSurface() presents to screen
    context_->unlockSurface();
}

// ─────────────────────────────────────────────────────────────────────────────
// Audio: engine → audio sink
// ─────────────────────────────────────────────────────────────────────────────

void Application::pumpAudio() {
    if (!engine_ || !audio_sink_) return;

    size_t avail = 0;
    legends_capture_audio(engine_, nullptr, 0, &avail);
    if (avail == 0) return;

    if (audio_buffer_.size() < avail) {
        audio_buffer_.resize(avail);
    }

    size_t actual = 0;
    legends_capture_audio(engine_, audio_buffer_.data(), audio_buffer_.size(), &actual);
    if (actual == 0) return;

    // actual is int16_t element count; stereo frames = actual / 2
    uint32_t frames = static_cast<uint32_t>(actual) / 2;
    audio_sink_->pushSamples(audio_buffer_.data(), frames);
}

// ─────────────────────────────────────────────────────────────────────────────
// Shutdown
// ─────────────────────────────────────────────────────────────────────────────

void Application::shutdown() {
    if (engine_) {
        legends_destroy(engine_);
        engine_ = nullptr;
    }
    input_source_.reset();
    audio_sink_.reset();
    host_clock_.reset();
    context_.reset();
    window_.reset();
    pal::Platform::shutdown();
}

} // namespace legends
