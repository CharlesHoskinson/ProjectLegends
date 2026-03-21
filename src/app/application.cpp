// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Application — full engine wiring: render, audio, input, Phase 2 actions.

#include "app/application.h"
#include "app/cli_parser.h"
#include "app/config_parser.h"
#include "app/platform_dirs.h"
#include "app/portable_mode.h"
#include "app/scancode_map.h"
#include "app/capture.h"
#include "app/input_mapper.h"
#include "app/save_manager.h"
#include "app/menu_system.h"
#include "app/hotkey_dispatcher.h"
#include "app/ai_screen_context.h"
#include "app/shader_presets.h"

#include <algorithm>
#include <csignal>
#include <cstdio>
#include <cstring>
#include <filesystem>

namespace legends {

// REQ-UX-010: Crash autosave globals (signal handlers can only access globals)
static legends_handle g_crash_engine = nullptr;
static SaveManager*   g_crash_save_mgr = nullptr;

static void crash_autosave_handler(int sig) {
    // Attempt a best-effort save — this is async-signal-unsafe but better
    // than losing all progress. The save path uses atomic writes.
    if (g_crash_engine && g_crash_save_mgr) {
        g_crash_save_mgr->saveToSlot(g_crash_engine, SaveManager::kAutosaveSlot,
                                      nullptr, 0, 0);
    }
    // Re-raise the signal with default handler
    std::signal(sig, SIG_DFL);
    std::raise(sig);
}

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

    // ── Rendering context ─────────────────────────────────────────────────
    // CLI --opengl overrides config
    if (cli.opengl) {
        use_opengl_ = true;
    }

    context_ = pal::Platform::createContext(*window_);
    if (!context_) {
        std::fprintf(stderr, "Error: Failed to create context\n");
        return ExitCode::ContextCreateFailed;
    }

    if (use_opengl_) {
        result = context_->createOpenGL(3, 3, true);
        if (pal::failed(result)) {
            std::fprintf(stderr,
                "Warning: OpenGL context creation failed (%s), falling back to software\n",
                pal::toString(result));
            use_opengl_ = false;
        }
    }

    if (!use_opengl_) {
        result = context_->createSoftware(640, 480, pal::PixelFormat::RGB888);
        if (pal::failed(result)) {
            std::fprintf(stderr, "Error: createSoftware() failed: %s\n",
                         pal::toString(result));
            return ExitCode::ContextCreateFailed;
        }
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
        else if (mt == "pc98")     ecfg.machine_type = 5;
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

    // ── REQ-UX-010: Crash autosave ─────────────────────────────────────
    g_crash_engine = engine_;
    g_crash_save_mgr = &save_manager_;
    std::signal(SIGSEGV, crash_autosave_handler);
    std::signal(SIGABRT, crash_autosave_handler);
#ifndef _WIN32
    std::signal(SIGBUS, crash_autosave_handler);
#endif

    // Check for previous crash autosave and offer recovery
    if (save_manager_.hasAutosave()) {
        std::fprintf(stderr, "Crash recovery save detected — loading autosave\n");
        if (save_manager_.recoverAutosave(engine_)) {
            std::fprintf(stderr, "Crash recovery successful\n");
        } else {
            std::fprintf(stderr, "Crash recovery failed: %s\n",
                         save_manager_.lastError().c_str());
        }
    }

    // ── Phase 4: Structured logging ─────────────────────────────────────
    if (cli.log_enabled) {
        std::string log_path = cli.log_file;
        if (log_path.empty()) {
            log_path = getLogDir() + "/legends.jsonl";
        }
        file_logger_.setMinLevel(parseLogLevel(cli.log_level.c_str()));
        if (file_logger_.open(log_path)) {
            file_logger_.log(LogLevel::Info, "Project Legends starting");
        } else {
            error_reporter_.report(ErrorSeverity::Warning,
                "Failed to open log file: " + log_path);
        }
    }

    // ── Phase 4: Crash reporting (opt-in) ────────────────────────────────
    if (cli.crash_reporting) {
        std::string crash_dir = getDataDir() + "/crashes";
        if (!globalCrashReporter().enable(crash_dir)) {
            error_reporter_.report(ErrorSeverity::Warning,
                "Failed to enable crash reporting");
        }
        LEGENDS_BREADCRUMB("Application initialized");
    }

    // ── Phase 4: Update checker (opt-in) ────────────────────────────────
    if (!cli.no_update_check) {
        update_checker_ = createPlatformUpdateChecker();
        if (update_checker_) {
            update_checker_->setEnabled(true);
            update_checker_->checkForUpdate();
        }
    }

    // ── Log callback ─────────────────────────────────────────────────────
    if (cli.log_enabled && engine_) {
        if (file_logger_.isOpen()) {
            legends_set_log_callback(engine_,
                FileLogger::engineLogCallback, &file_logger_);
        } else {
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
    }

    // ── Action handlers ──────────────────────────────────────────────────
    registerActionHandlers();

    // ── Input mapper ─────────────────────────────────────────────────────
    {
        std::string mapper_path = getConfigDir() + "/mapper.txt";
        input_mapper_.loadFromFile(mapper_path); // non-fatal if missing
    }

    // ── Menu system ──────────────────────────────────────────────────────
    menu_system_.initialize(&action_bus_);

    // ── Visual UI overlays ────────────────────────────────────────────────
    mapper_ui_.initialize(&action_bus_, &input_mapper_);
    save_browser_.initialize(&action_bus_, &save_manager_);

    // ── Mount drives from CLI ────────────────────────────────────────────
    for (const auto& mount_arg : cli.mount_args) {
        auto parsed = MountManager::parseMountArg(mount_arg);
        if (!parsed) {
            std::fprintf(stderr, "Warning: Invalid --mount argument: %s\n",
                         mount_arg.c_str());
            continue;
        }
        auto type = MountManager::detectMountType(parsed->host_path);
        bool ok = false;
        if (type == MountType::Directory) {
            ok = mount_manager_.mountLocal(parsed->letter, parsed->host_path);
        } else {
            ok = mount_manager_.mountImage(parsed->letter, parsed->host_path, type);
        }
        if (ok && engine_) {
            legends_mount_drive(engine_, parsed->letter,
                               parsed->host_path.c_str(), 0);
            std::fprintf(stderr, "Mounted %c: -> %s\n",
                         parsed->letter, parsed->host_path.c_str());
        } else if (!ok) {
            std::fprintf(stderr, "Warning: Failed to mount %c: %s\n",
                         parsed->letter, mount_manager_.lastError().c_str());
        }
    }

    // ── Phase 3: Enhanced Features config ────────────────────────────────

    // Sprint 2: Shader config (CLI --opengl already set use_opengl_ above)
    if (!use_opengl_) {
        std::string renderer = config.get("render", "renderer", "software");
        use_opengl_ = (renderer == "opengl");
    }

    // Sprint 3: AI config
    ai_config_.loadFrom(config);
    ai_panel_.initialize(&action_bus_);

    // Sprint 4: MIDI config
    midi_config_.loadFrom(config);
    if (midi_config_.device != MIDIDevice::None && engine_) {
        legends_midi_set_device(engine_, MIDIConfig::deviceName(midi_config_.device));
        if (!midi_config_.soundfont_path.empty()) {
            legends_midi_set_soundfont(engine_, midi_config_.soundfont_path.c_str());
        }
        if (!midi_config_.mt32_romdir.empty()) {
            legends_midi_set_romdir(engine_, midi_config_.mt32_romdir.c_str());
        }
    }

    // Sprint 5: Printer + TTF config
    {
        std::string printer_dir = config.get("printer", "output", "");
        if (!printer_dir.empty()) {
            printer_manager_.setOutputDirectory(printer_dir);
            printer_manager_.setEnabled(config.getBool("printer", "enabled", false));
            if (printer_manager_.isEnabled() && engine_) {
                legends_printer_set_output(engine_, printer_dir.c_str());
            }
        }

        std::string ttf_path = config.get("ttf", "font", "");
        if (!ttf_path.empty()) {
            uint32_t ttf_size = static_cast<uint32_t>(config.getInt("ttf", "size", 16));
            ttf_renderer_.loadFont(ttf_path, ttf_size);
            ttf_renderer_.setEnabled(config.getBool("ttf", "enabled", false));
            if (ttf_renderer_.isEnabled() && engine_) {
                legends_set_ttf_font(engine_, ttf_path.c_str(), ttf_size);
            }
        }
    }

    // Sprint 6: IPX + Glide config
    ipx_config_.loadFrom(config);
    glide_config_.loadFrom(config);
    if (glide_config_.enabled) {
        use_opengl_ = true; // Glide requires OpenGL
    }

    // Sprint 7: PC-98 config
    pc98_config_.loadFrom(config);

    // Sprint 6: IPX — wire config to engine
    if (ipx_config_.enabled && engine_) {
        legends_ipx_enable(engine_, 1);
        if (!ipx_config_.server.empty()) {
            legends_ipx_connect(engine_, ipx_config_.server.c_str(), ipx_config_.port);
        }
    }

    // Sprint 6: Glide — wire config to engine
    if (glide_config_.enabled && engine_) {
        legends_glide_enable(engine_, 1);
        legends_glide_set_resolution(engine_, glide_config_.width, glide_config_.height);
    }

    // Sprint 7: PC-98 — wire config to engine
    if (pc98_config_.enabled && engine_) {
        legends_set_machine_pc98(engine_, 1);
    }

    return ExitCode::Success;
}

// ─────────────────────────────────────────────────────────────────────────────
// Run loop with frame pacing and pause support
// ─────────────────────────────────────────────────────────────────────────────

ExitCode Application::run() {
    running_ = true;

    constexpr uint64_t kTargetFrameUs = 16667; // ~60 FPS
    // REQ-QA-001: Cap maximum elapsed time per frame to prevent physics/logic
    // jumps after OS suspend/resume or debugger pause.
    constexpr uint64_t kMaxFrameUs = 100000;  // 100 ms (10 FPS minimum)

    while (running_) {
        uint64_t frame_start = host_clock_ ? host_clock_->getTicksUs() : 0;

        if (!processEvents()) {
            break;
        }

        // Step engine ~16 ms of emulated time per frame (skip when paused)
        bool step_ok = true;
        if (!paused_ && !menu_system_.isOpen()) {
            legends_step_result_t step_result{};
            legends_error_t step_err = legends_step_ms(engine_, 16, &step_result);
            // REQ-QA-005: Check step result for errors. On error frames,
            // suppress capture and audio to avoid processing stale data.
            if (step_err != LEGENDS_OK) {
                step_ok = false;
                std::fprintf(stderr, "Warning: legends_step_ms returned error %d\n",
                             static_cast<int>(step_err));
            }
        }

        // REQ-UX-005: Record frame delta for performance overlay
        if (host_clock_) {
            uint64_t elapsed = host_clock_->getTicksUs() - frame_start;
            // REQ-QA-001: Clamp elapsed time to prevent logic jumps after
            // OS suspend/resume or debugger pause.
            if (elapsed > kMaxFrameUs) {
                elapsed = kMaxFrameUs;
            }
            perf_overlay_.recordFrame(elapsed);
            if (engine_) {
                uint64_t total_cycles = 0;
                legends_get_total_cycles(engine_, &total_cycles);
                // Rough estimate: cycles executed this frame / 16ms
                perf_overlay_.setCyclesPerSec(total_cycles > 0 ? total_cycles * 60 : 0);
            }
            if (audio_sink_) {
                uint32_t queued = audio_sink_->getQueuedFrames();
                uint32_t ms = (queued * 1000) / 44100;
                perf_overlay_.setAudioQueuedMs(ms);
            }
        }

        // Render framebuffer to window (suppress on error frames per REQ-QA-005)
        if (step_ok) {
            renderFrame();
        }

        // Pump audio from engine to audio sink (suppress on error frames per REQ-QA-005)
        if (step_ok) {
            pumpAudio();
        }

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
// Events → engine input (Phase 1 + Phase 2 hotkeys via ActionBus)
// ─────────────────────────────────────────────────────────────────────────────

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

                // Track all modifier state
                if (ev.key.scancode == 0xE0) { // Left Ctrl
                    if (down) modifiers_ |= kModLCtrl;
                    else      modifiers_ &= static_cast<uint8_t>(~kModLCtrl);
                }
                if (ev.key.scancode == 0xE4) { // Right Ctrl
                    if (down) modifiers_ |= kModRCtrl;
                    else      modifiers_ &= static_cast<uint8_t>(~kModRCtrl);
                }
                if (ev.key.scancode == 0xE1) { // Left Shift
                    if (down) modifiers_ |= kModLShift;
                    else      modifiers_ &= static_cast<uint8_t>(~kModLShift);
                }
                if (ev.key.scancode == 0xE5) { // Right Shift
                    if (down) modifiers_ |= kModRShift;
                    else      modifiers_ &= static_cast<uint8_t>(~kModRShift);
                }
                if (ev.key.scancode == 0xE2) { // Left Alt
                    if (down) modifiers_ |= kModLAlt;
                    else      modifiers_ &= static_cast<uint8_t>(~kModLAlt);
                }
                if (ev.key.scancode == 0xE6) { // Right Alt
                    if (down) modifiers_ |= kModRAlt;
                    else      modifiers_ &= static_cast<uint8_t>(~kModRAlt);
                }

                // ── AI panel input routing (when panel is open) ─────
                if (ai_panel_.isOpen() && !menu_system_.isOpen()) {
                    if (down) {
                        ai_panel_.handleKey(ev.key.scancode, true);
                    }
                    break; // Don't forward to engine while AI panel is open
                }

                // ── Mapper UI input routing (when mapper is open) ────
                if (mapper_ui_.isOpen()) {
                    if (down) {
                        mapper_ui_.handleKey(ev.key.scancode, true);
                    }
                    break; // Don't forward to engine while mapper is open
                }

                // ── Save browser input routing (when browser is open) ─
                if (save_browser_.isOpen()) {
                    if (down) {
                        save_browser_.handleKey(ev.key.scancode, true);
                    }
                    break; // Don't forward to engine while browser is open
                }

                // ── Menu input routing (when menu is open) ──────────
                if (menu_system_.isOpen()) {
                    if (down) {
                        menu_system_.handleKey(ev.key.scancode, true);
                    }
                    break; // Don't forward to engine while menu is open
                }

                // ── Hotkey interception (key-down only) ─────────────

                if (down) {
                    auto hk = matchHotkey(ev.key.scancode, modifiers_, mouse_captured_);
                    if (hk.matched) {
                        action_bus_.dispatch(hk.action, hk.param);
                        break;
                    }
                }

                // ── Forward to engine via InputMapper ────────────────
                if (!engine_) break;
                auto at = input_mapper_.translate(ev.key.scancode);
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
                if (engine_ && mouse_captured_ && !menu_system_.isOpen()) {
                    legends_mouse_event(engine_,
                        static_cast<int16_t>(ev.mouse_motion.dx),
                        static_cast<int16_t>(ev.mouse_motion.dy),
                        0);
                }
                break;

            case pal::InputEventType::MouseButtonDown:
            case pal::InputEventType::MouseButtonUp: {
                // Menu click routing
                if (menu_system_.isOpen() && ev.type == pal::InputEventType::MouseButtonDown) {
                    menu_system_.handleMouseClick(ev.mouse_button.x, ev.mouse_button.y);
                    break;
                }

                // Menu bar click routing (persistent bar, not full overlay)
                if (menu_system_.isBarVisible() && !menu_system_.isOpen() &&
                    ev.type == pal::InputEventType::MouseButtonDown) {
                    if (menu_system_.handleBarClick(ev.mouse_button.x, ev.mouse_button.y)) {
                        break;
                    }
                }

                // Click to capture
                if (ev.type == pal::InputEventType::MouseButtonDown) {
                    if (!mouse_captured_ && ev.mouse_button.button == 1) {
                        setMouseCaptured(true);
                        break;
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
                if (ev.mouse_button.button == 1) buttons |= 0x01;
                if (ev.mouse_button.button == 3) buttons |= 0x02;
                if (ev.mouse_button.button == 2) buttons |= 0x04;
                if (ev.type == pal::InputEventType::MouseButtonUp) buttons = 0;
                legends_mouse_event(engine_, 0, 0, buttons);
                break;
            }

            case pal::InputEventType::JoystickAxis: {
                if (!engine_) break;
                // PAL reports individual axis events; update mapper state
                uint8_t joy_id = ev.joy_axis.id;
                // Map axis index: 0=X, 1=Y
                auto prev = joystick_mapper_.state(joy_id);
                int16_t ax = (ev.joy_axis.axis == 0) ? ev.joy_axis.value
                             : static_cast<int16_t>(prev.axis_x * 256 - 32768);
                int16_t ay = (ev.joy_axis.axis == 1) ? ev.joy_axis.value
                             : static_cast<int16_t>(prev.axis_y * 256 - 32768);
                joystick_mapper_.update(joy_id, ax, ay, prev.buttons);
                auto js = joystick_mapper_.state(joy_id);
                legends_joystick_event(engine_, joy_id,
                    js.axis_x, js.axis_y, js.buttons);
                break;
            }

            case pal::InputEventType::JoystickButton: {
                if (!engine_) break;
                uint8_t joy_id = ev.joy_button.id;
                auto prev = joystick_mapper_.state(joy_id);
                uint8_t btns = prev.buttons;
                uint8_t mask = static_cast<uint8_t>(1u << ev.joy_button.button);
                if (ev.joy_button.pressed) {
                    btns |= mask;
                } else {
                    btns = static_cast<uint8_t>(btns & ~mask);
                }
                // Reconstruct axis values from stored state (already in DOS range)
                int16_t ax = static_cast<int16_t>(prev.axis_x * 256 - 32768);
                int16_t ay = static_cast<int16_t>(prev.axis_y * 256 - 32768);
                joystick_mapper_.update(joy_id, ax, ay, btns);
                auto js = joystick_mapper_.state(joy_id);
                legends_joystick_event(engine_, joy_id,
                    js.axis_x, js.axis_y, js.buttons);
                break;
            }

            // REQ-QA-002: Display hotplug — re-query display info
            case pal::InputEventType::DisplayChanged:
                if (window_ && window_->isCreated()) {
                    uint32_t w, h;
                    window_->getSize(w, h);
                    // If the window reported a valid size, keep going.
                    // The next renderFrame() will adapt if the context
                    // dimensions have changed.
                    (void)w; (void)h;
                }
                break;

            // REQ-QA-003: Audio device change — reopen audio sink
            case pal::InputEventType::AudioDeviceChanged:
                if (audio_sink_ && audio_sink_->isOpen()) {
                    auto cfg = audio_sink_->getConfig();
                    audio_sink_->close();
                    auto res = audio_sink_->open(cfg);
                    if (pal::failed(res)) {
                        std::fprintf(stderr,
                            "Warning: Audio device change — failed to reopen (%s)\n",
                            pal::toString(res));
                        audio_sink_.reset();
                    }
                }
                break;

            default:
                break;
        }
    }

    // Poll AI response if panel is open and waiting
    if (ai_panel_.isOpen() && ai_panel_.isWaiting()) {
        AIResponse response;
        if (ai_http_client_.pollResponse(response)) {
            ai_panel_.setWaiting(false);
            if (response.success) {
                ai_panel_.addResponse(response.body);
            } else {
                ai_panel_.addResponse("[Error] " + response.error);
            }
        }
    }

    return running_;
}

// ─────────────────────────────────────────────────────────────────────────────
// ActionBus handler registration (Phase 2)
// ─────────────────────────────────────────────────────────────────────────────

void Application::registerActionHandlers() {
    // Quit
    action_bus_.registerHandler(Action::Quit, [this](int) {
        running_ = false;
    });

    // Pause / Resume / Toggle
    action_bus_.registerHandler(Action::Pause, [this](int) {
        paused_ = true;
        updateWindowTitle();
    });
    action_bus_.registerHandler(Action::Resume, [this](int) {
        paused_ = false;
        updateWindowTitle();
    });
    action_bus_.registerHandler(Action::TogglePause, [this](int) {
        paused_ = !paused_;
        updateWindowTitle();
    });

    // Reset
    action_bus_.registerHandler(Action::Reset, [this](int) {
        if (engine_) {
            legends_reset(engine_);
            paused_ = false;
            updateWindowTitle();
        }
    });

    // Screenshot
    action_bus_.registerHandler(Action::Screenshot, [this](int) {
        if (!engine_) return;
        // Query framebuffer size
        size_t size_needed = 0;
        uint16_t w = 0, h = 0;
        legends_capture_rgb(engine_, nullptr, 0, &size_needed, &w, &h);
        if (size_needed == 0 || w == 0 || h == 0) return;
        std::vector<uint8_t> buf(size_needed);
        legends_capture_rgb(engine_, buf.data(), buf.size(), &size_needed, &w, &h);

        std::string dir = getCaptureDir();
        std::filesystem::create_directories(dir);
        std::string path = dir + "/" + generateCaptureFilename();
        if (writeScreenshotPNG(path, buf.data(), w, h)) {
            std::fprintf(stderr, "Screenshot saved: %s\n", path.c_str());
        } else {
            std::fprintf(stderr, "Screenshot failed: %s\n", path.c_str());
        }
    });

    // Save state
    action_bus_.registerHandler(Action::SaveState, [this](int slot) {
        if (!engine_ || slot < 1 || slot > SaveManager::kMaxSlots) return;
        // Get thumbnail for the save
        size_t size_needed = 0;
        uint16_t w = 0, h = 0;
        legends_capture_rgb(engine_, nullptr, 0, &size_needed, &w, &h);
        std::vector<uint8_t> thumb;
        if (size_needed > 0 && w > 0 && h > 0) {
            thumb.resize(size_needed);
            legends_capture_rgb(engine_, thumb.data(), thumb.size(), &size_needed, &w, &h);
        }
        if (save_manager_.saveToSlot(engine_, slot,
                                     thumb.empty() ? nullptr : thumb.data(), w, h)) {
            std::fprintf(stderr, "State saved to slot %d\n", slot);
        } else {
            std::fprintf(stderr, "Save failed (slot %d): %s\n", slot,
                         save_manager_.lastError().c_str());
        }
    });

    // Load state
    action_bus_.registerHandler(Action::LoadState, [this](int slot) {
        if (!engine_ || slot < 1 || slot > SaveManager::kMaxSlots) return;
        if (save_manager_.loadFromSlot(engine_, slot)) {
            std::fprintf(stderr, "State loaded from slot %d\n", slot);
        } else {
            std::fprintf(stderr, "Load failed (slot %d): %s\n", slot,
                         save_manager_.lastError().c_str());
        }
    });

    // Clipboard paste (via PAL abstraction)
    action_bus_.registerHandler(Action::ClipboardPaste, [this](int) {
        if (window_ && engine_) {
            std::string text = window_->getClipboardText();
            if (!text.empty()) {
                legends_text_input(engine_, text.c_str());
            }
        }
    });

    // Volume up
    action_bus_.registerHandler(Action::VolumeUp, [this](int) {
        volume_ = std::min(1.0f, volume_ + 0.1f);
        muted_ = false;
        if (audio_sink_) audio_sink_->setVolume(volume_);
    });

    // Volume down
    action_bus_.registerHandler(Action::VolumeDown, [this](int) {
        volume_ = std::max(0.0f, volume_ - 0.1f);
        muted_ = false;
        if (audio_sink_) audio_sink_->setVolume(volume_);
    });

    // Toggle mute
    action_bus_.registerHandler(Action::ToggleMute, [this](int) {
        if (muted_) {
            muted_ = false;
            volume_ = pre_mute_vol_;
        } else {
            muted_ = true;
            pre_mute_vol_ = volume_;
            volume_ = 0.0f;
        }
        if (audio_sink_) audio_sink_->setVolume(volume_);
    });

    // Release mouse capture
    action_bus_.registerHandler(Action::ReleaseMouseCapture, [this](int) {
        setMouseCaptured(false);
    });

    // Open mapper UI (REQ-MAPPER-001)
    action_bus_.registerHandler(Action::OpenMapper, [this](int) {
        if (mapper_ui_.isOpen()) {
            mapper_ui_.close();
        } else {
            mapper_ui_.open();
        }
    });

    // Open save browser (REQ-SAVE-003)
    action_bus_.registerHandler(Action::OpenSaveBrowser, [this](int param) {
        if (save_browser_.isOpen()) {
            save_browser_.close();
        } else if (param == 0) {
            save_browser_.openForSave();
        } else {
            save_browser_.openForLoad();
        }
    });

    // Open menu
    action_bus_.registerHandler(Action::OpenMenu, [this](int) {
        if (menu_system_.isOpen()) {
            menu_system_.close();
        } else {
            menu_system_.open();
        }
    });

    // ── Phase 2: Mounting ─────────────────────────────────────────────────

    action_bus_.registerHandler(Action::MountDrive, [](int param) {
        // param 0 = mount directory, param 1 = mount image
        // TODO: Open file dialog for path selection (requires SDL3 file dialog)
        (void)param;
        std::fprintf(stderr, "Mount drive: file dialog not yet implemented\n");
    });

    action_bus_.registerHandler(Action::UnmountDrive, [](int) {
        // TODO: Open drive letter selection dialog
        std::fprintf(stderr, "Unmount drive: drive selector not yet implemented\n");
    });

    // ── Phase 2: Video Capture ──────────────────────────────────────────────

    action_bus_.registerHandler(Action::ToggleVideoCapture, [this](int) {
        if (video_capture_.isRecording()) {
            video_capture_.stopCapture();
            std::fprintf(stderr, "Video capture stopped\n");
        } else {
            std::string dir = getCaptureDir();
            std::filesystem::create_directories(dir);
            std::string path = dir + "/" + generateCaptureFilename() + ".avi";
            if (video_capture_.startCapture(path, ctx_width_, ctx_height_, 30)) {
                std::fprintf(stderr, "Video capture started: %s\n", path.c_str());
            } else {
                std::fprintf(stderr, "Video capture failed to start\n");
            }
        }
    });
    action_bus_.registerHandler(Action::StartVideoCapture, [this](int) {
        if (!video_capture_.isRecording()) {
            action_bus_.dispatch(Action::ToggleVideoCapture);
        }
    });
    action_bus_.registerHandler(Action::StopVideoCapture, [this](int) {
        if (video_capture_.isRecording()) {
            video_capture_.stopCapture();
            std::fprintf(stderr, "Video capture stopped\n");
        }
    });

    // ── Phase 3: Enhanced Feature handlers ────────────────────────────────

    // Sprint 1: Toggle fullscreen
    action_bus_.registerHandler(Action::ToggleFullscreen, [this](int) {
        fullscreen_ = !fullscreen_;
        if (window_) {
            window_->setFullscreen(fullscreen_);
        }
        menu_system_.setFullscreen(fullscreen_);
    });

    // Sprint 2: Shader handlers
    action_bus_.registerHandler(Action::ToggleShaders, [this](int) {
        shader_renderer_.setShadersEnabled(!shader_renderer_.shadersEnabled());
    });
    action_bus_.registerHandler(Action::NextShader, [this](int) {
        shader_renderer_.nextPreset();
    });
    action_bus_.registerHandler(Action::PrevShader, [this](int) {
        shader_renderer_.prevPreset();
    });
    action_bus_.registerHandler(Action::LoadCustomShader, [](int) {
        std::fprintf(stderr, "Load custom shader: file dialog not yet implemented\n");
    });

    // Sprint 3: AI panel
    action_bus_.registerHandler(Action::ToggleAIPanel, [this](int) {
        if (ai_panel_.isOpen()) {
            ai_panel_.close();
        } else {
            ai_panel_.open();
        }
    });
    action_bus_.registerHandler(Action::AISubmitQuery, [this](int) {
        if (!ai_config_.enabled) return;
        if (ai_config_.privacy_mode) {
            ai_panel_.addResponse("Privacy mode is active. AI queries are disabled.");
            ai_panel_.setWaiting(false);
            return;
        }
        std::string api_key = ai_config_.resolveApiKey();
        if (api_key.empty()) {
            ai_panel_.addResponse("[Error] API key not found in environment variable: "
                                   + ai_config_.api_key_env);
            ai_panel_.setWaiting(false);
            return;
        }
        // Capture screen context and cursor/geometry via embed API
        std::string screen = captureScreenContext(engine_, ai_config_.max_context_chars);
        uint8_t cursor_x = 0, cursor_y = 0;
        int cursor_visible = 0;
        legends_get_cursor(engine_, &cursor_x, &cursor_y, &cursor_visible);
        legends_text_info_t text_info{};
        legends_capture_text(engine_, nullptr, 0, nullptr, &text_info);
        // REQ-SEC-018: Use formatScreenContext() for structured delimiters
        // that separate untrusted screen content from the system prompt.
        std::string formatted = formatScreenContext(
            screen, cursor_x, cursor_y, text_info.columns, text_info.rows);
        // Build request
        AIRequest req;
        req.endpoint = ai_config_.endpoint;
        req.api_key = api_key;
        req.model = ai_config_.model;
        req.system_prompt = "You are an AI assistant embedded in a DOS emulator. "
            "Help the user with their DOS programs and games.\n\n" + formatted;
        const auto& history = ai_panel_.history();
        if (!history.empty()) {
            req.user_message = history.back().text;
        }
        req.max_tokens = ai_config_.max_tokens;
        ai_http_client_.submitRequest(req, [](const AIResponse& resp) {
            // Response will be polled in processEvents
            (void)resp;
        });
    });

    // Sprint 4: MIDI device
    action_bus_.registerHandler(Action::SetMIDIDevice, [this](int param) {
        auto device = static_cast<MIDIDevice>(param);
        midi_config_.device = device;
        if (engine_) {
            legends_midi_set_device(engine_, MIDIConfig::deviceName(device));
        }
    });

    // Sprint 5: Printer + TTF
    action_bus_.registerHandler(Action::TogglePrinter, [this](int) {
        printer_manager_.setEnabled(!printer_manager_.isEnabled());
        if (engine_ && printer_manager_.isEnabled() && printer_manager_.isConfigured()) {
            legends_printer_set_output(engine_, printer_manager_.outputDirectory().c_str());
        }
    });
    action_bus_.registerHandler(Action::ToggleTTFMode, [this](int) {
        ttf_renderer_.setEnabled(!ttf_renderer_.isEnabled());
    });

    // Sprint 6: IPX + Glide
    action_bus_.registerHandler(Action::IPXConnect, [this](int) {
        if (engine_ && !ipx_config_.server.empty()) {
            legends_ipx_enable(engine_, 1);
            legends_ipx_connect(engine_, ipx_config_.server.c_str(), ipx_config_.port);
        }
    });
    action_bus_.registerHandler(Action::IPXDisconnect, [this](int) {
        if (engine_) {
            legends_ipx_disconnect(engine_);
        }
    });
    action_bus_.registerHandler(Action::ToggleGlide, [this](int) {
        glide_config_.enabled = !glide_config_.enabled;
        if (engine_) {
            legends_glide_enable(engine_, glide_config_.enabled ? 1 : 0);
            if (glide_config_.enabled) {
                legends_glide_set_resolution(engine_, glide_config_.width, glide_config_.height);
            }
        }
    });

    // Sprint 7: PC-98
    action_bus_.registerHandler(Action::SetMachinePC98, [this](int) {
        pc98_config_.enabled = !pc98_config_.enabled;
        if (engine_) {
            legends_set_machine_pc98(engine_, pc98_config_.enabled ? 1 : 0);
        }
    });

    // REQ-UX-005: Performance overlay
    action_bus_.registerHandler(Action::TogglePerfOverlay, [this](int) {
        perf_overlay_.toggle();
    });
}

void Application::updateWindowTitle() {
    if (!window_) return;
    std::string title = base_title_;
    if (paused_) title += " - PAUSED";
    window_->setTitle(title.c_str());
}

// ─────────────────────────────────────────────────────────────────────────────
// Mouse capture helpers
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

    // ── TTF text-mode override ──────────────────────────────────────────
    if (ttf_renderer_.isEnabled() && ttf_renderer_.isLoaded()) {
        size_t cell_count = 0;
        legends_text_info_t tinfo{};
        legends_capture_text(engine_, nullptr, 0, &cell_count, &tinfo);
        if (cell_count > 0 && tinfo.columns > 0 && tinfo.rows > 0) {
            std::vector<legends_text_cell_t> cells(cell_count);
            legends_capture_text(engine_, cells.data(), cells.size(),
                                 &cell_count, &tinfo);

            uint32_t pitch = static_cast<uint32_t>(fw) * 3;
            for (uint8_t row = 0; row < tinfo.rows; ++row) {
                for (uint8_t col = 0; col < tinfo.columns; ++col) {
                    size_t idx = row * tinfo.columns + col;
                    if (idx >= cell_count) break;

                    uint8_t ch   = cells[idx].character;
                    uint8_t attr = cells[idx].attribute;

                    static constexpr uint8_t kVGA16[16][3] = {
                        {0,0,0}, {0,0,170}, {0,170,0}, {0,170,170},
                        {170,0,0}, {170,0,170}, {170,85,0}, {170,170,170},
                        {85,85,85}, {85,85,255}, {85,255,85}, {85,255,255},
                        {255,85,85}, {255,85,255}, {255,255,85}, {255,255,255}
                    };

                    uint8_t fg_idx = attr & 0x0F;
                    uint8_t bg_idx = (attr >> 4) & 0x07;

                    int x = col * ttf_renderer_.cellWidth();
                    int y = row * ttf_renderer_.cellHeight();

                    ttf_renderer_.renderCell(
                        rgb_buffer_.data(), pitch, fw, fh,
                        x, y, ch,
                        kVGA16[fg_idx][0], kVGA16[fg_idx][1], kVGA16[fg_idx][2],
                        kVGA16[bg_idx][0], kVGA16[bg_idx][1], kVGA16[bg_idx][2]);
                }
            }
        }
    }

    // ── OpenGL path: render through shader pipeline ─────────────────────
    if (use_opengl_) {
        bool gl_ok = true;
        if (!shader_renderer_.isInitialized() ||
            fw != ctx_width_ || fh != ctx_height_) {
            shader_renderer_.destroy();
            if (!shader_renderer_.init(fw, fh)) {
                std::fprintf(stderr,
                    "Warning: ShaderRenderer init failed, falling back to software\n");
                use_opengl_ = false;
                gl_ok = false;
            } else {
                ctx_width_  = fw;
                ctx_height_ = fh;
            }
        }
        if (gl_ok) {
            shader_renderer_.render(rgb_buffer_.data(), fw, fh);
            context_->swapBuffers();
            return;
        }
    }

    // ── Software path with dimension debouncing (REQ-QA-006) ────────────
    if (fw != ctx_width_ || fh != ctx_height_) {
        if (fw == pending_width_ && fh == pending_height_) {
            ++dim_stable_count_;
        } else {
            pending_width_  = fw;
            pending_height_ = fh;
            dim_stable_count_ = 1;
        }

        if (dim_stable_count_ >= kDimStableFrames) {
            context_->destroy();
            auto res = context_->createSoftware(fw, fh, pal::PixelFormat::RGB888);
            if (pal::failed(res)) return;
            ctx_width_  = fw;
            ctx_height_ = fh;
            // Step 8: Update logical presentation for aspect ratio
            context_->setLogicalSize(fw, fh);
            dim_stable_count_ = 0;
        }
    } else {
        // Dimensions match — reset pending state
        dim_stable_count_ = 0;
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

    // Render persistent menu bar (hidden in fullscreen)
    if (menu_system_.isBarVisible()) {
        menu_system_.renderBar(static_cast<uint8_t*>(sctx.pixels),
                               static_cast<uint16_t>(sw),
                               static_cast<uint16_t>(sh),
                               sctx.pitch);
    }

    // Composite menu overlay if open
    if (menu_system_.isOpen()) {
        menu_system_.render(static_cast<uint8_t*>(sctx.pixels),
                            static_cast<uint16_t>(sw),
                            static_cast<uint16_t>(sh),
                            sctx.pitch);
    }

    // Composite mapper UI overlay if open
    if (mapper_ui_.isOpen()) {
        mapper_ui_.render(static_cast<uint8_t*>(sctx.pixels),
                          static_cast<uint16_t>(sw),
                          static_cast<uint16_t>(sh),
                          sctx.pitch);
    }

    // Composite save browser overlay if open
    if (save_browser_.isOpen()) {
        save_browser_.render(static_cast<uint8_t*>(sctx.pixels),
                             static_cast<uint16_t>(sw),
                             static_cast<uint16_t>(sh),
                             sctx.pitch);
    }

    // Composite AI panel overlay if open (mutually exclusive with menu)
    if (ai_panel_.isOpen() && !menu_system_.isOpen()) {
        ai_panel_.render(static_cast<uint8_t*>(sctx.pixels),
                         static_cast<uint16_t>(sw),
                         static_cast<uint16_t>(sh),
                         sctx.pitch);
    }

    // REQ-UX-005: Performance overlay
    if (perf_overlay_.isEnabled()) {
        perf_overlay_.render(static_cast<uint8_t*>(sctx.pixels),
                              static_cast<uint16_t>(sw),
                              static_cast<uint16_t>(sh),
                              sctx.pitch);
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

    // Mix MIDI audio if active
    if (midi_config_.device != MIDIDevice::None) {
        size_t midi_avail = 0;
        legends_capture_midi_audio(engine_, nullptr, 0, &midi_avail);
        if (midi_avail > 0) {
            std::vector<int16_t> midi_buf(midi_avail);
            size_t midi_actual = 0;
            legends_capture_midi_audio(engine_, midi_buf.data(), midi_buf.size(), &midi_actual);
            if (midi_actual > 0) {
                size_t mix_count = std::min(actual, midi_actual);
                AudioMixer::mixAdditive(
                    std::span<int16_t>{audio_buffer_.data(), mix_count},
                    std::span<const int16_t>{midi_buf.data(), mix_count});
            }
        }
    }

    // actual is int16_t element count; stereo frames = actual / 2
    uint32_t frames = static_cast<uint32_t>(actual) / 2;
    audio_sink_->pushSamples(audio_buffer_.data(), frames);
}

// ─────────────────────────────────────────────────────────────────────────────
// Shutdown
// ─────────────────────────────────────────────────────────────────────────────

void Application::shutdown() {
    // Phase 4: Log shutdown and flush
    if (file_logger_.isOpen()) {
        file_logger_.log(LogLevel::Info, "Application shutting down");
        file_logger_.flush();
    }
    globalCrashReporter().disable();

    shader_renderer_.destroy();

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

    file_logger_.close();
}

} // namespace legends
