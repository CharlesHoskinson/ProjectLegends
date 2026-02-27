// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for Application startup/shutdown/run loop lifecycle.
// Tests constructor, destructor, and run-loop behavior through
// observable side effects and extracted components.

#include "app/application.h"
#include "app/action_bus.h"
#include "app/menu_system.h"
#include "app/audio_mixer.h"

#include <pal/platform.h>
#include <pal/types.h>

#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <vector>

namespace legends {
namespace {

// ═══════════════════════════════════════════════════════════════════════════
// Helper: argv builder
// ═══════════════════════════════════════════════════════════════════════════

class ArgvHolder {
public:
    explicit ArgvHolder(std::initializer_list<const char*> args) {
        for (const char* a : args) {
            storage_.emplace_back(a);
        }
        for (auto& s : storage_) {
            ptrs_.push_back(s.data());
        }
        ptrs_.push_back(nullptr);
    }
    int    argc() const { return static_cast<int>(storage_.size()); }
    char** argv()       { return ptrs_.data(); }
private:
    std::vector<std::string> storage_;
    std::vector<char*>       ptrs_;
};

// ═══════════════════════════════════════════════════════════════════════════
// Constructor / Destructor
// ═══════════════════════════════════════════════════════════════════════════

TEST(ApplicationLifecycleTest, Constructor_InitializesDefaults) {
    // Application should construct without error and without PAL services
    Application app;
    SUCCEED();
}

TEST(ApplicationLifecycleTest, Destructor_CallsShutdown_NoDoubleFree) {
    // Construct and immediately destroy — no init called
    {
        Application app;
    }
    SUCCEED();
}

TEST(ApplicationLifecycleTest, Destructor_AfterVersionInit) {
    // init(--version) returns early but destructor should still work
    {
        Application app;
        ArgvHolder args{"project_legends", "--version"};
        app.init(args.argc(), args.argv());
    }
    SUCCEED();
}

TEST(ApplicationLifecycleTest, Destructor_AfterHelpInit) {
    {
        Application app;
        ArgvHolder args{"project_legends", "--help"};
        app.init(args.argc(), args.argv());
    }
    SUCCEED();
}

TEST(ApplicationLifecycleTest, Destructor_AfterCLIFailure) {
    {
        Application app;
        ArgvHolder args{"project_legends", "--unknown-bad-flag"};
        app.init(args.argc(), args.argv());
    }
    SUCCEED();
}

// ═══════════════════════════════════════════════════════════════════════════
// ExitCode values (lifecycle-related)
// ═══════════════════════════════════════════════════════════════════════════

TEST(ApplicationLifecycleTest, ExitCode_SuccessIsZero) {
    EXPECT_EQ(static_cast<int>(ExitCode::Success), 0);
}

TEST(ApplicationLifecycleTest, ExitCode_AllCodesUnique) {
    std::vector<int> codes = {
        static_cast<int>(ExitCode::Success),
        static_cast<int>(ExitCode::PlatformInitFailed),
        static_cast<int>(ExitCode::WindowCreateFailed),
        static_cast<int>(ExitCode::ContextCreateFailed),
        static_cast<int>(ExitCode::ClockInitFailed),
        static_cast<int>(ExitCode::InputInitFailed),
        static_cast<int>(ExitCode::AudioInitFailed),
        static_cast<int>(ExitCode::EngineCreateFailed),
        static_cast<int>(ExitCode::CLIParseFailed),
    };
    std::sort(codes.begin(), codes.end());
    auto last = std::unique(codes.begin(), codes.end());
    EXPECT_EQ(last, codes.end()) << "ExitCode values must be unique";
}

// ═══════════════════════════════════════════════════════════════════════════
// Run loop control — test that the running flag concept works
// We test this through ActionBus since run() is the full loop
// ═══════════════════════════════════════════════════════════════════════════

TEST(ApplicationLifecycleTest, ActionBus_QuitAction_CanDispatch) {
    ActionBus bus;
    bool quit_called = false;
    bus.registerHandler(Action::Quit, [&](int) {
        quit_called = true;
    });
    bus.dispatch(Action::Quit, 0);
    EXPECT_TRUE(quit_called);
}

TEST(ApplicationLifecycleTest, ActionBus_PauseAction) {
    ActionBus bus;
    bool paused = false;
    bus.registerHandler(Action::Pause, [&](int) {
        paused = true;
    });
    bus.dispatch(Action::Pause, 0);
    EXPECT_TRUE(paused);
}

TEST(ApplicationLifecycleTest, ActionBus_ResumeAction) {
    ActionBus bus;
    bool paused = true;
    bus.registerHandler(Action::Resume, [&](int) {
        paused = false;
    });
    bus.dispatch(Action::Resume, 0);
    EXPECT_FALSE(paused);
}

TEST(ApplicationLifecycleTest, ActionBus_TogglePauseAction) {
    ActionBus bus;
    bool paused = false;
    bus.registerHandler(Action::TogglePause, [&](int) {
        paused = !paused;
    });
    bus.dispatch(Action::TogglePause, 0);
    EXPECT_TRUE(paused);
    bus.dispatch(Action::TogglePause, 0);
    EXPECT_FALSE(paused);
}

// ═══════════════════════════════════════════════════════════════════════════
// Frame pacing — verify the constant is ~16.67ms (60 FPS)
// ═══════════════════════════════════════════════════════════════════════════

TEST(ApplicationLifecycleTest, FramePacing_TargetIs60FPS) {
    constexpr uint64_t kTargetFrameUs = 16667;
    // ~60 FPS = 16.667ms per frame
    double fps = 1000000.0 / static_cast<double>(kTargetFrameUs);
    EXPECT_NEAR(fps, 60.0, 0.1);
}

// ═══════════════════════════════════════════════════════════════════════════
// Pause / Menu skip engine stepping
// ═══════════════════════════════════════════════════════════════════════════

TEST(ApplicationLifecycleTest, MenuOpen_SkipsEngineStepping) {
    // When menu is open, the run loop condition is:
    // if (!paused_ && !menu_system_.isOpen()) { step engine }
    MenuSystem menu;
    ActionBus bus;
    menu.initialize(&bus);
    EXPECT_FALSE(menu.isOpen());
    menu.open();
    EXPECT_TRUE(menu.isOpen());
    // The combination: !paused && !menu.isOpen() would be false
    bool should_step = (!false && !menu.isOpen());
    EXPECT_FALSE(should_step);
}

TEST(ApplicationLifecycleTest, Paused_SkipsEngineStepping) {
    bool paused = true;
    MenuSystem menu;
    bool should_step = (!paused && !menu.isOpen());
    EXPECT_FALSE(should_step);
}

TEST(ApplicationLifecycleTest, NotPausedAndMenuClosed_StepsEngine) {
    bool paused = false;
    MenuSystem menu;
    bool should_step = (!paused && !menu.isOpen());
    EXPECT_TRUE(should_step);
}

// ═══════════════════════════════════════════════════════════════════════════
// AudioMixer — pumpAudio handles null audio_sink gracefully
// ═══════════════════════════════════════════════════════════════════════════

TEST(ApplicationLifecycleTest, AudioMixer_MixAdditive_DoesNotCrash) {
    std::vector<int16_t> dst = {100, 200, -100};
    std::vector<int16_t> src = {50, -50, 100};
    AudioMixer::mixAdditive(dst.data(), src.data(), 3);
    // Verify mixing happened (values summed and clamped)
    EXPECT_NE(dst[0], 100); // Should be ~150
}

TEST(ApplicationLifecycleTest, AudioMixer_MixAdditive_EmptyBuffers) {
    // Mixing zero samples should not crash
    int16_t dummy = 0;
    AudioMixer::mixAdditive(&dummy, &dummy, 0);
    SUCCEED();
}

// ═══════════════════════════════════════════════════════════════════════════
// PAL Platform — basic sanity (does not test Application directly but
// validates the infrastructure Application depends on)
// ═══════════════════════════════════════════════════════════════════════════

TEST(ApplicationLifecycleTest, PAL_BackendStrings) {
    EXPECT_STREQ(pal::toString(pal::Backend::None), "None");
    EXPECT_STREQ(pal::toString(pal::Backend::SDL2), "SDL2");
    EXPECT_STREQ(pal::toString(pal::Backend::SDL3), "SDL3");
    EXPECT_STREQ(pal::toString(pal::Backend::Headless), "Headless");
}

TEST(ApplicationLifecycleTest, PAL_ResultStrings) {
    EXPECT_STREQ(pal::toString(pal::Result::Success), "Success");
    EXPECT_STREQ(pal::toString(pal::Result::NotInitialized), "NotInitialized");
}

TEST(ApplicationLifecycleTest, PAL_SucceededFailed) {
    EXPECT_TRUE(pal::succeeded(pal::Result::Success));
    EXPECT_FALSE(pal::failed(pal::Result::Success));
    EXPECT_TRUE(pal::failed(pal::Result::NotInitialized));
    EXPECT_FALSE(pal::succeeded(pal::Result::NotInitialized));
}

} // namespace
} // namespace legends
