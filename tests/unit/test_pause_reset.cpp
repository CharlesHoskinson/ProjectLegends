// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for Pause/Resume and Machine Reset via ActionBus.

#include <gtest/gtest.h>
#include "app/action_bus.h"

namespace legends {
namespace {

// ═══════════════════════════════════════════════════════════════════════════
// Pause / Resume / Toggle
// ═══════════════════════════════════════════════════════════════════════════

TEST(PauseResetTest, TogglePauseFlipsState) {
    ActionBus bus;
    bool paused = false;
    bus.registerHandler(Action::TogglePause, [&](int) { paused = !paused; });

    bus.dispatch(Action::TogglePause);
    EXPECT_TRUE(paused);

    bus.dispatch(Action::TogglePause);
    EXPECT_FALSE(paused);
}

TEST(PauseResetTest, PauseSetsPausedTrue) {
    ActionBus bus;
    bool paused = false;
    bus.registerHandler(Action::Pause, [&](int) { paused = true; });
    bus.dispatch(Action::Pause);
    EXPECT_TRUE(paused);
}

TEST(PauseResetTest, ResumeSetsPausedFalse) {
    ActionBus bus;
    bool paused = true;
    bus.registerHandler(Action::Resume, [&](int) { paused = false; });
    bus.dispatch(Action::Resume);
    EXPECT_FALSE(paused);
}

// ═══════════════════════════════════════════════════════════════════════════
// Reset
// ═══════════════════════════════════════════════════════════════════════════

TEST(PauseResetTest, ResetDispatchesAction) {
    ActionBus bus;
    int reset_count = 0;
    bus.registerHandler(Action::Reset, [&](int) { ++reset_count; });
    bus.dispatch(Action::Reset);
    EXPECT_EQ(reset_count, 1);
}

TEST(PauseResetTest, ResetClearsPause) {
    ActionBus bus;
    bool paused = true;
    bus.registerHandler(Action::Reset, [&](int) { paused = false; });
    bus.dispatch(Action::Reset);
    EXPECT_FALSE(paused);
}

// ═══════════════════════════════════════════════════════════════════════════
// Interaction between pause and reset
// ═══════════════════════════════════════════════════════════════════════════

TEST(PauseResetTest, ResetWhilePausedResumes) {
    ActionBus bus;
    bool paused = false;
    bus.registerHandler(Action::TogglePause, [&](int) { paused = !paused; });
    bus.registerHandler(Action::Reset, [&](int) { paused = false; });

    bus.dispatch(Action::TogglePause);
    EXPECT_TRUE(paused);

    bus.dispatch(Action::Reset);
    EXPECT_FALSE(paused);
}

TEST(PauseResetTest, MultipleToggleCycles) {
    ActionBus bus;
    int toggle_count = 0;
    bus.registerHandler(Action::TogglePause, [&](int) { ++toggle_count; });

    for (int i = 0; i < 10; ++i) {
        bus.dispatch(Action::TogglePause);
    }
    EXPECT_EQ(toggle_count, 10);
}

} // namespace
} // namespace legends
