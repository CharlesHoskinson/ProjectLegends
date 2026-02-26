// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for ActionBus centralized dispatch.

#include <gtest/gtest.h>
#include "app/action_bus.h"

namespace legends {
namespace {

// ═══════════════════════════════════════════════════════════════════════════
// Basic dispatch
// ═══════════════════════════════════════════════════════════════════════════

TEST(ActionBusTest, DispatchCallsRegisteredHandler) {
    ActionBus bus;
    int called = 0;
    bus.registerHandler(Action::Quit, [&](int) { ++called; });
    bus.dispatch(Action::Quit);
    EXPECT_EQ(called, 1);
}

TEST(ActionBusTest, DispatchPassesParam) {
    ActionBus bus;
    int received = -1;
    bus.registerHandler(Action::SaveState, [&](int param) { received = param; });
    bus.dispatch(Action::SaveState, 5);
    EXPECT_EQ(received, 5);
}

TEST(ActionBusTest, DispatchWithNoHandlerDoesNotCrash) {
    ActionBus bus;
    EXPECT_NO_THROW(bus.dispatch(Action::Screenshot));
}

TEST(ActionBusTest, DispatchCountIncrements) {
    ActionBus bus;
    EXPECT_EQ(bus.dispatchCount(), 0u);
    bus.dispatch(Action::Quit);
    bus.dispatch(Action::Pause);
    EXPECT_EQ(bus.dispatchCount(), 2u);
}

// ═══════════════════════════════════════════════════════════════════════════
// Multiple handlers
// ═══════════════════════════════════════════════════════════════════════════

TEST(ActionBusTest, MultipleHandlersForSameAction) {
    ActionBus bus;
    int count_a = 0, count_b = 0;
    bus.registerHandler(Action::TogglePause, [&](int) { ++count_a; });
    bus.registerHandler(Action::TogglePause, [&](int) { ++count_b; });
    bus.dispatch(Action::TogglePause);
    EXPECT_EQ(count_a, 1);
    EXPECT_EQ(count_b, 1);
}

TEST(ActionBusTest, HandlerCountReflectsRegistrations) {
    ActionBus bus;
    EXPECT_EQ(bus.handlerCount(Action::Reset), 0u);
    bus.registerHandler(Action::Reset, [](int) {});
    EXPECT_EQ(bus.handlerCount(Action::Reset), 1u);
    bus.registerHandler(Action::Reset, [](int) {});
    EXPECT_EQ(bus.handlerCount(Action::Reset), 2u);
}

// ═══════════════════════════════════════════════════════════════════════════
// Clear handlers
// ═══════════════════════════════════════════════════════════════════════════

TEST(ActionBusTest, ClearHandlersRemovesSpecificAction) {
    ActionBus bus;
    int called = 0;
    bus.registerHandler(Action::Screenshot, [&](int) { ++called; });
    bus.registerHandler(Action::Quit, [&](int) { ++called; });
    bus.clearHandlers(Action::Screenshot);
    bus.dispatch(Action::Screenshot);
    bus.dispatch(Action::Quit);
    EXPECT_EQ(called, 1); // only Quit handler called
}

TEST(ActionBusTest, ClearAllRemovesEverything) {
    ActionBus bus;
    int called = 0;
    bus.registerHandler(Action::Quit, [&](int) { ++called; });
    bus.registerHandler(Action::Reset, [&](int) { ++called; });
    bus.clearAll();
    bus.dispatch(Action::Quit);
    bus.dispatch(Action::Reset);
    EXPECT_EQ(called, 0);
}

// ═══════════════════════════════════════════════════════════════════════════
// Different actions are independent
// ═══════════════════════════════════════════════════════════════════════════

TEST(ActionBusTest, DifferentActionsAreIndependent) {
    ActionBus bus;
    int quit_count = 0, pause_count = 0;
    bus.registerHandler(Action::Quit, [&](int) { ++quit_count; });
    bus.registerHandler(Action::TogglePause, [&](int) { ++pause_count; });
    bus.dispatch(Action::Quit);
    EXPECT_EQ(quit_count, 1);
    EXPECT_EQ(pause_count, 0);
}

TEST(ActionBusTest, AllActionEnumValuesAreDistinct) {
    // Verify all enum values are unique by registering each
    ActionBus bus;
    std::vector<Action> actions = {
        Action::Quit, Action::Pause, Action::Resume, Action::TogglePause,
        Action::Reset, Action::SaveState, Action::LoadState, Action::Screenshot,
        Action::OpenMapper, Action::ClipboardPaste, Action::VolumeUp,
        Action::VolumeDown, Action::ToggleMute, Action::ReleaseMouseCapture,
        Action::OpenMenu,
    };
    for (auto a : actions) {
        bus.registerHandler(a, [](int) {});
    }
    // Each should have exactly 1 handler
    for (auto a : actions) {
        EXPECT_EQ(bus.handlerCount(a), 1u);
    }
}

TEST(ActionBusTest, DispatchCountIncrementsEvenWithNoHandler) {
    ActionBus bus;
    bus.dispatch(Action::OpenMenu);
    bus.dispatch(Action::OpenMenu);
    EXPECT_EQ(bus.dispatchCount(), 2u);
}

} // namespace
} // namespace legends
