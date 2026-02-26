// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for clipboard paste via ActionBus.

#include <gtest/gtest.h>
#include "app/action_bus.h"

namespace legends {
namespace {

TEST(ClipboardPasteTest, ClipboardPasteActionDispatches) {
    ActionBus bus;
    int called = 0;
    bus.registerHandler(Action::ClipboardPaste, [&](int) { ++called; });
    bus.dispatch(Action::ClipboardPaste);
    EXPECT_EQ(called, 1);
}

TEST(ClipboardPasteTest, ClipboardPasteIgnoresParam) {
    ActionBus bus;
    int received = -1;
    bus.registerHandler(Action::ClipboardPaste, [&](int p) { received = p; });
    bus.dispatch(Action::ClipboardPaste, 42);
    EXPECT_EQ(received, 42); // param is passed through even if unused
}

TEST(ClipboardPasteTest, MultipleHandlersAllCalled) {
    ActionBus bus;
    int count = 0;
    bus.registerHandler(Action::ClipboardPaste, [&](int) { ++count; });
    bus.registerHandler(Action::ClipboardPaste, [&](int) { ++count; });
    bus.dispatch(Action::ClipboardPaste);
    EXPECT_EQ(count, 2);
}

TEST(ClipboardPasteTest, ClipboardPasteIsDistinctFromOtherActions) {
    ActionBus bus;
    int paste_count = 0, quit_count = 0;
    bus.registerHandler(Action::ClipboardPaste, [&](int) { ++paste_count; });
    bus.registerHandler(Action::Quit, [&](int) { ++quit_count; });
    bus.dispatch(Action::ClipboardPaste);
    EXPECT_EQ(paste_count, 1);
    EXPECT_EQ(quit_count, 0);
}

// ═══════════════════════════════════════════════════════════════════════════
// Phase 2 QA: edge cases
// ═══════════════════════════════════════════════════════════════════════════

TEST(ClipboardPasteTest, DispatchWithNoHandlersDoesNotCrash) {
    ActionBus bus;
    // No handlers registered — should be a no-op
    EXPECT_NO_THROW(bus.dispatch(Action::ClipboardPaste));
}

TEST(ClipboardPasteTest, ReRegisterHandlerAfterClearHandlersWorks) {
    ActionBus bus;
    int count = 0;
    bus.registerHandler(Action::ClipboardPaste, [&](int) { ++count; });
    bus.clearHandlers(Action::ClipboardPaste);
    bus.dispatch(Action::ClipboardPaste);
    EXPECT_EQ(count, 0);

    // Re-register
    bus.registerHandler(Action::ClipboardPaste, [&](int) { ++count; });
    bus.dispatch(Action::ClipboardPaste);
    EXPECT_EQ(count, 1);
}

} // namespace
} // namespace legends
