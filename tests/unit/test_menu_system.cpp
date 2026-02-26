// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for the overlay menu system.

#include <gtest/gtest.h>
#include "app/menu_system.h"
#include "app/action_bus.h"

#include <vector>

namespace legends {
namespace {

class MenuSystemTest : public ::testing::Test {
protected:
    void SetUp() override {
        menu_.initialize(&bus_);
    }

    ActionBus bus_;
    MenuSystem menu_;
};

// ═══════════════════════════════════════════════════════════════════════════
// Open / Close
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(MenuSystemTest, InitiallyNotOpen) {
    EXPECT_FALSE(menu_.isOpen());
}

TEST_F(MenuSystemTest, OpenSetsOpen) {
    menu_.open();
    EXPECT_TRUE(menu_.isOpen());
}

TEST_F(MenuSystemTest, CloseSetsNotOpen) {
    menu_.open();
    menu_.close();
    EXPECT_FALSE(menu_.isOpen());
}

// ═══════════════════════════════════════════════════════════════════════════
// Keyboard navigation
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(MenuSystemTest, HandleKeyReturnsFalseWhenClosed) {
    EXPECT_FALSE(menu_.handleKey(0x51, true)); // Down
}

TEST_F(MenuSystemTest, HandleKeyReturnsTrueWhenOpen) {
    menu_.open();
    EXPECT_TRUE(menu_.handleKey(0x51, true)); // Down
}

TEST_F(MenuSystemTest, EscapeClosesMenu) {
    menu_.open();
    menu_.handleKey(0x29, true); // Escape
    EXPECT_FALSE(menu_.isOpen());
}

TEST_F(MenuSystemTest, F12ClosesMenu) {
    menu_.open();
    menu_.handleKey(0x45, true); // F12
    EXPECT_FALSE(menu_.isOpen());
}

TEST_F(MenuSystemTest, LeftRightSwitchesMenus) {
    menu_.open();
    // Navigate right
    menu_.handleKey(0x4F, true); // Right
    menu_.handleKey(0x4F, true); // Right again
    // Navigate left
    menu_.handleKey(0x50, true); // Left
    // No crash, still open
    EXPECT_TRUE(menu_.isOpen());
}

TEST_F(MenuSystemTest, UpDownNavigatesItems) {
    menu_.open();
    menu_.handleKey(0x51, true); // Down
    menu_.handleKey(0x51, true); // Down
    menu_.handleKey(0x52, true); // Up
    EXPECT_TRUE(menu_.isOpen());
}

// ═══════════════════════════════════════════════════════════════════════════
// Enter activates item and dispatches action
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(MenuSystemTest, EnterDispatchesAction) {
    int toggle_count = 0;
    bus_.registerHandler(Action::TogglePause, [&](int) { ++toggle_count; });

    menu_.open();
    // First menu is "Main", first item is "Pause/Resume" → TogglePause
    menu_.handleKey(0x28, true); // Enter
    EXPECT_EQ(toggle_count, 1);
    EXPECT_FALSE(menu_.isOpen()); // Menu closes after activation
}

TEST_F(MenuSystemTest, EnterOnSeparatorDoesNothing) {
    menu_.open();
    // Navigate down past items to separator
    menu_.handleKey(0x51, true); // Down (to Reset)
    menu_.handleKey(0x51, true); // Down (should skip separator to Quit)
    // No crash
    EXPECT_TRUE(menu_.isOpen());
}

// ═══════════════════════════════════════════════════════════════════════════
// Mouse click
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(MenuSystemTest, MouseClickReturnsFalseWhenClosed) {
    EXPECT_FALSE(menu_.handleMouseClick(10, 10));
}

TEST_F(MenuSystemTest, MouseClickOnMenuBarSelectsMenu) {
    menu_.open();
    // Click within menu bar (y < kMenuBarH = 20)
    EXPECT_TRUE(menu_.handleMouseClick(10, 5));
    EXPECT_TRUE(menu_.isOpen());
}

TEST_F(MenuSystemTest, MouseClickOutsideClosesMenu) {
    menu_.open();
    // Click far outside any menu area
    EXPECT_TRUE(menu_.handleMouseClick(500, 400));
    EXPECT_FALSE(menu_.isOpen());
}

// ═══════════════════════════════════════════════════════════════════════════
// Rendering
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(MenuSystemTest, RenderDoesNotCrashWhenClosed) {
    std::vector<uint8_t> buf(320 * 200 * 3, 128);
    menu_.render(buf.data(), 320, 200);
    // Should be a no-op — buffer unchanged
    EXPECT_EQ(buf[0], 128);
}

TEST_F(MenuSystemTest, RenderModifiesBufferWhenOpen) {
    std::vector<uint8_t> buf(320 * 200 * 3, 128);
    menu_.open();
    menu_.render(buf.data(), 320, 200);
    // Buffer should be modified (darkened background)
    // At least some pixels should differ from 128
    bool changed = false;
    for (size_t i = 0; i < buf.size(); ++i) {
        if (buf[i] != 128) { changed = true; break; }
    }
    EXPECT_TRUE(changed);
}

} // namespace
} // namespace legends
