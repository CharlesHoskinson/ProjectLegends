// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for MenuSystem bar mode — persistent menu bar with dropdowns.
// REQ-MENU-001: Enhanced overlay menu bar

#include <gtest/gtest.h>
#include "app/menu_system.h"
#include "app/action_bus.h"

#include <cstdint>
#include <vector>

namespace legends {
namespace {

class MenuBarTest : public ::testing::Test {
protected:
    void SetUp() override {
        menu_.initialize(&bus_);
    }

    ActionBus  bus_;
    MenuSystem menu_;
};

// ═══════════════════════════════════════════════════════════════════════════
// Bar Visibility
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(MenuBarTest, BarMode_VisibleInWindowed) {
    // Menu bar should be visible by default (windowed mode)
    EXPECT_TRUE(menu_.isBarVisible());
}

TEST_F(MenuBarTest, BarMode_HiddenInFullscreen) {
    menu_.setFullscreen(true);
    EXPECT_FALSE(menu_.isBarVisible());
}

TEST_F(MenuBarTest, BarMode_VisibleAfterExitFullscreen) {
    menu_.setFullscreen(true);
    menu_.setFullscreen(false);
    EXPECT_TRUE(menu_.isBarVisible());
}

// ═══════════════════════════════════════════════════════════════════════════
// Dropdown Behavior
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(MenuBarTest, BarClick_OpensDropdown) {
    // Click on the bar area (y < kMenuBarH, x within first menu title)
    menu_.handleBarClick(10, 5);
    EXPECT_TRUE(menu_.isDropdownOpen());
}

TEST_F(MenuBarTest, BarClick_SwitchesMenu) {
    // Click first menu
    menu_.handleBarClick(10, 5);
    int first = menu_.selectedMenuIndex();

    // Click second menu (approx x = 8 chars * 8px = 64)
    menu_.handleBarClick(80, 5);
    EXPECT_NE(menu_.selectedMenuIndex(), first);
}

TEST_F(MenuBarTest, DropdownClick_ActivatesItem) {
    int dispatched = 0;
    bus_.registerHandler(Action::TogglePause, [&](int) { dispatched++; });

    // Open menu and click first non-separator item (TogglePause in Main menu)
    menu_.handleBarClick(10, 5);
    // Simulate clicking on the first item in the dropdown
    // The dropdown starts at y = kMenuBarH (20), first item at y ~20
    menu_.handleBarClick(10, 22);
    EXPECT_GT(dispatched, 0);
}

TEST_F(MenuBarTest, ClickOutsideDropdown_ClosesIt) {
    menu_.handleBarClick(10, 5);
    EXPECT_TRUE(menu_.isDropdownOpen());

    // Click far below the dropdown
    menu_.handleBarClick(300, 400);
    EXPECT_FALSE(menu_.isDropdownOpen());
}

// ═══════════════════════════════════════════════════════════════════════════
// Bar Rendering
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(MenuBarTest, BarRender_DrawsMenuTitles) {
    std::vector<uint8_t> buf(640 * 480 * 3, 0);
    menu_.renderBar(buf.data(), 640, 480);

    // Check that the menu bar area (top 20 rows) has been modified
    bool bar_modified = false;
    for (int y = 0; y < 20 && !bar_modified; ++y) {
        for (int x = 0; x < 640; ++x) {
            size_t idx = static_cast<size_t>(y) * 640 * 3 + static_cast<size_t>(x) * 3;
            if (buf[idx] != 0 || buf[idx + 1] != 0 || buf[idx + 2] != 0) {
                bar_modified = true;
                break;
            }
        }
    }
    EXPECT_TRUE(bar_modified) << "Menu bar should draw menu titles";
}

TEST_F(MenuBarTest, OverlayStillWorksWithF12) {
    // F12 should still open the full overlay mode
    menu_.open();
    EXPECT_TRUE(menu_.isOpen());
    menu_.close();
    EXPECT_FALSE(menu_.isOpen());
}

TEST_F(MenuBarTest, BarAndOverlayAreDifferentModes) {
    // The bar can be visible while the full overlay is closed
    EXPECT_TRUE(menu_.isBarVisible());
    EXPECT_FALSE(menu_.isOpen());

    // Opening full overlay mode is separate
    menu_.open();
    EXPECT_TRUE(menu_.isOpen());
    EXPECT_TRUE(menu_.isBarVisible());
}

TEST_F(MenuBarTest, RenderBar_WithPitch) {
    // Using a wider pitch should not crash
    uint32_t pitch = 640 * 3 + 64;  // Extra padding
    std::vector<uint8_t> buf(pitch * 480, 0);
    menu_.renderBar(buf.data(), 640, 480, pitch);
    // No crash = pass
}

TEST_F(MenuBarTest, RapidOpenClose_NoStateCorruption) {
    for (int i = 0; i < 100; ++i) {
        menu_.handleBarClick(10, 5);  // Open dropdown
        menu_.handleBarClick(300, 400);  // Close by clicking outside
    }
    // Should still be in consistent state
    EXPECT_FALSE(menu_.isDropdownOpen());
}

TEST_F(MenuBarTest, ZeroWidthBuffer_NoOverflow) {
    // Rendering to a zero-width buffer should be safe
    std::vector<uint8_t> buf(1, 0);
    menu_.renderBar(buf.data(), 0, 0);
    // No crash = pass
}

} // namespace
} // namespace legends
