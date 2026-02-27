// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for SaveBrowser — visual save slot browser with 3x3 grid.
// REQ-SAVE-003: Save slot visual browser

#include <gtest/gtest.h>
#include <legends/gsl.hpp>
#include "app/save_browser.h"
#include "app/action_bus.h"
#include "app/save_manager.h"

#include <cstdint>
#include <vector>

namespace legends {
namespace {

class SaveBrowserTest : public ::testing::Test {
protected:
    void SetUp() override {
        browser_.initialize(&bus_, &save_mgr_);
    }

    ActionBus   bus_;
    SaveManager save_mgr_;
    SaveBrowser browser_;
};

// ═══════════════════════════════════════════════════════════════════════════
// Open / Close State
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(SaveBrowserTest, InitiallyNotOpen) {
    SaveBrowser fresh;
    EXPECT_FALSE(fresh.isOpen());
}

TEST_F(SaveBrowserTest, OpenInSaveMode) {
    browser_.openForSave();
    EXPECT_TRUE(browser_.isOpen());
    EXPECT_EQ(browser_.mode(), SaveBrowser::Mode::Save);
}

TEST_F(SaveBrowserTest, OpenInLoadMode) {
    browser_.openForLoad();
    EXPECT_TRUE(browser_.isOpen());
    EXPECT_EQ(browser_.mode(), SaveBrowser::Mode::Load);
}

TEST_F(SaveBrowserTest, CloseAfterOpen) {
    browser_.openForSave();
    browser_.close();
    EXPECT_FALSE(browser_.isOpen());
}

// ═══════════════════════════════════════════════════════════════════════════
// Grid Layout & Navigation
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(SaveBrowserTest, GridLayout_3x3) {
    EXPECT_EQ(SaveBrowser::kRows, 3);
    EXPECT_EQ(SaveBrowser::kCols, 3);
    EXPECT_EQ(SaveBrowser::kTotalSlots, 9);
}

TEST_F(SaveBrowserTest, SelectedSlot_DefaultIsFirst) {
    browser_.openForSave();
    EXPECT_EQ(browser_.selectedSlot(), 1);
}

TEST_F(SaveBrowserTest, NavigateRight) {
    browser_.openForSave();
    browser_.handleKey(0x4F, true);  // Right arrow
    EXPECT_EQ(browser_.selectedSlot(), 2);
}

TEST_F(SaveBrowserTest, NavigateDown) {
    browser_.openForSave();
    browser_.handleKey(0x51, true);  // Down arrow
    EXPECT_EQ(browser_.selectedSlot(), 4);  // Row 2, Col 1
}

TEST_F(SaveBrowserTest, NavigateWrap_Right) {
    browser_.openForSave();
    // Navigate right past end of row
    browser_.handleKey(0x4F, true);  // → slot 2
    browser_.handleKey(0x4F, true);  // → slot 3
    browser_.handleKey(0x4F, true);  // → wraps to slot 1
    EXPECT_EQ(browser_.selectedSlot(), 1);
}

TEST_F(SaveBrowserTest, NavigateWrap_Down) {
    browser_.openForSave();
    // Navigate down past end of column
    browser_.handleKey(0x51, true);  // → slot 4
    browser_.handleKey(0x51, true);  // → slot 7
    browser_.handleKey(0x51, true);  // → wraps to slot 1
    EXPECT_EQ(browser_.selectedSlot(), 1);
}

// ═══════════════════════════════════════════════════════════════════════════
// Action Dispatch
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(SaveBrowserTest, EnterOnSlot_SaveMode_DispatchesSave) {
    int dispatched_slot = -1;
    bus_.registerHandler(Action::SaveState, [&](int p) { dispatched_slot = p; });

    browser_.openForSave();
    browser_.handleKey(0x28, true);  // Enter
    EXPECT_EQ(dispatched_slot, 1);
    EXPECT_FALSE(browser_.isOpen());  // Closes after dispatch
}

TEST_F(SaveBrowserTest, EnterOnSlot_LoadMode_DispatchesLoad) {
    int dispatched_slot = -1;
    bus_.registerHandler(Action::LoadState, [&](int p) { dispatched_slot = p; });

    browser_.openForLoad();
    browser_.handleKey(0x28, true);  // Enter
    EXPECT_EQ(dispatched_slot, 1);
    EXPECT_FALSE(browser_.isOpen());
}

TEST_F(SaveBrowserTest, EscapeCloses) {
    browser_.openForSave();
    browser_.handleKey(0x29, true);  // Escape
    EXPECT_FALSE(browser_.isOpen());
}

// ═══════════════════════════════════════════════════════════════════════════
// Key Handling
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(SaveBrowserTest, HandleKey_ReturnsFalseWhenClosed) {
    EXPECT_FALSE(browser_.handleKey(0x28, true));
}

TEST_F(SaveBrowserTest, HandleKey_ReturnsTrueWhenOpen) {
    browser_.openForSave();
    EXPECT_TRUE(browser_.handleKey(0x29, true));  // Escape consumed
}

TEST_F(SaveBrowserTest, HandleKey_KeyUp_Ignored) {
    browser_.openForSave();
    int initial_slot = browser_.selectedSlot();
    // Key-up (down=false) for Right arrow — should be ignored
    EXPECT_FALSE(browser_.handleKey(0x4F, false));
    EXPECT_EQ(browser_.selectedSlot(), initial_slot);
}

// ═══════════════════════════════════════════════════════════════════════════
// Rendering
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(SaveBrowserTest, RenderDoesNotCrashWhenClosed) {
    std::vector<uint8_t> buf(640 * 480 * 3, 0);
    // Should be no-op, no crash
    browser_.render(buf.data(), 640, 480);
}

TEST_F(SaveBrowserTest, RenderShowsGrid_WhenOpen) {
    browser_.openForSave();
    std::vector<uint8_t> buf(640 * 480 * 3, 0);
    browser_.render(buf.data(), 640, 480);

    // At least some pixels should be non-zero (grid rendered)
    bool any_nonzero = false;
    for (auto b : buf) {
        if (b != 0) { any_nonzero = true; break; }
    }
    EXPECT_TRUE(any_nonzero) << "Open save browser should modify the buffer";
}

// ═══════════════════════════════════════════════════════════════════════════
// gsl-lite Contract Violations
// ═══════════════════════════════════════════════════════════════════════════

TEST(SaveBrowserContractTest, NullBus_InitializeThrowsFailFast) {
    SaveBrowser browser;
    SaveManager mgr;
    EXPECT_THROW(browser.initialize(nullptr, &mgr), legends::gsl::fail_fast);
}

TEST(SaveBrowserContractTest, NullMgr_InitializeThrowsFailFast) {
    SaveBrowser browser;
    ActionBus bus;
    EXPECT_THROW(browser.initialize(&bus, nullptr), legends::gsl::fail_fast);
}

TEST(SaveBrowserContractTest, NullRGB_RenderThrowsFailFast) {
    SaveBrowser browser;
    ActionBus bus;
    SaveManager mgr;
    browser.initialize(&bus, &mgr);
    browser.openForSave();
    EXPECT_THROW(browser.render(nullptr, 640, 480), legends::gsl::fail_fast);
}

TEST(SaveBrowserContractTest, SelectedSlot_WhenClosed_ThrowsFailFast) {
    SaveBrowser browser;
    ActionBus bus;
    SaveManager mgr;
    browser.initialize(&bus, &mgr);
    // Browser is closed, selectedSlot should throw
    EXPECT_THROW(browser.selectedSlot(), legends::gsl::fail_fast);
}

TEST(SaveBrowserContractTest, Mode_WhenClosed_ThrowsFailFast) {
    SaveBrowser browser;
    ActionBus bus;
    SaveManager mgr;
    browser.initialize(&bus, &mgr);
    EXPECT_THROW(browser.mode(), legends::gsl::fail_fast);
}

} // namespace
} // namespace legends
