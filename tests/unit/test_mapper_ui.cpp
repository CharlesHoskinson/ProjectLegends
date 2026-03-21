// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for MapperUI — interactive key mapper visual overlay.
// REQ-MAPPER-001: Key mapper visual UI

#include <gtest/gtest.h>
#include <legends/gsl.hpp>
#include "app/mapper_ui.h"
#include "app/action_bus.h"
#include "app/input_mapper.h"

#include <cstdint>
#include <vector>

namespace legends {
namespace {

class MapperUITest : public ::testing::Test {
protected:
    void SetUp() override {
        mapper_ui_.initialize(&bus_, &mapper_);
    }

    ActionBus bus_;
    InputMapper mapper_;
    MapperUI mapper_ui_;
};

// ═══════════════════════════════════════════════════════════════════════════
// Open / Close State
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(MapperUITest, InitiallyNotOpen) {
    MapperUI fresh;
    EXPECT_FALSE(fresh.isOpen());
}

TEST_F(MapperUITest, OpenSetsOpen) {
    mapper_ui_.open();
    EXPECT_TRUE(mapper_ui_.isOpen());
}

TEST_F(MapperUITest, CloseAfterOpen) {
    mapper_ui_.open();
    mapper_ui_.close();
    EXPECT_FALSE(mapper_ui_.isOpen());
}

// ═══════════════════════════════════════════════════════════════════════════
// State Machine
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(MapperUITest, StateMachine_InitiallyIdle) {
    mapper_ui_.open();
    EXPECT_EQ(mapper_ui_.state(), MapperUI::State::Idle);
}

TEST_F(MapperUITest, StateMachine_CaptureAndAssign) {
    mapper_ui_.open();
    mapper_ui_.startCapture();
    EXPECT_EQ(mapper_ui_.state(), MapperUI::State::Capturing);

    // Simulate a key press during capture
    mapper_ui_.handleCapturedKey(0x05);  // B key scancode
    EXPECT_EQ(mapper_ui_.state(), MapperUI::State::Idle);
}

TEST_F(MapperUITest, StateMachine_CancelCapture) {
    mapper_ui_.open();
    mapper_ui_.startCapture();
    mapper_ui_.cancelCapture();
    EXPECT_EQ(mapper_ui_.state(), MapperUI::State::Idle);
}

// ═══════════════════════════════════════════════════════════════════════════
// Key Handling
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(MapperUITest, HandleKey_ReturnsFalseWhenClosed) {
    EXPECT_FALSE(mapper_ui_.handleKey(0x01, true));  // Escape
}

TEST_F(MapperUITest, HandleKey_EscapeClosesUI) {
    mapper_ui_.open();
    mapper_ui_.handleKey(0x29, true);  // Escape scancode
    EXPECT_FALSE(mapper_ui_.isOpen());
}

TEST_F(MapperUITest, HandleKey_NavigateList) {
    mapper_ui_.open();
    int initial = mapper_ui_.selectedIndex();
    mapper_ui_.handleKey(0x51, true);  // Down arrow
    EXPECT_EQ(mapper_ui_.selectedIndex(), initial + 1);
}

// ═══════════════════════════════════════════════════════════════════════════
// Rendering
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(MapperUITest, RenderDoesNotCrashWhenClosed) {
    std::vector<uint8_t> buf(640 * 480 * 3, 0);
    // Should be no-op, no crash
    mapper_ui_.render(buf.data(), 640, 480);
}

TEST_F(MapperUITest, RenderModifiesBufferWhenOpen) {
    mapper_ui_.open();
    std::vector<uint8_t> buf(640 * 480 * 3, 0);
    mapper_ui_.render(buf.data(), 640, 480);

    // At least some pixels should be non-zero (overlay rendered)
    bool any_nonzero = false;
    for (auto b : buf) {
        if (b != 0) { any_nonzero = true; break; }
    }
    EXPECT_TRUE(any_nonzero) << "Open mapper UI should modify the buffer";
}

// ═══════════════════════════════════════════════════════════════════════════
// Save / Cancel
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(MapperUITest, SaveButton_CommitsRemaps) {
    mapper_ui_.open();
    size_t before = mapper_.customCount();
    mapper_ui_.addPendingRemap(0x04, 0x05);  // Remap A→B
    mapper_ui_.commitRemaps();
    EXPECT_GT(mapper_.customCount(), before);
}

TEST_F(MapperUITest, CloseCommitsPendingRemaps) {
    mapper_ui_.open();
    size_t before = mapper_.customCount();
    mapper_ui_.addPendingRemap(0x04, 0x05);  // Remap A→B
    mapper_ui_.close();  // Escape / close should commit pending remaps
    EXPECT_GT(mapper_.customCount(), before)
        << "Closing the mapper UI should commit pending remaps";
}

TEST_F(MapperUITest, EscapeKeyCommitsPendingRemaps) {
    mapper_ui_.open();
    size_t before = mapper_.customCount();
    mapper_ui_.addPendingRemap(0x04, 0x05);  // Remap A→B
    mapper_ui_.handleKey(0x29, true);  // Escape scancode
    EXPECT_FALSE(mapper_ui_.isOpen());
    EXPECT_GT(mapper_.customCount(), before)
        << "Pressing Escape should commit pending remaps via close()";
}

TEST_F(MapperUITest, CancelButton_DiscardsRemaps) {
    mapper_ui_.open();
    size_t before = mapper_.customCount();
    mapper_ui_.addPendingRemap(0x04, 0x05);
    mapper_ui_.discardRemaps();
    EXPECT_EQ(mapper_.customCount(), before);
}

// ═══════════════════════════════════════════════════════════════════════════
// Scroll Handling
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(MapperUITest, ScrollHandling_LargeList) {
    mapper_ui_.open();
    // Navigate far down the list
    for (int i = 0; i < 50; ++i) {
        mapper_ui_.handleKey(0x51, true);  // Down
    }
    EXPECT_GT(mapper_ui_.scrollOffset(), 0);
}

// ═══════════════════════════════════════════════════════════════════════════
// gsl-lite Contract Violations
// ═══════════════════════════════════════════════════════════════════════════

TEST(MapperUIContractTest, NullBus_InitializeThrowsFailFast) {
    MapperUI ui;
    InputMapper mapper;
    EXPECT_THROW(ui.initialize(nullptr, &mapper), legends::gsl::fail_fast);
}

TEST(MapperUIContractTest, NullMapper_InitializeThrowsFailFast) {
    MapperUI ui;
    ActionBus bus;
    EXPECT_THROW(ui.initialize(&bus, nullptr), legends::gsl::fail_fast);
}

TEST(MapperUIContractTest, NullRGB_RenderThrowsFailFast) {
    MapperUI ui;
    ActionBus bus;
    InputMapper mapper;
    ui.initialize(&bus, &mapper);
    ui.open();
    EXPECT_THROW(ui.render(nullptr, 640, 480), legends::gsl::fail_fast);
}

} // namespace
} // namespace legends
