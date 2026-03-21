/**
 * @file test_legends_embed_input.cpp
 * @brief Input injection tests for legends_embed API (key_event, mouse_event, text_input).
 *
 * Split from test_legends_embed.cpp for faster incremental builds.
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include "internal/legends_instance.h"
#include <cstring>
#include <vector>

// ─────────────────────────────────────────────────────────────────────────────
// Phase 4: Input Injection API Tests
// ─────────────────────────────────────────────────────────────────────────────

class DosboxxInputTest : public ::testing::Test {
protected:
    legends_handle handle_ = nullptr;

    void SetUp() override {
        // Clean up any previous instance
        legends_force_destroy();

        auto err = legends_create(nullptr, &handle_);
        ASSERT_EQ(err, LEGENDS_OK);
        ASSERT_NE(handle_, nullptr);
    }

    void TearDown() override {
        legends_destroy(handle_);
    }
};

// Key Event Tests

TEST_F(DosboxxInputTest, KeyEventWorks) {
    // Press 'A' key (scancode 0x1E)
    auto err = legends_key_event(handle_, 0x1E, 1);
    EXPECT_EQ(err, LEGENDS_OK);

    // Release 'A' key
    err = legends_key_event(handle_, 0x1E, 0);
    EXPECT_EQ(err, LEGENDS_OK);
}

TEST_F(DosboxxInputTest, KeyEventSetsDirty) {
    // Clear dirty flag first
    size_t count;
    legends_capture_text(handle_, nullptr, 0, &count, nullptr);
    std::vector<legends_text_cell_t> cells(count);
    legends_capture_text(handle_, cells.data(), cells.size(), &count, nullptr);

    int dirty;
    legends_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(dirty, 0);

    // Key event should set dirty
    legends_key_event(handle_, 0x1E, 1);

    legends_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(dirty, 1);
}

TEST_F(DosboxxInputTest, KeyEventExtWorks) {
    // Press Right Arrow key (E0 + 0x4D)
    auto err = legends_key_event_ext(handle_, 0x4D, 1);
    EXPECT_EQ(err, LEGENDS_OK);

    // Release Right Arrow key
    err = legends_key_event_ext(handle_, 0x4D, 0);
    EXPECT_EQ(err, LEGENDS_OK);
}

TEST_F(DosboxxInputTest, KeyEventExtInsertDeleteHomeEnd) {
    // Insert (E0 + 0x52)
    EXPECT_EQ(legends_key_event_ext(handle_, 0x52, 1), LEGENDS_OK);
    EXPECT_EQ(legends_key_event_ext(handle_, 0x52, 0), LEGENDS_OK);

    // Delete (E0 + 0x53)
    EXPECT_EQ(legends_key_event_ext(handle_, 0x53, 1), LEGENDS_OK);
    EXPECT_EQ(legends_key_event_ext(handle_, 0x53, 0), LEGENDS_OK);

    // Home (E0 + 0x47)
    EXPECT_EQ(legends_key_event_ext(handle_, 0x47, 1), LEGENDS_OK);
    EXPECT_EQ(legends_key_event_ext(handle_, 0x47, 0), LEGENDS_OK);

    // End (E0 + 0x4F)
    EXPECT_EQ(legends_key_event_ext(handle_, 0x4F, 1), LEGENDS_OK);
    EXPECT_EQ(legends_key_event_ext(handle_, 0x4F, 0), LEGENDS_OK);
}

// Text Input Tests

TEST_F(DosboxxInputTest, TextInputWorks) {
    auto err = legends_text_input(handle_, "Hello");
    EXPECT_EQ(err, LEGENDS_OK);
}

TEST_F(DosboxxInputTest, TextInputHandlesNewlines) {
    auto err = legends_text_input(handle_, "DIR\n");
    EXPECT_EQ(err, LEGENDS_OK);
}

TEST_F(DosboxxInputTest, TextInputHandlesShiftChars) {
    // Uppercase letters and shifted symbols
    auto err = legends_text_input(handle_, "ABC!");
    EXPECT_EQ(err, LEGENDS_OK);
}

TEST_F(DosboxxInputTest, TextInputRejectsNull) {
    auto err = legends_text_input(handle_, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_POINTER);
}

TEST_F(DosboxxInputTest, TextInputEmptyStringIsOk) {
    auto err = legends_text_input(handle_, "");
    EXPECT_EQ(err, LEGENDS_OK);
}

TEST_F(DosboxxInputTest, TextInputSetsDirty) {
    // Clear dirty flag first
    size_t count;
    legends_capture_text(handle_, nullptr, 0, &count, nullptr);
    std::vector<legends_text_cell_t> cells(count);
    legends_capture_text(handle_, cells.data(), cells.size(), &count, nullptr);

    int dirty;
    legends_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(dirty, 0);

    // Text input should set dirty
    legends_text_input(handle_, "A");

    legends_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(dirty, 1);
}

// Mouse Event Tests

TEST_F(DosboxxInputTest, MouseEventWorks) {
    // Move mouse with no buttons
    auto err = legends_mouse_event(handle_, 10, 5, 0);
    EXPECT_EQ(err, LEGENDS_OK);
}

TEST_F(DosboxxInputTest, MouseEventWithButtons) {
    // Left button click
    auto err = legends_mouse_event(handle_, 0, 0, 1);  // Left button down
    EXPECT_EQ(err, LEGENDS_OK);

    err = legends_mouse_event(handle_, 0, 0, 0);  // Release
    EXPECT_EQ(err, LEGENDS_OK);
}

TEST_F(DosboxxInputTest, MouseEventRightButton) {
    // Right button click
    auto err = legends_mouse_event(handle_, 0, 0, 2);  // Right button
    EXPECT_EQ(err, LEGENDS_OK);
}

TEST_F(DosboxxInputTest, MouseEventMiddleButton) {
    // Middle button click
    auto err = legends_mouse_event(handle_, 0, 0, 4);  // Middle button
    EXPECT_EQ(err, LEGENDS_OK);
}

TEST_F(DosboxxInputTest, MouseEventNegativeMovement) {
    // Negative movement (move up/left)
    auto err = legends_mouse_event(handle_, -20, -15, 0);
    EXPECT_EQ(err, LEGENDS_OK);
}

TEST_F(DosboxxInputTest, MouseEventSetsDirty) {
    // Clear dirty flag first
    size_t count;
    legends_capture_text(handle_, nullptr, 0, &count, nullptr);
    std::vector<legends_text_cell_t> cells(count);
    legends_capture_text(handle_, cells.data(), cells.size(), &count, nullptr);

    int dirty;
    legends_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(dirty, 0);

    // Mouse event should set dirty
    legends_mouse_event(handle_, 5, 5, 0);

    legends_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(dirty, 1);
}

// Reset Tests

TEST_F(DosboxxInputTest, ResetClearsInputQueues) {
    // Queue some events
    legends_key_event(handle_, 0x1E, 1);
    legends_key_event(handle_, 0x1E, 0);
    legends_mouse_event(handle_, 10, 10, 1);

    // Reset should clear queues
    auto err = legends_reset(handle_);
    EXPECT_EQ(err, LEGENDS_OK);

    // Can still queue events after reset
    err = legends_key_event(handle_, 0x1E, 1);
    EXPECT_EQ(err, LEGENDS_OK);
}
