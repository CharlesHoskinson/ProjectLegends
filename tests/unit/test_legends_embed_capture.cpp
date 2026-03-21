/**
 * @file test_legends_embed_capture.cpp
 * @brief Frame capture tests for legends_embed API (capture_rgb, capture_text).
 *
 * Split from test_legends_embed.cpp for faster incremental builds.
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include "internal/legends_instance.h"
#include <cstring>
#include <vector>

// ─────────────────────────────────────────────────────────────────────────────
// Phase 3: Frame Capture API Tests
// ─────────────────────────────────────────────────────────────────────────────

class DosboxxCaptureTest : public ::testing::Test {
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

// Text Capture Tests

TEST_F(DosboxxCaptureTest, CaptureTextQuerySize) {
    size_t count;
    auto err = legends_capture_text(handle_, nullptr, 0, &count, nullptr);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(count, 80u * 25u);  // Default 80x25 text mode
}

TEST_F(DosboxxCaptureTest, CaptureTextReturnsInfo) {
    size_t count;
    legends_text_info_t info;
    auto err = legends_capture_text(handle_, nullptr, 0, &count, &info);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(info.columns, 80u);
    EXPECT_EQ(info.rows, 25u);
    EXPECT_EQ(info.active_page, 0u);
    EXPECT_EQ(info.cursor_visible, 1u);  // Cursor is visible by default
}

TEST_F(DosboxxCaptureTest, CaptureTextFillsBuffer) {
    // Set up predictable test pattern for unit test
    auto* inst = reinterpret_cast<legends_instance*>(handle_);
    inst->frame_state.init_test_pattern();

    size_t count;
    legends_capture_text(handle_, nullptr, 0, &count, nullptr);

    std::vector<legends_text_cell_t> cells(count);
    auto err = legends_capture_text(handle_, cells.data(), cells.size(), &count, nullptr);
    EXPECT_EQ(err, LEGENDS_OK);

    // First character should be 'C' from "C:\>" prompt (from test pattern)
    EXPECT_EQ(cells[0].character, 'C');
    EXPECT_EQ(cells[0].attribute, 0x07);  // Light gray on black
}

TEST_F(DosboxxCaptureTest, CaptureTextBufferTooSmall) {
    size_t count;
    legends_capture_text(handle_, nullptr, 0, &count, nullptr);

    std::vector<legends_text_cell_t> cells(count / 2);  // Too small
    size_t out_count;
    auto err = legends_capture_text(handle_, cells.data(), cells.size(), &out_count, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_BUFFER_TOO_SMALL);
}

TEST_F(DosboxxCaptureTest, CaptureTextRejectsNullCountOut) {
    auto err = legends_capture_text(handle_, nullptr, 0, nullptr, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_POINTER);
}

// RGB Capture Tests

TEST_F(DosboxxCaptureTest, CaptureRgbQuerySize) {
    size_t size;
    uint16_t width, height;
    auto err = legends_capture_rgb(handle_, nullptr, 0, &size, &width, &height);
    EXPECT_EQ(err, LEGENDS_OK);
    // Text mode: 80*8 x 25*16 = 640x400
    EXPECT_EQ(width, 640u);
    EXPECT_EQ(height, 400u);
    EXPECT_EQ(size, 640u * 400u * 3u);  // RGB24
}

TEST_F(DosboxxCaptureTest, CaptureRgbFillsBuffer) {
    // Set up predictable test pattern for unit test
    auto* inst = reinterpret_cast<legends_instance*>(handle_);
    inst->frame_state.init_test_pattern();

    size_t size;
    uint16_t width, height;
    legends_capture_rgb(handle_, nullptr, 0, &size, &width, &height);

    std::vector<uint8_t> buffer(size);
    auto err = legends_capture_rgb(handle_, buffer.data(), buffer.size(), &size, nullptr, nullptr);
    EXPECT_EQ(err, LEGENDS_OK);

    // Buffer should have been filled with something (not all zeros for text areas with content)
    bool has_non_zero = false;
    for (size_t i = 0; i < buffer.size() && !has_non_zero; ++i) {
        if (buffer[i] != 0) has_non_zero = true;
    }
    EXPECT_TRUE(has_non_zero);
}

TEST_F(DosboxxCaptureTest, CaptureRgbBufferTooSmall) {
    size_t size;
    legends_capture_rgb(handle_, nullptr, 0, &size, nullptr, nullptr);

    std::vector<uint8_t> buffer(size / 2);  // Too small
    size_t out_size;
    auto err = legends_capture_rgb(handle_, buffer.data(), buffer.size(), &out_size, nullptr, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_BUFFER_TOO_SMALL);
}

TEST_F(DosboxxCaptureTest, CaptureRgbRejectsNullSizeOut) {
    auto err = legends_capture_rgb(handle_, nullptr, 0, nullptr, nullptr, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_POINTER);
}

// Dirty Tracking Tests

TEST_F(DosboxxCaptureTest, IsFrameDirtyInitiallyTrue) {
    int dirty;
    auto err = legends_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(dirty, 1);  // Initially dirty
}

TEST_F(DosboxxCaptureTest, CaptureTextClearsDirty) {
    // Capture should clear dirty flag
    size_t count;
    legends_capture_text(handle_, nullptr, 0, &count, nullptr);
    std::vector<legends_text_cell_t> cells(count);
    legends_capture_text(handle_, cells.data(), cells.size(), &count, nullptr);

    int dirty;
    legends_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(dirty, 0);  // No longer dirty after capture
}

TEST_F(DosboxxCaptureTest, CaptureRgbClearsDirty) {
    size_t size;
    legends_capture_rgb(handle_, nullptr, 0, &size, nullptr, nullptr);
    std::vector<uint8_t> buffer(size);
    legends_capture_rgb(handle_, buffer.data(), buffer.size(), &size, nullptr, nullptr);

    int dirty;
    legends_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(dirty, 0);  // No longer dirty after capture
}

TEST_F(DosboxxCaptureTest, ResetSetsDirty) {
    // Capture to clear dirty
    size_t count;
    legends_capture_text(handle_, nullptr, 0, &count, nullptr);
    std::vector<legends_text_cell_t> cells(count);
    legends_capture_text(handle_, cells.data(), cells.size(), &count, nullptr);

    int dirty;
    legends_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(dirty, 0);

    // Reset should set dirty again
    legends_reset(handle_);
    legends_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(dirty, 1);
}

// Cursor Tests

TEST_F(DosboxxCaptureTest, GetCursorWorks) {
    // Set up predictable test pattern for unit test
    auto* inst = reinterpret_cast<legends_instance*>(handle_);
    inst->frame_state.init_test_pattern();

    uint8_t x, y;
    int visible;
    auto err = legends_get_cursor(handle_, &x, &y, &visible);
    EXPECT_EQ(err, LEGENDS_OK);
    // After test pattern init, cursor is at column 4, row 0
    EXPECT_EQ(x, 4u);
    EXPECT_EQ(y, 0u);
    EXPECT_EQ(visible, 1);
}

TEST_F(DosboxxCaptureTest, GetCursorWorksWithNullOutputs) {
    // Set up predictable test pattern for unit test
    auto* inst = reinterpret_cast<legends_instance*>(handle_);
    inst->frame_state.init_test_pattern();

    // Should work even if some outputs are null
    auto err = legends_get_cursor(handle_, nullptr, nullptr, nullptr);
    EXPECT_EQ(err, LEGENDS_OK);

    uint8_t x;
    err = legends_get_cursor(handle_, &x, nullptr, nullptr);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(x, 4u);
}

TEST_F(DosboxxCaptureTest, CursorInfoMatchesTextInfo) {
    // Cursor info from text capture should match get_cursor
    size_t count;
    legends_text_info_t info;
    legends_capture_text(handle_, nullptr, 0, &count, &info);

    uint8_t x, y;
    int visible;
    legends_get_cursor(handle_, &x, &y, &visible);

    EXPECT_EQ(info.cursor_x, x);
    EXPECT_EQ(info.cursor_y, y);
    EXPECT_EQ(info.cursor_visible, visible);
}
