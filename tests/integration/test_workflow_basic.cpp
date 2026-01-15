/**
 * @file test_workflow_basic.cpp
 * @brief Integration tests for basic emulator workflows.
 *
 * Tests end-to-end: create -> step -> capture -> destroy sequences.
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include <pal/platform.h>
#include <cstring>
#include <vector>

class BasicWorkflowTest : public ::testing::Test {
protected:
    legends_handle handle_ = nullptr;

    void SetUp() override {
        pal::Platform::shutdown();
        pal::Platform::initialize(pal::Backend::Headless);
        legends_destroy(reinterpret_cast<legends_handle>(1));
    }

    void TearDown() override {
        if (handle_) {
            legends_destroy(handle_);
        }
        pal::Platform::shutdown();
    }
};

// E2E: create -> step -> capture_text -> destroy
TEST_F(BasicWorkflowTest, CreateStepCaptureTextDestroy) {
    // Create
    legends_error_t err = legends_create(nullptr, &handle_);
    ASSERT_EQ(err, LEGENDS_OK);
    ASSERT_NE(handle_, nullptr);

    // Step 100ms
    legends_step_result_t result;
    err = legends_step_ms(handle_, 100, &result);
    ASSERT_EQ(err, LEGENDS_OK);
    EXPECT_GT(result.cycles_executed, 0u);
    EXPECT_EQ(result.stop_reason, LEGENDS_STOP_COMPLETED);

    // Capture text - two-call pattern
    size_t count;
    legends_text_info_t info;
    err = legends_capture_text(handle_, nullptr, 0, &count, &info);
    ASSERT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(count, 80u * 25u);
    EXPECT_EQ(info.columns, 80);
    EXPECT_EQ(info.rows, 25);

    std::vector<legends_text_cell_t> cells(count);
    err = legends_capture_text(handle_, cells.data(), count, &count, nullptr);
    ASSERT_EQ(err, LEGENDS_OK);

    // Verify some content exists
    bool has_content = false;
    for (const auto& cell : cells) {
        if (cell.character != ' ' && cell.character != 0) {
            has_content = true;
            break;
        }
    }
    EXPECT_TRUE(has_content) << "Screen should have some content";

    // Destroy
    err = legends_destroy(handle_);
    EXPECT_EQ(err, LEGENDS_OK);
    handle_ = nullptr;
}

// E2E: create -> step -> capture_rgb -> destroy
TEST_F(BasicWorkflowTest, CreateStepCaptureRgbDestroy) {
    legends_error_t err = legends_create(nullptr, &handle_);
    ASSERT_EQ(err, LEGENDS_OK);

    legends_step_ms(handle_, 50, nullptr);

    // Capture RGB - two-call pattern
    size_t size;
    uint16_t width, height;
    err = legends_capture_rgb(handle_, nullptr, 0, &size, &width, &height);
    ASSERT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(width, 640);
    EXPECT_EQ(height, 400);
    EXPECT_EQ(size, static_cast<size_t>(width) * height * 3);  // RGB24

    std::vector<uint8_t> buffer(size);
    err = legends_capture_rgb(handle_, buffer.data(), size, &size, nullptr, nullptr);
    ASSERT_EQ(err, LEGENDS_OK);

    // Verify non-empty framebuffer
    bool has_content = false;
    for (size_t i = 0; i < buffer.size() && !has_content; ++i) {
        if (buffer[i] != 0) has_content = true;
    }
    EXPECT_TRUE(has_content) << "RGB framebuffer should have some content";
}

// E2E: create -> step -> reset -> step -> destroy
TEST_F(BasicWorkflowTest, CreateStepResetStepDestroy) {
    legends_create(nullptr, &handle_);

    legends_step_cycles(handle_, 50000, nullptr);

    uint64_t time_before_reset;
    legends_get_emu_time(handle_, &time_before_reset);
    EXPECT_GT(time_before_reset, 0u);

    // Reset
    legends_error_t err = legends_reset(handle_);
    ASSERT_EQ(err, LEGENDS_OK);

    uint64_t time_after_reset;
    legends_get_emu_time(handle_, &time_after_reset);
    EXPECT_EQ(time_after_reset, 0u) << "Time should reset to 0";

    // Step again
    legends_step_cycles(handle_, 10000, nullptr);

    uint64_t time_after_step;
    legends_get_emu_time(handle_, &time_after_step);
    EXPECT_GT(time_after_step, 0u);
}

// E2E: Mixed step types
TEST_F(BasicWorkflowTest, MixedStepTypes) {
    legends_create(nullptr, &handle_);

    // Step by cycles
    legends_step_result_t result1;
    legends_step_cycles(handle_, 10000, &result1);
    EXPECT_EQ(result1.cycles_executed, 10000u);

    // Step by time
    legends_step_result_t result2;
    legends_step_ms(handle_, 10, &result2);
    EXPECT_GT(result2.cycles_executed, 0u);

    // Verify total
    uint64_t total_cycles;
    legends_get_total_cycles(handle_, &total_cycles);
    EXPECT_EQ(total_cycles, result1.cycles_executed + result2.cycles_executed);
}

// E2E: Dirty flag tracking
TEST_F(BasicWorkflowTest, DirtyFlagTracking) {
    legends_create(nullptr, &handle_);

    int dirty;
    legends_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(dirty, 1) << "Initially dirty";

    // Capture clears dirty
    size_t count;
    legends_capture_text(handle_, nullptr, 0, &count, nullptr);
    std::vector<legends_text_cell_t> cells(count);
    legends_capture_text(handle_, cells.data(), count, &count, nullptr);

    legends_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(dirty, 0) << "Capture should clear dirty flag";

    // Input sets dirty (not step, since headless stub may not mark dirty on step)
    legends_key_event(handle_, 0x1E, 1);
    legends_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(dirty, 1) << "Input should set dirty flag";
}

// E2E: Cursor position tracking
TEST_F(BasicWorkflowTest, CursorPositionTracking) {
    legends_create(nullptr, &handle_);
    legends_step_ms(handle_, 50, nullptr);

    uint8_t cursor_x, cursor_y;
    int cursor_visible;
    legends_error_t err = legends_get_cursor(handle_, &cursor_x, &cursor_y, &cursor_visible);
    EXPECT_EQ(err, LEGENDS_OK);

    // Cursor should be somewhere valid
    EXPECT_LT(cursor_x, 80);
    EXPECT_LT(cursor_y, 25);
}
