/**
 * @file test_edge_cases.cpp
 * @brief Edge case and boundary condition tests.
 *
 * Tests extreme dimensions, boundary values, and unusual but valid inputs.
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include <legends/llm_frame.h>
#include <pal/platform.h>
#include <vector>
#include <cstring>
#include <limits>

using namespace legends::llm;

class ApiEdgeCaseTest : public ::testing::Test {
protected:
    legends_handle handle_ = nullptr;

    void SetUp() override {
        pal::Platform::shutdown();
        pal::Platform::initialize(pal::Backend::Headless);
        legends_destroy(reinterpret_cast<legends_handle>(1));
        legends_create(nullptr, &handle_);
    }

    void TearDown() override {
        if (handle_) {
            legends_destroy(handle_);
            handle_ = nullptr;
        }
        pal::Platform::shutdown();
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// Step Edge Cases
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(ApiEdgeCaseTest, StepZeroCycles) {
    legends_step_result_t result;
    legends_error_t err = legends_step_cycles(handle_, 0, &result);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(result.cycles_executed, 0u);
}

TEST_F(ApiEdgeCaseTest, StepZeroMs) {
    legends_step_result_t result;
    legends_error_t err = legends_step_ms(handle_, 0, &result);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(result.cycles_executed, 0u);
}

TEST_F(ApiEdgeCaseTest, StepOneCycle) {
    legends_step_result_t result;
    legends_error_t err = legends_step_cycles(handle_, 1, &result);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(result.cycles_executed, 1u);
}

TEST_F(ApiEdgeCaseTest, StepOneMs) {
    legends_step_result_t result;
    legends_error_t err = legends_step_ms(handle_, 1, &result);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_GT(result.cycles_executed, 0u);
}

TEST_F(ApiEdgeCaseTest, StepLargeCycleCount) {
    legends_step_result_t result;
    legends_error_t err = legends_step_cycles(handle_, 1000000, &result);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(result.cycles_executed, 1000000u);
}

TEST_F(ApiEdgeCaseTest, StepMaxMs) {
    legends_step_result_t result;
    // Step for max reasonable ms (10 seconds)
    legends_error_t err = legends_step_ms(handle_, 10000, &result);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_GT(result.cycles_executed, 0u);
}

TEST_F(ApiEdgeCaseTest, StepWithNullResult) {
    // Stepping with null result pointer should still work
    legends_error_t err = legends_step_cycles(handle_, 1000, nullptr);
    EXPECT_EQ(err, LEGENDS_OK);

    err = legends_step_ms(handle_, 10, nullptr);
    EXPECT_EQ(err, LEGENDS_OK);
}

// ─────────────────────────────────────────────────────────────────────────────
// Input Edge Cases
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(ApiEdgeCaseTest, KeyEventCommonScancodes) {
    // Test common AT scancode values
    // Standard keys should all work
    std::vector<uint8_t> common_scancodes = {
        0x01, // Escape
        0x1E, // A
        0x30, // B
        0x2E, // C
        0x1C, // Enter
        0x39, // Space
        0x0E, // Backspace
        0x0F, // Tab
    };

    for (uint8_t scancode : common_scancodes) {
        legends_error_t err = legends_key_event(handle_, scancode, 1);
        EXPECT_EQ(err, LEGENDS_OK) << "Failed for scancode " << static_cast<int>(scancode);

        err = legends_key_event(handle_, scancode, 0);
        EXPECT_EQ(err, LEGENDS_OK) << "Failed for scancode release " << static_cast<int>(scancode);
    }
}

TEST_F(ApiEdgeCaseTest, KeyEventExtCommonScancodes) {
    // Test common extended (E0-prefixed) scancodes
    std::vector<uint8_t> common_ext = {
        0x4D, // Right arrow
        0x4B, // Left arrow
        0x48, // Up arrow
        0x50, // Down arrow
        0x47, // Home
        0x4F, // End
        0x49, // Page Up
        0x51, // Page Down
        0x52, // Insert
        0x53, // Delete
    };

    for (uint8_t scancode : common_ext) {
        legends_error_t err = legends_key_event_ext(handle_, scancode, 1);
        EXPECT_EQ(err, LEGENDS_OK) << "Failed for ext scancode " << static_cast<int>(scancode);

        err = legends_key_event_ext(handle_, scancode, 0);
        EXPECT_EQ(err, LEGENDS_OK) << "Failed for ext scancode release " << static_cast<int>(scancode);
    }
}

TEST_F(ApiEdgeCaseTest, MouseEventExtremeDeltas) {
    // Test extreme mouse movement values
    legends_error_t err;

    // Max positive
    err = legends_mouse_event(handle_, INT16_MAX, INT16_MAX, 0);
    EXPECT_EQ(err, LEGENDS_OK);

    // Max negative
    err = legends_mouse_event(handle_, INT16_MIN, INT16_MIN, 0);
    EXPECT_EQ(err, LEGENDS_OK);

    // Zero movement
    err = legends_mouse_event(handle_, 0, 0, 0);
    EXPECT_EQ(err, LEGENDS_OK);
}

TEST_F(ApiEdgeCaseTest, MouseEventAllButtons) {
    // Test all button combinations (bits 0-2)
    for (uint8_t buttons = 0; buttons <= 7; ++buttons) {
        legends_error_t err = legends_mouse_event(handle_, 0, 0, buttons);
        EXPECT_EQ(err, LEGENDS_OK) << "Failed for buttons " << static_cast<int>(buttons);
    }
}

TEST_F(ApiEdgeCaseTest, TextInputEmptyString) {
    legends_error_t err = legends_text_input(handle_, "");
    EXPECT_EQ(err, LEGENDS_OK);
}

TEST_F(ApiEdgeCaseTest, TextInputSingleChar) {
    legends_error_t err = legends_text_input(handle_, "A");
    EXPECT_EQ(err, LEGENDS_OK);
}

TEST_F(ApiEdgeCaseTest, TextInputShortString) {
    // Type a short string that should always work
    std::string text(10, 'X');
    legends_error_t err = legends_text_input(handle_, text.c_str());
    EXPECT_EQ(err, LEGENDS_OK);
}

TEST_F(ApiEdgeCaseTest, TextInputSpecialChars) {
    // Test special characters
    legends_error_t err;

    err = legends_text_input(handle_, "\n");  // Newline
    EXPECT_EQ(err, LEGENDS_OK);

    err = legends_text_input(handle_, "\t");  // Tab
    EXPECT_EQ(err, LEGENDS_OK);

    err = legends_text_input(handle_, " ");   // Space
    EXPECT_EQ(err, LEGENDS_OK);
}

// ─────────────────────────────────────────────────────────────────────────────
// Capture Edge Cases
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(ApiEdgeCaseTest, CaptureTextExactBuffer) {
    // Get exact required size
    size_t count;
    legends_capture_text(handle_, nullptr, 0, &count, nullptr);

    // Allocate exact size
    std::vector<legends_text_cell_t> cells(count);
    legends_error_t err = legends_capture_text(handle_, cells.data(), count, &count, nullptr);
    EXPECT_EQ(err, LEGENDS_OK);
}

TEST_F(ApiEdgeCaseTest, CaptureTextOverSizedBuffer) {
    // Get required size
    size_t count;
    legends_capture_text(handle_, nullptr, 0, &count, nullptr);

    // Allocate larger buffer
    std::vector<legends_text_cell_t> cells(count * 2);
    size_t actual_count = count * 2;
    legends_error_t err = legends_capture_text(handle_, cells.data(), cells.size(), &actual_count, nullptr);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(actual_count, count);  // Should return actual count, not buffer size
}

TEST_F(ApiEdgeCaseTest, CaptureRgbExactBuffer) {
    // Get exact required size
    size_t size;
    uint16_t width, height;
    legends_capture_rgb(handle_, nullptr, 0, &size, &width, &height);

    // Allocate exact size
    std::vector<uint8_t> buffer(size);
    legends_error_t err = legends_capture_rgb(handle_, buffer.data(), size, &size, &width, &height);
    EXPECT_EQ(err, LEGENDS_OK);
}

TEST_F(ApiEdgeCaseTest, CaptureRgbOverSizedBuffer) {
    // Get required size
    size_t size;
    uint16_t width, height;
    legends_capture_rgb(handle_, nullptr, 0, &size, &width, &height);

    // Allocate larger buffer
    std::vector<uint8_t> buffer(size * 2);
    size_t actual_size = size * 2;
    legends_error_t err = legends_capture_rgb(handle_, buffer.data(), buffer.size(), &actual_size, &width, &height);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(actual_size, size);
}

// ─────────────────────────────────────────────────────────────────────────────
// Time and Cycle Edge Cases
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(ApiEdgeCaseTest, GetEmuTimeInitiallyZero) {
    // After create (no stepping), time should be 0
    uint64_t time;
    legends_error_t err = legends_get_emu_time(handle_, &time);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(time, 0u);
}

TEST_F(ApiEdgeCaseTest, GetTotalCyclesInitiallyZero) {
    // After create (no stepping), cycles should be 0
    uint64_t cycles;
    legends_error_t err = legends_get_total_cycles(handle_, &cycles);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(cycles, 0u);
}

TEST_F(ApiEdgeCaseTest, GetEmuTimeAfterReset) {
    legends_step_cycles(handle_, 100000, nullptr);

    uint64_t time_before;
    legends_get_emu_time(handle_, &time_before);
    EXPECT_GT(time_before, 0u);

    legends_reset(handle_);

    uint64_t time_after;
    legends_get_emu_time(handle_, &time_after);
    EXPECT_EQ(time_after, 0u);
}

TEST_F(ApiEdgeCaseTest, GetTotalCyclesAfterReset) {
    legends_step_cycles(handle_, 100000, nullptr);

    uint64_t cycles_before;
    legends_get_total_cycles(handle_, &cycles_before);
    EXPECT_GT(cycles_before, 0u);

    legends_reset(handle_);

    uint64_t cycles_after;
    legends_get_total_cycles(handle_, &cycles_after);
    EXPECT_EQ(cycles_after, 0u);
}

// ─────────────────────────────────────────────────────────────────────────────
// Cursor Edge Cases
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(ApiEdgeCaseTest, CursorPositionValidRange) {
    uint8_t x, y;
    int visible;
    legends_error_t err = legends_get_cursor(handle_, &x, &y, &visible);
    EXPECT_EQ(err, LEGENDS_OK);

    // Cursor should be in valid text mode range
    EXPECT_LT(x, 80u);
    EXPECT_LT(y, 50u);  // Max possible text rows
}

TEST_F(ApiEdgeCaseTest, CursorVisibilityIsBool) {
    uint8_t x, y;
    int visible;
    legends_error_t err = legends_get_cursor(handle_, &x, &y, &visible);
    EXPECT_EQ(err, LEGENDS_OK);

    // Visible should be 0 or 1
    EXPECT_TRUE(visible == 0 || visible == 1);
}

// ─────────────────────────────────────────────────────────────────────────────
// Save/Load Edge Cases
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(ApiEdgeCaseTest, SaveLoadRoundTrip) {
    // Get initial hash
    uint8_t hash_before[32];
    legends_get_state_hash(handle_, hash_before);

    // Save state
    size_t size;
    legends_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> state(size);
    legends_save_state(handle_, state.data(), size, &size);

    // Step to change state
    legends_step_cycles(handle_, 100000, nullptr);

    // Load saved state
    legends_error_t err = legends_load_state(handle_, state.data(), size);
    EXPECT_EQ(err, LEGENDS_OK);

    // Hash should match original
    uint8_t hash_after[32];
    legends_get_state_hash(handle_, hash_after);
    EXPECT_EQ(std::memcmp(hash_before, hash_after, 32), 0);
}

TEST_F(ApiEdgeCaseTest, SaveStateMultipleTimes) {
    std::vector<std::vector<uint8_t>> saves;

    // Save at different points
    for (int i = 0; i < 5; ++i) {
        legends_step_cycles(handle_, 10000, nullptr);

        size_t size;
        legends_save_state(handle_, nullptr, 0, &size);
        std::vector<uint8_t> state(size);
        legends_save_state(handle_, state.data(), size, &size);
        saves.push_back(std::move(state));
    }

    // Each save should be different (different state)
    for (size_t i = 0; i < saves.size() - 1; ++i) {
        EXPECT_NE(saves[i], saves[i + 1]) << "Saves " << i << " and " << i + 1 << " should differ";
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Dirty Flag Edge Cases
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(ApiEdgeCaseTest, DirtyFlagInitially) {
    int dirty;
    legends_error_t err = legends_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(dirty, 1);  // Initially dirty
}

TEST_F(ApiEdgeCaseTest, DirtyFlagClearedAfterCapture) {
    // Capture clears dirty
    size_t count;
    legends_capture_text(handle_, nullptr, 0, &count, nullptr);
    std::vector<legends_text_cell_t> cells(count);
    legends_capture_text(handle_, cells.data(), count, &count, nullptr);

    int dirty;
    legends_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(dirty, 0);
}

TEST_F(ApiEdgeCaseTest, DirtyFlagSetByInput) {
    // Clear dirty first
    size_t count;
    legends_capture_text(handle_, nullptr, 0, &count, nullptr);
    std::vector<legends_text_cell_t> cells(count);
    legends_capture_text(handle_, cells.data(), count, &count, nullptr);

    // Input should set dirty
    legends_key_event(handle_, 0x1E, 1);

    int dirty;
    legends_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(dirty, 1);
}

// ─────────────────────────────────────────────────────────────────────────────
// Frame Builder Edge Cases
// ─────────────────────────────────────────────────────────────────────────────

TEST(FrameBuilderApiEdgeCaseTest, BuildFrameMinDimensions) {
    FrameBuilder builder;
    std::vector<uint8_t> chars(1, 'X');

    auto frame = builder.build_full_frame(1, 1, chars.data(), 0, 0, true);

    EXPECT_GT(frame.frame_id, 0u);
    EXPECT_EQ(frame.mode, VideoMode::Unknown);  // Non-standard dimensions
}

TEST(FrameBuilderApiEdgeCaseTest, BuildFrameMaxStandardDimensions) {
    FrameBuilder builder;
    std::vector<uint8_t> chars(80 * 50, ' ');  // 80x50 is max standard text mode

    auto frame = builder.build_full_frame(80, 50, chars.data(), 0, 0, true);

    EXPECT_GT(frame.frame_id, 0u);
    EXPECT_EQ(frame.mode, VideoMode::Text80x50);
}

TEST(FrameBuilderApiEdgeCaseTest, BuildFrameAllSpaces) {
    FrameBuilder builder;
    std::vector<uint8_t> chars(80 * 25, ' ');

    auto frame = builder.build_full_frame(80, 25, chars.data(), 0, 0, true);

    // Frame should be valid even if all spaces
    EXPECT_FALSE(frame.to_json().empty());
}

TEST(FrameBuilderApiEdgeCaseTest, BuildFrameAllNulls) {
    FrameBuilder builder;
    std::vector<uint8_t> chars(80 * 25, 0);  // All null characters

    auto frame = builder.build_full_frame(80, 25, chars.data(), 0, 0, true);

    EXPECT_FALSE(frame.to_json().empty());
}

TEST(FrameBuilderApiEdgeCaseTest, BuildFrameAllHighASCII) {
    FrameBuilder builder;
    std::vector<uint8_t> chars(80 * 25, 0xFF);  // All high-ASCII

    auto frame = builder.build_full_frame(80, 25, chars.data(), 0, 0, true);

    EXPECT_FALSE(frame.to_json().empty());
}

TEST(FrameBuilderApiEdgeCaseTest, CursorAtBoundaries) {
    FrameBuilder builder;
    std::vector<uint8_t> chars(80 * 25, 'X');

    // Cursor at top-left
    auto frame1 = builder.build_full_frame(80, 25, chars.data(), 0, 0, true);
    EXPECT_EQ(frame1.cursor.column, 0);
    EXPECT_EQ(frame1.cursor.row, 0);

    // Cursor at bottom-right
    auto frame2 = builder.build_full_frame(80, 25, chars.data(), 79, 24, true);
    EXPECT_EQ(frame2.cursor.column, 79);
    EXPECT_EQ(frame2.cursor.row, 24);
}

// ─────────────────────────────────────────────────────────────────────────────
// API Version Edge Cases
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(ApiEdgeCaseTest, GetApiVersionAllFields) {
    // Get all version fields
    uint32_t major, minor, patch;
    legends_error_t err = legends_get_api_version(&major, &minor, &patch);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(major, LEGENDS_API_VERSION_MAJOR);
    EXPECT_EQ(minor, LEGENDS_API_VERSION_MINOR);
    EXPECT_EQ(patch, LEGENDS_API_VERSION_PATCH);
}

