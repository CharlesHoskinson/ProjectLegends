/**
 * @file test_workflow_input.cpp
 * @brief Integration tests for input injection workflows.
 *
 * Tests keyboard, mouse, and text input through the C API.
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include <pal/platform.h>
#include <cstring>
#include <vector>

class InputWorkflowTest : public ::testing::Test {
protected:
    legends_handle handle_ = nullptr;

    void SetUp() override {
        pal::Platform::shutdown();
        pal::Platform::initialize(pal::Backend::Headless);
        legends_destroy(reinterpret_cast<legends_handle>(1));
        legends_create(nullptr, &handle_);
    }

    void TearDown() override {
        if (handle_) legends_destroy(handle_);
        pal::Platform::shutdown();
    }

    std::vector<legends_text_cell_t> capture_screen() {
        size_t count;
        legends_capture_text(handle_, nullptr, 0, &count, nullptr);
        std::vector<legends_text_cell_t> cells(count);
        legends_capture_text(handle_, cells.data(), count, &count, nullptr);
        return cells;
    }
};

// Keyboard scancode injection
TEST_F(InputWorkflowTest, KeyboardScancodeInjection) {
    // Initial capture
    legends_step_ms(handle_, 50, nullptr);
    auto before = capture_screen();

    // Press and release 'A' key (AT scancode 0x1E)
    legends_error_t err = legends_key_event(handle_, 0x1E, 1);  // Press
    EXPECT_EQ(err, LEGENDS_OK);
    legends_step_cycles(handle_, 1000, nullptr);

    err = legends_key_event(handle_, 0x1E, 0);  // Release
    EXPECT_EQ(err, LEGENDS_OK);
    legends_step_ms(handle_, 50, nullptr);

    // Dirty flag should be set
    int dirty;
    legends_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(dirty, 1);
}

// Text input translation
TEST_F(InputWorkflowTest, TextInputTranslation) {
    legends_step_ms(handle_, 50, nullptr);

    // Use text_input to type a string
    legends_error_t err = legends_text_input(handle_, "DIR");
    EXPECT_EQ(err, LEGENDS_OK);

    // Step to process input
    legends_step_ms(handle_, 100, nullptr);

    // Verify dirty flag set
    int dirty;
    legends_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(dirty, 1);
}

// Mouse relative movement
TEST_F(InputWorkflowTest, MouseRelativeMovement) {
    legends_step_ms(handle_, 50, nullptr);

    // Send mouse movement
    legends_error_t err = legends_mouse_event(handle_, 10, 5, 0);  // Move only
    EXPECT_EQ(err, LEGENDS_OK);

    legends_step_cycles(handle_, 5000, nullptr);

    // Mouse click
    err = legends_mouse_event(handle_, 0, 0, 1);  // Left button down
    EXPECT_EQ(err, LEGENDS_OK);

    legends_step_cycles(handle_, 2000, nullptr);

    err = legends_mouse_event(handle_, 0, 0, 0);  // Button up
    EXPECT_EQ(err, LEGENDS_OK);
}

// Extended key support (E0-prefixed scancodes)
TEST_F(InputWorkflowTest, ExtendedKeySupport) {
    legends_step_ms(handle_, 50, nullptr);

    // Right arrow key (E0-prefixed)
    legends_error_t err = legends_key_event_ext(handle_, 0x4D, 1);  // Press
    EXPECT_EQ(err, LEGENDS_OK);
    legends_step_cycles(handle_, 1000, nullptr);

    err = legends_key_event_ext(handle_, 0x4D, 0);  // Release
    EXPECT_EQ(err, LEGENDS_OK);

    // Up arrow
    err = legends_key_event_ext(handle_, 0x48, 1);
    EXPECT_EQ(err, LEGENDS_OK);
    legends_step_cycles(handle_, 1000, nullptr);

    err = legends_key_event_ext(handle_, 0x48, 0);
    EXPECT_EQ(err, LEGENDS_OK);

    legends_step_ms(handle_, 50, nullptr);
}
