/**
 * @file test_workflow_llm.cpp
 * @brief Integration tests for LLM frame capture and serialization.
 *
 * Tests end-to-end LLM integration workflows.
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include <legends/llm_frame.h>
#include <pal/platform.h>
#include <vector>
#include <string>

using namespace legends::llm;

class LLMWorkflowTest : public ::testing::Test {
protected:
    legends_handle handle_ = nullptr;
    FrameBuilder builder_;

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

    std::vector<uint8_t> capture_screen_chars() {
        size_t count;
        legends_capture_text(handle_, nullptr, 0, &count, nullptr);
        std::vector<legends_text_cell_t> cells(count);
        legends_capture_text(handle_, cells.data(), count, &count, nullptr);

        // Extract character data
        std::vector<uint8_t> chars(count);
        for (size_t i = 0; i < count; ++i) {
            chars[i] = cells[i].character;
        }
        return chars;
    }
};

// E2E: capture -> frame -> JSON
TEST_F(LLMWorkflowTest, CaptureToFrameToJson) {
    legends_step_ms(handle_, 50, nullptr);

    auto chars = capture_screen_chars();

    uint8_t cursor_x, cursor_y;
    int cursor_visible;
    legends_get_cursor(handle_, &cursor_x, &cursor_y, &cursor_visible);

    auto frame = builder_.build_full_frame(
        80, 25, chars.data(), cursor_x, cursor_y, cursor_visible == 1
    );

    std::string json = frame.to_json();

    EXPECT_FALSE(json.empty());
    EXPECT_NE(json.find("\"frame_id\":"), std::string::npos);
    EXPECT_NE(json.find("\"mode\":"), std::string::npos);
}

// E2E: capture -> frame -> canonical text
TEST_F(LLMWorkflowTest, CaptureToFrameToCanonicalText) {
    legends_step_ms(handle_, 50, nullptr);

    auto chars = capture_screen_chars();

    uint8_t cursor_x, cursor_y;
    int cursor_visible;
    legends_get_cursor(handle_, &cursor_x, &cursor_y, &cursor_visible);

    auto frame = builder_.build_full_frame(
        80, 25, chars.data(), cursor_x, cursor_y, cursor_visible == 1
    );

    std::string canonical = frame.to_canonical_text();

    EXPECT_FALSE(canonical.empty());
    // Should contain frame header info
    EXPECT_NE(canonical.find("Frame"), std::string::npos);
}

// E2E: Frame diff workflow
TEST_F(LLMWorkflowTest, FrameDiffWorkflow) {
    auto chars1 = capture_screen_chars();

    uint8_t cx1, cy1;
    int cv1;
    legends_get_cursor(handle_, &cx1, &cy1, &cv1);

    auto frame1 = builder_.build_full_frame(
        80, 25, chars1.data(), cx1, cy1, cv1 == 1
    );

    // Type something
    legends_text_input(handle_, "A");
    legends_step_ms(handle_, 50, nullptr);

    auto chars2 = capture_screen_chars();
    uint8_t cx2, cy2;
    int cv2;
    legends_get_cursor(handle_, &cx2, &cy2, &cv2);

    auto frame2 = builder_.build_diff_frame(
        80, 25, chars2.data(), cx2, cy2, cv2 == 1
    );

    // Both frames should be valid
    EXPECT_GT(frame1.frame_id, 0u);
    EXPECT_GT(frame2.frame_id, frame1.frame_id);
}

// E2E: Hypercall logging
TEST_F(LLMWorkflowTest, HypercallLogging) {
    builder_.set_hypercall_log_limit(5);

    // Add hypercall entries
    for (int i = 0; i < 10; ++i) {
        HypercallLogEntry entry;
        entry.timestamp_us = i * 1000;
        entry.command_id = static_cast<uint16_t>(i);
        entry.success = (i % 2 == 0);
        builder_.add_hypercall_log(entry);
    }

    auto chars = capture_screen_chars();
    auto frame = builder_.build_full_frame(
        80, 25, chars.data(), 0, 0, true
    );

    // Should have last 5 entries (limit enforced)
    EXPECT_LE(frame.hypercall_log.size(), 5u);

    std::string json = frame.to_json();
    EXPECT_NE(json.find("hypercall"), std::string::npos);
}
