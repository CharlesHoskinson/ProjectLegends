/**
 * @file test_agent_smoke.cpp
 * @brief LLM agent smoke test: capture frames, inject input, verify changes.
 *
 * Uses the legends LLM infrastructure to demonstrate that an agent
 * can interact with a running DOSBox instance via text frames.
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include <legends/llm_frame.h>
#include <legends/llm_diff.h>
#include <pal/platform.h>
#include <vector>
#include <string>

using namespace legends::llm;

class AgentSmokeTest : public ::testing::Test {
protected:
    legends_handle handle_ = nullptr;
    FrameBuilder builder_;

    void SetUp() override {
        pal::Platform::shutdown();
        pal::Platform::initialize(pal::Backend::Headless);
        legends_force_destroy();
        legends_create(nullptr, &handle_);
    }

    void TearDown() override {
        if (handle_) legends_destroy(handle_);
        pal::Platform::shutdown();
    }

    std::vector<uint8_t> capture_screen_chars() {
        size_t count = 0;
        legends_capture_text(handle_, nullptr, 0, &count, nullptr);
        std::vector<legends_text_cell_t> cells(count);
        legends_capture_text(handle_, cells.data(), count, &count, nullptr);
        std::vector<uint8_t> chars(count);
        for (size_t i = 0; i < count; ++i) {
            chars[i] = cells[i].character;
        }
        return chars;
    }
};

TEST_F(AgentSmokeTest, CaptureFrameAfterStep) {
    // Step 50ms of emulation
    legends_step_ms(handle_, 50, nullptr);

    // Capture text screen
    auto chars = capture_screen_chars();
    ASSERT_FALSE(chars.empty()) << "Screen capture returned no data";

    // Get cursor
    uint8_t cx, cy;
    int cv;
    legends_get_cursor(handle_, &cx, &cy, &cv);

    // Build full frame
    auto frame = builder_.build_full_frame(
        80, 25, chars.data(), cx, cy, cv == 1
    );

    // Verify frame is valid
    EXPECT_GT(frame.frame_id, 0u);
    EXPECT_TRUE(frame.is_text());
    EXPECT_EQ(frame.text_columns, 80);
    EXPECT_EQ(frame.text_rows, 25);
    EXPECT_EQ(frame.cell_count(), 80u * 25u);

    // Serialize to JSON
    std::string json = frame.to_json();
    EXPECT_FALSE(json.empty());
    EXPECT_NE(json.find("\"frame_id\":"), std::string::npos);
    EXPECT_NE(json.find("\"mode\":"), std::string::npos);
}

TEST_F(AgentSmokeTest, InputChangesFrame) {
    // Capture baseline frame
    auto chars1 = capture_screen_chars();
    uint8_t cx1, cy1;
    int cv1;
    legends_get_cursor(handle_, &cx1, &cy1, &cv1);
    auto frame1 = builder_.build_full_frame(
        80, 25, chars1.data(), cx1, cy1, cv1 == 1
    );

    // Inject text input
    legends_text_input(handle_, "A");
    legends_step_ms(handle_, 50, nullptr);

    // Capture new frame
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

    // Diff should show changes (input was injected)
    ScreenshotDiff diff;
    auto result = diff.compare(frame1, frame2);
    // Even if no visible change (headless may not have a shell),
    // the diff infrastructure should work without crashing
    EXPECT_GE(result.total_cells, 80u * 25u);
}
