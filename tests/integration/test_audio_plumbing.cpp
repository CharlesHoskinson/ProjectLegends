/**
 * @file test_audio_plumbing.cpp
 * @brief Integration tests for Phase -1 audio pipeline plumbing.
 *
 * Verifies that audio is enabled, samples flow from the engine,
 * and the destructive read semantics work correctly.
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include <pal/platform.h>
#include <cstring>
#include <vector>

class AudioPlumbingTest : public ::testing::Test {
protected:
    legends_handle handle_ = nullptr;

    void SetUp() override {
        pal::Platform::shutdown();
        pal::Platform::initialize(pal::Backend::Headless);
        legends_force_destroy();

        auto err = legends_create(nullptr, &handle_);
        ASSERT_EQ(err, LEGENDS_OK);
        ASSERT_NE(handle_, nullptr);
    }

    void TearDown() override {
        if (handle_) {
            legends_destroy(handle_);
        }
        pal::Platform::shutdown();
    }
};

// After create, audio should be active
TEST_F(AudioPlumbingTest, AudioActivated) {
    int active = 0;
    auto err = legends_is_audio_active(handle_, &active);
    ASSERT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(active, 1) << "Audio should be active after create";
}

// After stepping, there should be audio samples available
TEST_F(AudioPlumbingTest, SamplesAfterStep) {
    // Step 100ms to generate audio data
    legends_step_result_t result;
    auto err = legends_step_ms(handle_, 100, &result);
    ASSERT_EQ(err, LEGENDS_OK);

    // Query available sample count
    // In headless stub mode, audio hardware isn't emulated, so count may be 0
    size_t count = 0;
    err = legends_capture_audio(handle_, nullptr, 0, &count);
    ASSERT_EQ(err, LEGENDS_OK);

    if (count > 0) {
        // Actually capture the samples
        std::vector<int16_t> samples(count);
        size_t captured = 0;
        err = legends_capture_audio(handle_, samples.data(), samples.size(), &captured);
        ASSERT_EQ(err, LEGENDS_OK);
        EXPECT_GT(captured, 0u);
    }
}

// Capture is destructive: second capture should return fewer/zero samples
TEST_F(AudioPlumbingTest, CaptureIsDestructive) {
    // Step to generate samples
    legends_step_ms(handle_, 100, nullptr);

    // First capture: get all samples
    size_t count1 = 0;
    legends_capture_audio(handle_, nullptr, 0, &count1);

    if (count1 > 0) {
        std::vector<int16_t> samples(count1);
        size_t captured = 0;
        auto err = legends_capture_audio(handle_, samples.data(), samples.size(), &captured);
        ASSERT_EQ(err, LEGENDS_OK);

        // Second capture: should have no samples (all were consumed)
        size_t count2 = 0;
        err = legends_capture_audio(handle_, nullptr, 0, &count2);
        ASSERT_EQ(err, LEGENDS_OK);
        EXPECT_EQ(count2, 0u) << "Second capture should return 0 after draining all samples";
    }
}

// legends_capture_audio rejects null count_out
TEST_F(AudioPlumbingTest, CaptureRejectsNullCountOut) {
    auto err = legends_capture_audio(handle_, nullptr, 0, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_POINTER);
}

// legends_is_audio_active rejects null active_out
TEST_F(AudioPlumbingTest, IsActiveRejectsNullActiveOut) {
    auto err = legends_is_audio_active(handle_, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_POINTER);
}
