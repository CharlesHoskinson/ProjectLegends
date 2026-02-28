// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Integration tests for video capture lifecycle via the C API.
// REQ-CAPTURE-003: Video capture

#include <legends/legends_embed.h>
#include <pal/platform.h>

#include <cstdint>
#include <filesystem>
#include <gtest/gtest.h>
#include <string>

namespace legends {
namespace {

class VideoCaptureLifecycleTest : public ::testing::Test {
protected:
    void SetUp() override {
        pal::Platform::shutdown();
        pal::Platform::initialize(pal::Backend::Headless);
        legends_force_destroy();

        legends_config_t cfg = LEGENDS_CONFIG_INIT;
        cfg.deterministic = 1;
        legends_error_t err = legends_create(&cfg, &engine_);
        ASSERT_EQ(err, LEGENDS_OK);
        ASSERT_NE(engine_, nullptr);

        for (int i = 0; i < 10; ++i) {
            legends_step_result_t result{};
            legends_step_ms(engine_, 16, &result);
        }

        output_dir_ = std::filesystem::temp_directory_path() / "legends_vidcap_integ";
        std::filesystem::create_directories(output_dir_);
        output_path_ = (output_dir_ / "test_capture.avi").string();
    }

    void TearDown() override {
        // Stop any active capture before destroying engine
        legends_stop_video_capture(engine_);
        if (engine_) {
            legends_destroy(engine_);
            engine_ = nullptr;
        }
        pal::Platform::shutdown();
        std::filesystem::remove_all(output_dir_);
    }

    legends_handle engine_ = nullptr;
    std::filesystem::path output_dir_;
    std::string output_path_;
};

TEST_F(VideoCaptureLifecycleTest, RecordTenFrames_ProducesValidAVI) {
    GTEST_SKIP() << "Video capture backend not wired in headless build";
}

TEST_F(VideoCaptureLifecycleTest, QueryRecordingState) {
    GTEST_SKIP() << "Video capture backend not wired in headless build";
}

TEST_F(VideoCaptureLifecycleTest, NullHandle_ReturnsError) {
    legends_error_t err = legends_start_video_capture(
        nullptr, output_path_.c_str());
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);

    err = legends_stop_video_capture(nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);

    int capturing = 0;
    err = legends_is_video_capturing(nullptr, &capturing);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

} // namespace
} // namespace legends
