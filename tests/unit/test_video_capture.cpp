// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for VideoCapture — AVI recording with ZMBV codec.
// REQ-CAPTURE-003: Video capture

#include <gtest/gtest.h>
#include <legends/gsl.hpp>
#include "app/video_capture.h"

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <string>
#include <vector>

namespace legends {
namespace {

class VideoCaptureTest : public ::testing::Test {
protected:
    void SetUp() override {
        output_dir_ = std::filesystem::temp_directory_path() / "legends_vidcap_test";
        std::filesystem::create_directories(output_dir_);
        output_path_ = (output_dir_ / "test_output.avi").string();
    }

    void TearDown() override {
        if (capture_.isRecording()) {
            capture_.stopCapture();
        }
        std::filesystem::remove_all(output_dir_);
    }

    VideoCapture capture_;
    std::filesystem::path output_dir_;
    std::string output_path_;
};

// ═══════════════════════════════════════════════════════════════════════════
// Initial State
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(VideoCaptureTest, IsRecording_InitiallyFalse) {
    EXPECT_FALSE(capture_.isRecording());
}

TEST_F(VideoCaptureTest, FramesWritten_InitiallyZero) {
    EXPECT_EQ(capture_.framesWritten(), 0u);
}

// ═══════════════════════════════════════════════════════════════════════════
// Start / Stop
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(VideoCaptureTest, StartCapture_CreatesFile) {
    EXPECT_TRUE(capture_.startCapture(output_path_, 640, 480, 30));
    EXPECT_TRUE(capture_.isRecording());
    EXPECT_TRUE(std::filesystem::exists(output_path_));
}

TEST_F(VideoCaptureTest, StopCapture_FinalizesFile) {
    ASSERT_TRUE(capture_.startCapture(output_path_, 320, 200, 30));

    // Write a few frames
    std::vector<uint8_t> frame(320 * 200 * 3, 64);
    for (int i = 0; i < 5; ++i) {
        capture_.addVideoFrame(frame.data(), 320, 200);
    }

    capture_.stopCapture();
    EXPECT_FALSE(capture_.isRecording());

    // File should be non-empty
    auto file_size = std::filesystem::file_size(output_path_);
    EXPECT_GT(file_size, 0u) << "AVI file should have data after finalization";
}

TEST_F(VideoCaptureTest, StopWithoutStart_NoOp) {
    // Should not crash or error
    capture_.stopCapture();
    EXPECT_FALSE(capture_.isRecording());
}

TEST_F(VideoCaptureTest, DoubleStart_ReturnsFalse) {
    ASSERT_TRUE(capture_.startCapture(output_path_, 640, 480, 30));
    EXPECT_FALSE(capture_.startCapture(output_path_, 640, 480, 30));
}

// ═══════════════════════════════════════════════════════════════════════════
// Frame Writing
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(VideoCaptureTest, AddVideoFrame_WhileRecording) {
    ASSERT_TRUE(capture_.startCapture(output_path_, 64, 64, 30));
    std::vector<uint8_t> frame(64 * 64 * 3, 128);
    EXPECT_TRUE(capture_.addVideoFrame(frame.data(), 64, 64));
    EXPECT_EQ(capture_.framesWritten(), 1u);
}

TEST_F(VideoCaptureTest, AddAudioSamples_WhileRecording) {
    ASSERT_TRUE(capture_.startCapture(output_path_, 64, 64, 30));
    std::vector<int16_t> audio(4096, 0);
    EXPECT_TRUE(capture_.addAudioSamples(audio.data(), audio.size()));
}

// ═══════════════════════════════════════════════════════════════════════════
// AVI Format Validation
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(VideoCaptureTest, OutputFileIsValidAVI) {
    ASSERT_TRUE(capture_.startCapture(output_path_, 320, 200, 30));
    std::vector<uint8_t> frame(320 * 200 * 3, 0);
    capture_.addVideoFrame(frame.data(), 320, 200);
    capture_.stopCapture();

    // Read first 12 bytes and verify RIFF/AVI header
    std::ifstream f(output_path_, std::ios::binary);
    ASSERT_TRUE(f.good());

    char header[12] = {};
    f.read(header, 12);

    EXPECT_EQ(std::string(header, 4), "RIFF") << "Should start with RIFF";
    EXPECT_EQ(std::string(header + 8, 4), "AVI ") << "Should be AVI format";
}

// ═══════════════════════════════════════════════════════════════════════════
// gsl-lite Contract Violations
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(VideoCaptureTest, NullRGB_AddFrameThrowsFailFast) {
    ASSERT_TRUE(capture_.startCapture(output_path_, 64, 64, 30));
    EXPECT_THROW(capture_.addVideoFrame(nullptr, 64, 64),
                 legends::gsl::fail_fast);
}

TEST_F(VideoCaptureTest, NullPCM_AddAudioThrowsFailFast) {
    ASSERT_TRUE(capture_.startCapture(output_path_, 64, 64, 30));
    EXPECT_THROW(capture_.addAudioSamples(nullptr, 100),
                 legends::gsl::fail_fast);
}

TEST_F(VideoCaptureTest, EmptyPath_StartThrowsFailFast) {
    EXPECT_THROW(capture_.startCapture("", 64, 64, 30),
                 legends::gsl::fail_fast);
}

TEST_F(VideoCaptureTest, ZeroDimensions_StartReturnsFalse) {
    EXPECT_FALSE(capture_.startCapture(output_path_, 0, 0, 30));
}

} // namespace
} // namespace legends
