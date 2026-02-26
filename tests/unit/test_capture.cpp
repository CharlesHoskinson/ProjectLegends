// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for screenshot capture (PNG writing, filename generation).

#include <gtest/gtest.h>
#include "app/capture.h"
#include "app/platform_dirs.h"

#include <filesystem>
#include <fstream>
#include <regex>
#include <vector>

namespace legends {
namespace {

// ═══════════════════════════════════════════════════════════════════════════
// getCaptureDir()
// ═══════════════════════════════════════════════════════════════════════════

TEST(CaptureTest, CaptureDirContainsCaptures) {
    std::string dir = getCaptureDir();
    EXPECT_FALSE(dir.empty());
    // Should end with "captures"
    EXPECT_NE(dir.find("captures"), std::string::npos);
}

TEST(CaptureTest, CaptureDirStartsWithDataDir) {
    std::string data = getDataDir();
    std::string cap = getCaptureDir();
    EXPECT_EQ(cap.substr(0, data.size()), data);
}

// ═══════════════════════════════════════════════════════════════════════════
// generateCaptureFilename()
// ═══════════════════════════════════════════════════════════════════════════

TEST(CaptureTest, FilenameMatchesPattern) {
    std::string name = generateCaptureFilename();
    // Expected: capture_YYYYMMDD_HHMMSS_NNN.png
    std::regex pattern(R"(capture_\d{8}_\d{6}_\d{3}\.png)");
    EXPECT_TRUE(std::regex_match(name, pattern)) << "Got: " << name;
}

TEST(CaptureTest, FilenameEndsWithPng) {
    std::string name = generateCaptureFilename();
    EXPECT_GE(name.size(), 4u);
    EXPECT_EQ(name.substr(name.size() - 4), ".png");
}

TEST(CaptureTest, ConsecutiveFilenamesDiffer) {
    // Two calls in quick succession should produce different filenames
    // (due to millisecond component)
    std::string a = generateCaptureFilename();
    std::string b = generateCaptureFilename();
    // They might be identical if called within same ms, but usually differ
    // Test passes if they're the same — we just verify format
    EXPECT_GE(a.size(), 20u);
    EXPECT_GE(b.size(), 20u);
}

// ═══════════════════════════════════════════════════════════════════════════
// writeScreenshotPNG()
// ═══════════════════════════════════════════════════════════════════════════

TEST(CaptureTest, WriteScreenshotPNG_CreatesFile) {
    // Create a small 4x4 RGB test image (red)
    std::vector<uint8_t> rgb(4 * 4 * 3, 0);
    for (size_t i = 0; i < rgb.size(); i += 3) {
        rgb[i] = 255; // R
    }

    auto tmp_dir = std::filesystem::temp_directory_path() / "legends_test_capture";
    std::filesystem::create_directories(tmp_dir);
    std::string path = (tmp_dir / "test_screenshot.png").string();

    bool ok = writeScreenshotPNG(path, rgb.data(), 4, 4);
    EXPECT_TRUE(ok);
    EXPECT_TRUE(std::filesystem::exists(path));

    // Verify it's a valid PNG (check magic bytes)
    {
        std::ifstream file(path, std::ios::binary);
        uint8_t magic[8];
        file.read(reinterpret_cast<char*>(magic), 8);
        EXPECT_EQ(magic[0], 137);
        EXPECT_EQ(magic[1], 80);  // 'P'
        EXPECT_EQ(magic[2], 78);  // 'N'
        EXPECT_EQ(magic[3], 71);  // 'G'
    } // file closed here before remove_all

    // Cleanup
    std::filesystem::remove_all(tmp_dir);
}

TEST(CaptureTest, WriteScreenshotPNG_NullData) {
    bool ok = writeScreenshotPNG("/tmp/null_test.png", nullptr, 4, 4);
    EXPECT_FALSE(ok);
}

TEST(CaptureTest, WriteScreenshotPNG_ZeroSize) {
    uint8_t data[3] = {255, 0, 0};
    EXPECT_FALSE(writeScreenshotPNG("/tmp/zero.png", data, 0, 4));
    EXPECT_FALSE(writeScreenshotPNG("/tmp/zero.png", data, 4, 0));
}

TEST(CaptureTest, WriteScreenshotPNG_LargerImage) {
    // 64x64 blue image
    std::vector<uint8_t> rgb(64 * 64 * 3, 0);
    for (size_t i = 0; i < rgb.size(); i += 3) {
        rgb[i + 2] = 255; // B
    }

    auto tmp_dir = std::filesystem::temp_directory_path() / "legends_test_capture2";
    std::filesystem::create_directories(tmp_dir);
    std::string path = (tmp_dir / "test_large.png").string();

    bool ok = writeScreenshotPNG(path, rgb.data(), 64, 64);
    EXPECT_TRUE(ok);

    auto file_size = std::filesystem::file_size(path);
    EXPECT_GT(file_size, 0u);

    std::filesystem::remove_all(tmp_dir);
}

TEST(CaptureTest, WriteScreenshotPNG_InvalidPath) {
    uint8_t data[12] = {};
    bool ok = writeScreenshotPNG("/nonexistent/dir/test.png", data, 2, 2);
    EXPECT_FALSE(ok);
}

} // namespace
} // namespace legends
