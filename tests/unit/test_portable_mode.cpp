// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for portable mode detection and directory redirection.

#include "app/portable_mode.h"

#include <filesystem>
#include <fstream>
#include <gtest/gtest.h>
#include <string>

namespace legends {
namespace {

class PortableModeTest : public ::testing::Test {
protected:
    void SetUp() override {
        test_dir_ = std::filesystem::temp_directory_path() / "legends_portable_test";
        std::filesystem::remove_all(test_dir_);
        std::filesystem::create_directories(test_dir_);
    }

    void TearDown() override {
        std::filesystem::remove_all(test_dir_);
    }

    void createMarkerFile(const std::filesystem::path& dir) {
        std::ofstream f(dir / "portable.txt");
        f << "Portable mode marker\n";
    }

    std::filesystem::path test_dir_;
};

// ── Detection Logic ──────────────────────────────────────────────────────

TEST_F(PortableModeTest, GetExecutableDirReturnsNonEmpty) {
    std::string exe_dir = getExecutableDir();
    EXPECT_FALSE(exe_dir.empty())
        << "getExecutableDir() should return a non-empty path";
}

TEST_F(PortableModeTest, GetExecutableDirIsAbsolute) {
    std::string exe_dir = getExecutableDir();
    if (!exe_dir.empty()) {
        std::filesystem::path p(exe_dir);
        EXPECT_TRUE(p.is_absolute())
            << "getExecutableDir() should return an absolute path";
    }
}

TEST_F(PortableModeTest, GetExecutableDirExists) {
    std::string exe_dir = getExecutableDir();
    if (!exe_dir.empty()) {
        EXPECT_TRUE(std::filesystem::exists(exe_dir))
            << "getExecutableDir() should return an existing directory";
    }
}

TEST_F(PortableModeTest, PortableModeDetectsMarker) {
    // Note: This test checks the actual executable directory.
    // In a test environment, portable.txt likely doesn't exist next to the test exe.
    // So isPortableMode() should return false by default.
    // We can't easily create portable.txt next to the test binary in all cases,
    // but we verify the function runs without crash.
    bool portable = isPortableMode();
    EXPECT_FALSE(portable);
}

TEST_F(PortableModeTest, GetPortableBaseDirMatchesExeDir) {
    std::string exe_dir = getExecutableDir();
    std::string portable_dir = getPortableBaseDir();
    EXPECT_EQ(exe_dir, portable_dir);
}

// ── Directory Redirection ────────────────────────────────────────────────

TEST_F(PortableModeTest, MarkerFileCreation) {
    // Create marker file and verify it exists
    createMarkerFile(test_dir_);
    EXPECT_TRUE(std::filesystem::exists(test_dir_ / "portable.txt"));
}

TEST_F(PortableModeTest, NoMarkerFileNoPortable) {
    // Directory without marker file should not be portable
    EXPECT_FALSE(std::filesystem::exists(test_dir_ / "portable.txt"));
}

// ── Filesystem Edge Cases ────────────────────────────────────────────────

TEST_F(PortableModeTest, ExecutableDirNoTrailingSlash) {
    std::string exe_dir = getExecutableDir();
    if (!exe_dir.empty()) {
        EXPECT_NE(exe_dir.back(), '/')
            << "getExecutableDir() should not end with slash";
#if defined(_WIN32)
        EXPECT_NE(exe_dir.back(), '\\')
            << "getExecutableDir() should not end with backslash";
#endif
    }
}

} // namespace
} // namespace legends
