// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for MountManager — drive letter parsing, path validation,
// mount type detection, state tracking, and gsl-lite contract enforcement.
// REQ-MOUNT-001, REQ-MOUNT-002

#include <gtest/gtest.h>
#include <legends/gsl.hpp>
#include "app/mount_manager.h"

#include <filesystem>
#include <fstream>
#include <string>

namespace legends {
namespace {

// ═══════════════════════════════════════════════════════════════════════════
// Drive Letter Parsing
// ═══════════════════════════════════════════════════════════════════════════

TEST(MountManagerTest, ParseDriveLetter_ValidAtoZ) {
    EXPECT_EQ(MountManager::parseDriveLetter("A"), 0);
    EXPECT_EQ(MountManager::parseDriveLetter("D"), 3);
    EXPECT_EQ(MountManager::parseDriveLetter("Z"), 25);
}

TEST(MountManagerTest, ParseDriveLetter_CaseInsensitive) {
    EXPECT_EQ(MountManager::parseDriveLetter("a"), 0);
    EXPECT_EQ(MountManager::parseDriveLetter("d"), 3);
    EXPECT_EQ(MountManager::parseDriveLetter("z"), 25);
}

TEST(MountManagerTest, ParseDriveLetter_Invalid) {
    EXPECT_EQ(MountManager::parseDriveLetter(""), -1);
    EXPECT_EQ(MountManager::parseDriveLetter("1"), -1);
    EXPECT_EQ(MountManager::parseDriveLetter("AB"), -1);
    EXPECT_EQ(MountManager::parseDriveLetter("!"), -1);
}

// ═══════════════════════════════════════════════════════════════════════════
// Host Path Validation
// ═══════════════════════════════════════════════════════════════════════════

TEST(MountManagerTest, ValidateHostPath_ExistingDir) {
    auto tmp = std::filesystem::temp_directory_path() / "legends_mount_test_dir";
    std::filesystem::create_directories(tmp);

    EXPECT_TRUE(MountManager::validateHostPath(tmp.string()));

    std::filesystem::remove_all(tmp);
}

TEST(MountManagerTest, ValidateHostPath_NonexistentDir) {
    EXPECT_FALSE(MountManager::validateHostPath("/nonexistent/path/that/should/not/exist"));
}

TEST(MountManagerTest, ValidateHostPath_FileNotDir) {
    auto tmp = std::filesystem::temp_directory_path() / "legends_mount_test_file.txt";
    { std::ofstream f(tmp); f << "test"; }

    EXPECT_FALSE(MountManager::validateHostPath(tmp.string()));

    std::filesystem::remove(tmp);
}

// ═══════════════════════════════════════════════════════════════════════════
// Image Path Validation
// ═══════════════════════════════════════════════════════════════════════════

TEST(MountManagerTest, ValidateImagePath_SupportedExtensions) {
    EXPECT_TRUE(MountManager::validateImageExtension(".iso"));
    EXPECT_TRUE(MountManager::validateImageExtension(".img"));
    EXPECT_TRUE(MountManager::validateImageExtension(".ima"));
    EXPECT_TRUE(MountManager::validateImageExtension(".cue"));
    EXPECT_TRUE(MountManager::validateImageExtension(".bin"));
}

TEST(MountManagerTest, ValidateImagePath_CaseInsensitive) {
    EXPECT_TRUE(MountManager::validateImageExtension(".ISO"));
    EXPECT_TRUE(MountManager::validateImageExtension(".Img"));
    EXPECT_TRUE(MountManager::validateImageExtension(".CUE"));
}

TEST(MountManagerTest, ValidateImagePath_UnsupportedExtension) {
    EXPECT_FALSE(MountManager::validateImageExtension(".txt"));
    EXPECT_FALSE(MountManager::validateImageExtension(".exe"));
    EXPECT_FALSE(MountManager::validateImageExtension(""));
}

// ═══════════════════════════════════════════════════════════════════════════
// Mount Type Detection
// ═══════════════════════════════════════════════════════════════════════════

TEST(MountManagerTest, DetectMountType_Directory) {
    auto tmp = std::filesystem::temp_directory_path() / "legends_mount_detect";
    std::filesystem::create_directories(tmp);

    EXPECT_EQ(MountManager::detectMountType(tmp.string()), MountType::Directory);

    std::filesystem::remove_all(tmp);
}

TEST(MountManagerTest, DetectMountType_ImageByExtension) {
    EXPECT_EQ(MountManager::detectMountType("/some/path/game.iso"), MountType::ISO);
    EXPECT_EQ(MountManager::detectMountType("/some/path/game.ISO"), MountType::ISO);
    EXPECT_EQ(MountManager::detectMountType("/some/path/disk.img"), MountType::FATImage);
    EXPECT_EQ(MountManager::detectMountType("/some/path/disk.ima"), MountType::FATImage);
    EXPECT_EQ(MountManager::detectMountType("/some/path/game.cue"), MountType::ISO);
    EXPECT_EQ(MountManager::detectMountType("/some/path/game.bin"), MountType::FATImage);
}

// ═══════════════════════════════════════════════════════════════════════════
// CLI Mount Argument Parsing
// ═══════════════════════════════════════════════════════════════════════════

TEST(MountManagerTest, ParseCLIMount_Valid) {
    auto result = MountManager::parseMountArg("D:=/path/to/dir");
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result->letter, 'D');
    EXPECT_EQ(result->host_path, "/path/to/dir");
}

TEST(MountManagerTest, ParseCLIMount_LowercaseLetter) {
    auto result = MountManager::parseMountArg("c:=/dos/games");
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result->letter, 'C');  // Normalized to uppercase
    EXPECT_EQ(result->host_path, "/dos/games");
}

TEST(MountManagerTest, ParseCLIMount_Invalid) {
    EXPECT_FALSE(MountManager::parseMountArg("invalid").has_value());
    EXPECT_FALSE(MountManager::parseMountArg(":=/path").has_value());
    EXPECT_FALSE(MountManager::parseMountArg("D:=").has_value());
    EXPECT_FALSE(MountManager::parseMountArg("").has_value());
    EXPECT_FALSE(MountManager::parseMountArg("1:=/path").has_value());
}

// ═══════════════════════════════════════════════════════════════════════════
// Mount State Tracking
// ═══════════════════════════════════════════════════════════════════════════

TEST(MountManagerTest, MountState_InitiallyEmpty) {
    MountManager mgr;
    EXPECT_FALSE(mgr.isMounted('A'));
    EXPECT_FALSE(mgr.isMounted('C'));
    EXPECT_FALSE(mgr.isMounted('Z'));
}

TEST(MountManagerTest, MountState_TracksActive) {
    MountManager mgr;
    auto tmp = std::filesystem::temp_directory_path() / "legends_mount_state";
    std::filesystem::create_directories(tmp);

    EXPECT_TRUE(mgr.mountLocal('D', tmp.string()));
    EXPECT_TRUE(mgr.isMounted('D'));

    EXPECT_TRUE(mgr.unmount('D'));
    EXPECT_FALSE(mgr.isMounted('D'));

    std::filesystem::remove_all(tmp);
}

TEST(MountManagerTest, MountState_RejectsDuplicate) {
    MountManager mgr;
    auto tmp = std::filesystem::temp_directory_path() / "legends_mount_dup";
    std::filesystem::create_directories(tmp);

    EXPECT_TRUE(mgr.mountLocal('D', tmp.string()));
    EXPECT_FALSE(mgr.mountLocal('D', tmp.string()));  // Already mounted

    mgr.unmount('D');
    std::filesystem::remove_all(tmp);
}

TEST(MountManagerTest, UnmountNonexistent_ReturnsFalse) {
    MountManager mgr;
    EXPECT_FALSE(mgr.unmount('D'));
}

// ═══════════════════════════════════════════════════════════════════════════
// Security: Path Traversal
// ═══════════════════════════════════════════════════════════════════════════

TEST(MountManagerTest, PathTraversal_DotDot_Rejected) {
    EXPECT_FALSE(MountManager::validateHostPath("../etc/passwd"));
    EXPECT_FALSE(MountManager::validateHostPath("/tmp/../etc/passwd"));
}

TEST(MountManagerTest, MaxPathLength_Handled) {
    std::string long_path(500, 'a');
    // Very long path should not crash, just return false (doesn't exist)
    EXPECT_FALSE(MountManager::validateHostPath(long_path));
}

// ═══════════════════════════════════════════════════════════════════════════
// Mount Info Retrieval
// ═══════════════════════════════════════════════════════════════════════════

TEST(MountManagerTest, GetMountInfo_ReturnsInfoWhenMounted) {
    MountManager mgr;
    auto tmp = std::filesystem::temp_directory_path() / "legends_mount_info";
    std::filesystem::create_directories(tmp);

    mgr.mountLocal('E', tmp.string());
    auto info = mgr.getMountInfo('E');
    ASSERT_TRUE(info.has_value());
    EXPECT_EQ(info->letter, 'E');
    EXPECT_EQ(info->type, MountType::Directory);

    mgr.unmount('E');
    std::filesystem::remove_all(tmp);
}

TEST(MountManagerTest, GetMountInfo_ReturnsNulloptWhenNotMounted) {
    MountManager mgr;
    EXPECT_FALSE(mgr.getMountInfo('A').has_value());
}

// ═══════════════════════════════════════════════════════════════════════════
// gsl-lite Contract Violations
// ═══════════════════════════════════════════════════════════════════════════

TEST(MountManagerTest, InvalidDriveLetter_MountThrowsFailFast) {
    MountManager mgr;
    // Drive letter '1' is not A-Z
    EXPECT_THROW(mgr.mountLocal('1', "/tmp"), legends::gsl::fail_fast);
}

TEST(MountManagerTest, InvalidDriveLetter_UnmountThrowsFailFast) {
    MountManager mgr;
    EXPECT_THROW(mgr.unmount('!'), legends::gsl::fail_fast);
}

TEST(MountManagerTest, InvalidDriveLetter_IsMountedThrowsFailFast) {
    MountManager mgr;
    EXPECT_THROW(mgr.isMounted('0'), legends::gsl::fail_fast);
}

TEST(MountManagerTest, EmptyPath_MountThrowsFailFast) {
    MountManager mgr;
    EXPECT_THROW(mgr.mountLocal('D', ""), legends::gsl::fail_fast);
}

} // namespace
} // namespace legends
