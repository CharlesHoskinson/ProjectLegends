// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for platform directory resolution.

#include <gtest/gtest.h>
#include "app/platform_dirs.h"

#include <algorithm>
#include <string>

namespace legends {
namespace {

// ═══════════════════════════════════════════════════════════════════════════
// Non-empty
// ═══════════════════════════════════════════════════════════════════════════

TEST(PlatformDirsTest, ConfigDirNonEmpty) {
    std::string dir = getConfigDir();
    EXPECT_FALSE(dir.empty());
}

TEST(PlatformDirsTest, DataDirNonEmpty) {
    std::string dir = getDataDir();
    EXPECT_FALSE(dir.empty());
}

TEST(PlatformDirsTest, CacheDirNonEmpty) {
    std::string dir = getCacheDir();
    EXPECT_FALSE(dir.empty());
}

// ═══════════════════════════════════════════════════════════════════════════
// Branding — directory contains project name
// ═══════════════════════════════════════════════════════════════════════════

static bool containsProjectName(const std::string& path) {
    // Check for ProjectLegends (Windows/macOS) or projectlegends (Linux)
    std::string lower = path;
    std::transform(lower.begin(), lower.end(), lower.begin(),
                   [](unsigned char c) { return static_cast<char>(std::tolower(c)); });
    return lower.find("projectlegends") != std::string::npos;
}

TEST(PlatformDirsTest, ConfigDirContainsProjectName) {
    EXPECT_TRUE(containsProjectName(getConfigDir()));
}

TEST(PlatformDirsTest, DataDirContainsProjectName) {
    EXPECT_TRUE(containsProjectName(getDataDir()));
}

TEST(PlatformDirsTest, CacheDirContainsProjectName) {
    EXPECT_TRUE(containsProjectName(getCacheDir()));
}

// ═══════════════════════════════════════════════════════════════════════════
// Stability — calling twice returns the same result
// ═══════════════════════════════════════════════════════════════════════════

TEST(PlatformDirsTest, ConfigDirDeterministic) {
    EXPECT_EQ(getConfigDir(), getConfigDir());
}

TEST(PlatformDirsTest, DataDirDeterministic) {
    EXPECT_EQ(getDataDir(), getDataDir());
}

TEST(PlatformDirsTest, CacheDirDeterministic) {
    EXPECT_EQ(getCacheDir(), getCacheDir());
}

} // namespace
} // namespace legends
