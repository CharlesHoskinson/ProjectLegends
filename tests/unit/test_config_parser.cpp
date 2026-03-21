// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for ConfigParser.

#include <gtest/gtest.h>
#include "app/config_parser.h"
#include "test_utils/temp_file_fixture.h"

#include <string>

namespace legends {
namespace {

class ConfigParserTest : public test_utils::TempFileFixture {
protected:
    ConfigParser parser_;

    std::string writeTempFile(const std::string& content) {
        return test_utils::TempFileFixture::writeTempFile(content, "test_config");
    }
};

// ═══════════════════════════════════════════════════════════════════════════
// Loading
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(ConfigParserTest, LoadValidFile) {
    auto path = writeTempFile("[dosbox]\nmachine=ega\n");
    EXPECT_TRUE(parser_.loadFile(path));
}

TEST_F(ConfigParserTest, LoadNonExistentFile) {
    EXPECT_FALSE(parser_.loadFile("/nonexistent/path/file.conf"));
}

TEST_F(ConfigParserTest, LoadEmptyFile) {
    auto path = writeTempFile("");
    EXPECT_TRUE(parser_.loadFile(path));
}

TEST_F(ConfigParserTest, GetLoadedPath) {
    auto path = writeTempFile("[a]\nk=v\n");
    parser_.loadFile(path);
    EXPECT_EQ(parser_.getLoadedPath(), path);
}

// ═══════════════════════════════════════════════════════════════════════════
// Sections
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(ConfigParserTest, HasSectionAfterLoad) {
    auto path = writeTempFile("[cpu]\ncycles=1000\n");
    parser_.loadFile(path);
    EXPECT_TRUE(parser_.hasSection("cpu"));
}

TEST_F(ConfigParserTest, HasSectionMissing) {
    auto path = writeTempFile("[cpu]\ncycles=1000\n");
    parser_.loadFile(path);
    EXPECT_FALSE(parser_.hasSection("nonexistent"));
}

TEST_F(ConfigParserTest, HasSectionCaseInsensitive) {
    auto path = writeTempFile("[DosBox]\nmachine=vga\n");
    parser_.loadFile(path);
    EXPECT_TRUE(parser_.hasSection("dosbox"));
    EXPECT_TRUE(parser_.hasSection("DOSBOX"));
}

// ═══════════════════════════════════════════════════════════════════════════
// Key=Value
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(ConfigParserTest, GetStringValue) {
    auto path = writeTempFile("[dosbox]\nmachine=ega\n");
    parser_.loadFile(path);
    EXPECT_EQ(parser_.get("dosbox", "machine"), "ega");
}

TEST_F(ConfigParserTest, GetStringDefault) {
    auto path = writeTempFile("[dosbox]\n");
    parser_.loadFile(path);
    EXPECT_EQ(parser_.get("dosbox", "missing", "fallback"), "fallback");
}

TEST_F(ConfigParserTest, HasKeyTrue) {
    auto path = writeTempFile("[cpu]\ncycles=500\n");
    parser_.loadFile(path);
    EXPECT_TRUE(parser_.hasKey("cpu", "cycles"));
}

TEST_F(ConfigParserTest, HasKeyFalse) {
    auto path = writeTempFile("[cpu]\ncycles=500\n");
    parser_.loadFile(path);
    EXPECT_FALSE(parser_.hasKey("cpu", "speed"));
}

TEST_F(ConfigParserTest, KeyCaseInsensitive) {
    auto path = writeTempFile("[cpu]\nCycles=500\n");
    parser_.loadFile(path);
    EXPECT_TRUE(parser_.hasKey("cpu", "cycles"));
    EXPECT_EQ(parser_.get("cpu", "CYCLES"), "500");
}

TEST_F(ConfigParserTest, ValueWithSpaces) {
    auto path = writeTempFile("[path]\ndir = /home/user/games \n");
    parser_.loadFile(path);
    EXPECT_EQ(parser_.get("path", "dir"), "/home/user/games");
}

TEST_F(ConfigParserTest, KeyBeforeSectionGoesToEmptySection) {
    auto path = writeTempFile("loose_key=value\n[section]\nk=v\n");
    parser_.loadFile(path);
    EXPECT_EQ(parser_.get("", "loose_key"), "value");
}

// ═══════════════════════════════════════════════════════════════════════════
// Typed Getters
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(ConfigParserTest, GetIntValid) {
    auto path = writeTempFile("[cpu]\ncycles=3000\n");
    parser_.loadFile(path);
    EXPECT_EQ(parser_.getInt("cpu", "cycles"), 3000);
}

TEST_F(ConfigParserTest, GetIntInvalidDefault) {
    auto path = writeTempFile("[cpu]\ncycles=abc\n");
    parser_.loadFile(path);
    EXPECT_EQ(parser_.getInt("cpu", "cycles", 42), 42);
}

TEST_F(ConfigParserTest, GetIntMissingDefault) {
    auto path = writeTempFile("[cpu]\n");
    parser_.loadFile(path);
    EXPECT_EQ(parser_.getInt("cpu", "cycles", 99), 99);
}

TEST_F(ConfigParserTest, GetBoolTrueValues) {
    for (const char* val : {"true", "yes", "1", "on"}) {
        auto path = writeTempFile(std::string("[s]\nk=") + val + "\n");
        ConfigParser p;
        p.loadFile(path);
        EXPECT_TRUE(p.getBool("s", "k", false)) << "Failed for: " << val;
    }
}

TEST_F(ConfigParserTest, GetBoolFalseValues) {
    for (const char* val : {"false", "no", "0", "off"}) {
        auto path = writeTempFile(std::string("[s]\nk=") + val + "\n");
        ConfigParser p;
        p.loadFile(path);
        EXPECT_FALSE(p.getBool("s", "k", true)) << "Failed for: " << val;
    }
}

TEST_F(ConfigParserTest, GetBoolInvalidDefault) {
    auto path = writeTempFile("[s]\nk=maybe\n");
    parser_.loadFile(path);
    EXPECT_TRUE(parser_.getBool("s", "k", true));
    EXPECT_FALSE(parser_.getBool("s", "k", false));
}

// ═══════════════════════════════════════════════════════════════════════════
// Comments and Whitespace
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(ConfigParserTest, CommentsSkipped) {
    auto path = writeTempFile("# Comment line\n; Another comment\n[s]\nk=v\n");
    parser_.loadFile(path);
    EXPECT_EQ(parser_.get("s", "k"), "v");
}

TEST_F(ConfigParserTest, EmptyLinesSkipped) {
    auto path = writeTempFile("\n\n[s]\n\nk=v\n\n");
    parser_.loadFile(path);
    EXPECT_EQ(parser_.get("s", "k"), "v");
}

TEST_F(ConfigParserTest, WhitespaceTrimmed) {
    auto path = writeTempFile("  [  dosbox  ]  \n  machine  =  vga  \n");
    parser_.loadFile(path);
    // Section header trimming: "[  dosbox  ]" -> section name is "dosbox"
    // The trim only trims the full line then inside brackets. Let's check what actually happens.
    // line = "[ dosbox ]" -> front=='[' back==']' -> substr(1, len-2) = " dosbox " -> trim -> "dosbox"
    EXPECT_TRUE(parser_.hasSection("dosbox"));
    EXPECT_EQ(parser_.get("dosbox", "machine"), "vga");
}

// ═══════════════════════════════════════════════════════════════════════════
// BOM (A4)
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(ConfigParserTest, LoadFileWithUtf8Bom) {
    // UTF-8 BOM: EF BB BF
    std::string bom = "\xEF\xBB\xBF";
    auto path = writeTempFile(bom + "[dosbox]\nmachine=ega\n");
    parser_.loadFile(path);
    EXPECT_TRUE(parser_.hasSection("dosbox"));
    EXPECT_EQ(parser_.get("dosbox", "machine"), "ega");
}

// ═══════════════════════════════════════════════════════════════════════════
// Reload
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(ConfigParserTest, LoadFileClearsPreviousData) {
    auto path1 = writeTempFile("[old]\nk=1\n");
    auto path2 = writeTempFile("[new]\nk=2\n");
    parser_.loadFile(path1);
    EXPECT_TRUE(parser_.hasSection("old"));
    parser_.loadFile(path2);
    EXPECT_FALSE(parser_.hasSection("old"));
    EXPECT_TRUE(parser_.hasSection("new"));
}

} // namespace
} // namespace legends
