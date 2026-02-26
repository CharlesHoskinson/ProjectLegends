// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for CLIOptions::parse().

#include <gtest/gtest.h>
#include "app/cli_parser.h"
#include <climits>
#include <cstdint>
#include <string>
#include <vector>

namespace legends {
namespace {

// Helper to build argv arrays from string literals.
class Args {
public:
    Args(std::initializer_list<const char*> args) {
        for (auto a : args) ptrs_.push_back(const_cast<char*>(a));
        ptrs_.push_back(nullptr);
    }
    int    argc() const { return static_cast<int>(ptrs_.size()) - 1; }
    char** argv()       { return ptrs_.data(); }
private:
    std::vector<char*> ptrs_;
};

// ═══════════════════════════════════════════════════════════════════════════
// Defaults
// ═══════════════════════════════════════════════════════════════════════════

TEST(CLIParserTest, ParseNoArgsSucceeds) {
    Args a{"project_legends"};
    CLIOptions opts;
    EXPECT_TRUE(opts.parse(a.argc(), a.argv()));
    EXPECT_TRUE(opts.parse_ok);
    EXPECT_EQ(opts.conf_path, "");
    EXPECT_FALSE(opts.fullscreen);
    EXPECT_EQ(opts.cycles, 0u);
    EXPECT_EQ(opts.machine_type, "vga");
    EXPECT_FALSE(opts.machine_type_explicit);
    EXPECT_EQ(opts.memsize_kb, 640u);
    EXPECT_EQ(opts.profile, "interactive");
    EXPECT_FALSE(opts.log_enabled);
    EXPECT_EQ(opts.program, "");
    EXPECT_FALSE(opts.show_version);
    EXPECT_FALSE(opts.show_help);
}

// ═══════════════════════════════════════════════════════════════════════════
// Bool Flags
// ═══════════════════════════════════════════════════════════════════════════

TEST(CLIParserTest, ParseFullscreenFlag) {
    Args a{"app", "--fullscreen"};
    CLIOptions opts;
    EXPECT_TRUE(opts.parse(a.argc(), a.argv()));
    EXPECT_TRUE(opts.fullscreen);
}

TEST(CLIParserTest, ParseLogFlag) {
    Args a{"app", "--log"};
    CLIOptions opts;
    EXPECT_TRUE(opts.parse(a.argc(), a.argv()));
    EXPECT_TRUE(opts.log_enabled);
}

// ═══════════════════════════════════════════════════════════════════════════
// Actions
// ═══════════════════════════════════════════════════════════════════════════

TEST(CLIParserTest, ParseVersionFlag) {
    Args a{"app", "--version"};
    CLIOptions opts;
    EXPECT_TRUE(opts.parse(a.argc(), a.argv()));
    EXPECT_TRUE(opts.show_version);
}

TEST(CLIParserTest, ParseHelpLong) {
    Args a{"app", "--help"};
    CLIOptions opts;
    EXPECT_TRUE(opts.parse(a.argc(), a.argv()));
    EXPECT_TRUE(opts.show_help);
}

TEST(CLIParserTest, ParseHelpShort) {
    Args a{"app", "-h"};
    CLIOptions opts;
    EXPECT_TRUE(opts.parse(a.argc(), a.argv()));
    EXPECT_TRUE(opts.show_help);
}

TEST(CLIParserTest, VersionStopsParsingEarly) {
    Args a{"app", "--version", "--fullscreen"};
    CLIOptions opts;
    EXPECT_TRUE(opts.parse(a.argc(), a.argv()));
    EXPECT_TRUE(opts.show_version);
    EXPECT_FALSE(opts.fullscreen); // --fullscreen never reached
}

// ═══════════════════════════════════════════════════════════════════════════
// Values
// ═══════════════════════════════════════════════════════════════════════════

TEST(CLIParserTest, ParseConfPath) {
    Args a{"app", "--conf", "/tmp/my.conf"};
    CLIOptions opts;
    EXPECT_TRUE(opts.parse(a.argc(), a.argv()));
    EXPECT_EQ(opts.conf_path, "/tmp/my.conf");
}

TEST(CLIParserTest, ParseCyclesValue) {
    Args a{"app", "--cycles", "5000"};
    CLIOptions opts;
    EXPECT_TRUE(opts.parse(a.argc(), a.argv()));
    EXPECT_EQ(opts.cycles, 5000u);
}

TEST(CLIParserTest, ParseMachineType) {
    Args a{"app", "--machine", "ega"};
    CLIOptions opts;
    EXPECT_TRUE(opts.parse(a.argc(), a.argv()));
    EXPECT_EQ(opts.machine_type, "ega");
}

TEST(CLIParserTest, ParseMachineTypeExplicitFlag) {
    Args a{"app", "--machine", "vga"};
    CLIOptions opts;
    EXPECT_TRUE(opts.parse(a.argc(), a.argv()));
    EXPECT_EQ(opts.machine_type, "vga");
    EXPECT_TRUE(opts.machine_type_explicit);
}

TEST(CLIParserTest, ParseMemsize) {
    Args a{"app", "--memsize", "1024"};
    CLIOptions opts;
    EXPECT_TRUE(opts.parse(a.argc(), a.argv()));
    EXPECT_EQ(opts.memsize_kb, 1024u);
}

TEST(CLIParserTest, ParseProfile) {
    Args a{"app", "--profile", "deterministic"};
    CLIOptions opts;
    EXPECT_TRUE(opts.parse(a.argc(), a.argv()));
    EXPECT_EQ(opts.profile, "deterministic");
}

// ═══════════════════════════════════════════════════════════════════════════
// Positional
// ═══════════════════════════════════════════════════════════════════════════

TEST(CLIParserTest, ParsePositionalProgram) {
    Args a{"app", "DOOM.EXE"};
    CLIOptions opts;
    EXPECT_TRUE(opts.parse(a.argc(), a.argv()));
    EXPECT_EQ(opts.program, "DOOM.EXE");
}

// ═══════════════════════════════════════════════════════════════════════════
// Errors
// ═══════════════════════════════════════════════════════════════════════════

TEST(CLIParserTest, MissingConfArgFails) {
    Args a{"app", "--conf"};
    CLIOptions opts;
    EXPECT_FALSE(opts.parse(a.argc(), a.argv()));
    EXPECT_FALSE(opts.parse_ok);
    EXPECT_FALSE(opts.error_message.empty());
}

TEST(CLIParserTest, MissingCyclesArgFails) {
    Args a{"app", "--cycles"};
    CLIOptions opts;
    EXPECT_FALSE(opts.parse(a.argc(), a.argv()));
}

TEST(CLIParserTest, InvalidCyclesArgFails) {
    Args a{"app", "--cycles", "notanumber"};
    CLIOptions opts;
    EXPECT_FALSE(opts.parse(a.argc(), a.argv()));
}

TEST(CLIParserTest, MissingMachineArgFails) {
    Args a{"app", "--machine"};
    CLIOptions opts;
    EXPECT_FALSE(opts.parse(a.argc(), a.argv()));
}

TEST(CLIParserTest, MissingMemsizeArgFails) {
    Args a{"app", "--memsize"};
    CLIOptions opts;
    EXPECT_FALSE(opts.parse(a.argc(), a.argv()));
}

TEST(CLIParserTest, InvalidMemsizeArgFails) {
    Args a{"app", "--memsize", "xyz"};
    CLIOptions opts;
    EXPECT_FALSE(opts.parse(a.argc(), a.argv()));
}

TEST(CLIParserTest, UnknownOptionFails) {
    Args a{"app", "--bogus"};
    CLIOptions opts;
    EXPECT_FALSE(opts.parse(a.argc(), a.argv()));
    EXPECT_FALSE(opts.parse_ok);
}

TEST(CLIParserTest, TwoPositionalArgsFails) {
    Args a{"app", "first", "second"};
    CLIOptions opts;
    EXPECT_FALSE(opts.parse(a.argc(), a.argv()));
}

// ═══════════════════════════════════════════════════════════════════════════
// Overflow (A2)
// ═══════════════════════════════════════════════════════════════════════════

TEST(CLIParserTest, OverflowCyclesValue) {
    // On 64-bit systems where unsigned long > uint32_t, this should fail
    if constexpr (sizeof(unsigned long) > sizeof(uint32_t)) {
        Args a{"app", "--cycles", "5000000000"}; // > UINT32_MAX
        CLIOptions opts;
        EXPECT_FALSE(opts.parse(a.argc(), a.argv()));
    }
}

TEST(CLIParserTest, OverflowMemsizeValue) {
    if constexpr (sizeof(unsigned long) > sizeof(uint32_t)) {
        Args a{"app", "--memsize", "5000000000"};
        CLIOptions opts;
        EXPECT_FALSE(opts.parse(a.argc(), a.argv()));
    }
}

TEST(CLIParserTest, ZeroCyclesIsValid) {
    Args a{"app", "--cycles", "0"};
    CLIOptions opts;
    EXPECT_TRUE(opts.parse(a.argc(), a.argv()));
    EXPECT_EQ(opts.cycles, 0u);
}

TEST(CLIParserTest, MaxUint32CyclesIsValid) {
    Args a{"app", "--cycles", "4294967295"}; // UINT32_MAX
    CLIOptions opts;
    EXPECT_TRUE(opts.parse(a.argc(), a.argv()));
    EXPECT_EQ(opts.cycles, UINT32_MAX);
}

// ═══════════════════════════════════════════════════════════════════════════
// Null argv guard (A5)
// ═══════════════════════════════════════════════════════════════════════════

TEST(CLIParserTest, NullArgvWithPositiveArgcFails) {
    CLIOptions opts;
    EXPECT_FALSE(opts.parse(3, nullptr));
    EXPECT_FALSE(opts.parse_ok);
}

TEST(CLIParserTest, ZeroArgcWithNullArgvSucceeds) {
    CLIOptions opts;
    EXPECT_TRUE(opts.parse(0, nullptr));
}

// ═══════════════════════════════════════════════════════════════════════════
// Combo
// ═══════════════════════════════════════════════════════════════════════════

TEST(CLIParserTest, ParseMultipleOptionsAndPositional) {
    Args a{"app", "--fullscreen", "--cycles", "3000", "--machine", "cga",
           "--memsize", "512", "--profile", "deterministic", "--log",
           "--conf", "/etc/dosbox.conf", "GAME.COM"};
    CLIOptions opts;
    EXPECT_TRUE(opts.parse(a.argc(), a.argv()));
    EXPECT_TRUE(opts.fullscreen);
    EXPECT_EQ(opts.cycles, 3000u);
    EXPECT_EQ(opts.machine_type, "cga");
    EXPECT_TRUE(opts.machine_type_explicit);
    EXPECT_EQ(opts.memsize_kb, 512u);
    EXPECT_EQ(opts.profile, "deterministic");
    EXPECT_TRUE(opts.log_enabled);
    EXPECT_EQ(opts.conf_path, "/etc/dosbox.conf");
    EXPECT_EQ(opts.program, "GAME.COM");
}

} // namespace
} // namespace legends
