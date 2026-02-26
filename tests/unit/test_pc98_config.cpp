// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for PC98Config.

#include <gtest/gtest.h>
#include "app/pc98_config.h"
#include "app/config_parser.h"

#include <filesystem>
#include <fstream>
#include <string>

namespace legends {
namespace {

class PC98ConfigTest : public ::testing::Test {
protected:
    PC98Config pc98_;
    ConfigParser parser_;
    std::vector<std::string> temp_files_;

    void TearDown() override {
        for (auto& f : temp_files_) {
            std::filesystem::remove(f);
        }
    }

    std::string writeTempFile(const std::string& content) {
        auto path = std::filesystem::temp_directory_path() /
                    ("test_pc98_" + std::to_string(counter_++) + ".conf");
        std::ofstream out(path, std::ios::binary);
        out << content;
        out.close();
        auto s = path.string();
        temp_files_.push_back(s);
        return s;
    }

private:
    static inline int counter_ = 0;
};

// ═══════════════════════════════════════════════════════════════════════════
// Defaults
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PC98ConfigTest, DefaultEnabledIsFalse) {
    EXPECT_FALSE(pc98_.enabled);
}

TEST_F(PC98ConfigTest, DefaultGdcClockIsDefault) {
    EXPECT_EQ(pc98_.gdc_clock, "default");
}

TEST_F(PC98ConfigTest, DefaultSoundBoardIsAuto) {
    EXPECT_EQ(pc98_.sound_board, "auto");
}

TEST_F(PC98ConfigTest, DefaultBusMouseIsTrue) {
    EXPECT_TRUE(pc98_.bus_mouse);
}

TEST_F(PC98ConfigTest, MachineTypeIs5) {
    EXPECT_EQ(PC98Config::kMachineType, 5);
}

// ═══════════════════════════════════════════════════════════════════════════
// isValid
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PC98ConfigTest, IsValidReturnsTrueByDefault) {
    EXPECT_TRUE(pc98_.isValid());
}

// ═══════════════════════════════════════════════════════════════════════════
// isValidGDCClock
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PC98ConfigTest, IsValidGDCClockDefault) {
    EXPECT_TRUE(PC98Config::isValidGDCClock("default"));
}

TEST_F(PC98ConfigTest, IsValidGDCClock5MHz) {
    EXPECT_TRUE(PC98Config::isValidGDCClock("5mhz"));
}

TEST_F(PC98ConfigTest, IsValidGDCClockInvalid) {
    EXPECT_FALSE(PC98Config::isValidGDCClock("invalid"));
}

TEST_F(PC98ConfigTest, IsValidGDCClockEmpty) {
    EXPECT_FALSE(PC98Config::isValidGDCClock(""));
}

// ═══════════════════════════════════════════════════════════════════════════
// isValidSoundBoard
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PC98ConfigTest, IsValidSoundBoardAuto) {
    EXPECT_TRUE(PC98Config::isValidSoundBoard("auto"));
}

TEST_F(PC98ConfigTest, IsValidSoundBoard26K) {
    EXPECT_TRUE(PC98Config::isValidSoundBoard("26k"));
}

TEST_F(PC98ConfigTest, IsValidSoundBoard86) {
    EXPECT_TRUE(PC98Config::isValidSoundBoard("86"));
}

TEST_F(PC98ConfigTest, IsValidSoundBoardInvalid) {
    EXPECT_FALSE(PC98Config::isValidSoundBoard("invalid"));
}

// ═══════════════════════════════════════════════════════════════════════════
// loadFrom
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(PC98ConfigTest, LoadFromEmptyConfigKeepsDefaults) {
    auto path = writeTempFile("");
    parser_.loadFile(path);
    pc98_.loadFrom(parser_);

    EXPECT_FALSE(pc98_.enabled);
    EXPECT_EQ(pc98_.gdc_clock, "default");
    EXPECT_EQ(pc98_.sound_board, "auto");
    EXPECT_TRUE(pc98_.bus_mouse);
}

} // namespace
} // namespace legends
