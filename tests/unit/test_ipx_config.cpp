// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for IPXConfig.

#include <gtest/gtest.h>
#include "app/ipx_config.h"
#include "app/config_parser.h"

#include <filesystem>
#include <fstream>
#include <string>

namespace legends {
namespace {

class IPXConfigTest : public ::testing::Test {
protected:
    IPXConfig ipx_;
    ConfigParser parser_;
    std::vector<std::string> temp_files_;

    void TearDown() override {
        for (auto& f : temp_files_) {
            std::filesystem::remove(f);
        }
    }

    std::string writeTempFile(const std::string& content) {
        auto path = std::filesystem::temp_directory_path() /
                    ("test_ipx_" + std::to_string(counter_++) + ".conf");
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

TEST_F(IPXConfigTest, DefaultEnabledIsFalse) {
    EXPECT_FALSE(ipx_.enabled);
}

TEST_F(IPXConfigTest, DefaultPortIs213) {
    EXPECT_EQ(ipx_.port, 213);
}

TEST_F(IPXConfigTest, DefaultServerIsEmpty) {
    EXPECT_TRUE(ipx_.server.empty());
}

// ═══════════════════════════════════════════════════════════════════════════
// isValid
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(IPXConfigTest, IsValidWithEmptyServerWhenDisabled) {
    ipx_.enabled = false;
    ipx_.server = "";
    EXPECT_TRUE(ipx_.isValid());
}

TEST_F(IPXConfigTest, IsValidWithEmptyServerWhenEnabled) {
    ipx_.enabled = true;
    ipx_.server = "";
    EXPECT_FALSE(ipx_.isValid());
}

TEST_F(IPXConfigTest, IsValidWithServerSetWhenEnabled) {
    ipx_.enabled = true;
    ipx_.server = "192.168.1.1";
    EXPECT_TRUE(ipx_.isValid());
}

TEST_F(IPXConfigTest, PortRangeEdgeZero) {
    ipx_.port = 0;
    EXPECT_EQ(ipx_.port, 0);
}

TEST_F(IPXConfigTest, PortRangeEdge65535) {
    ipx_.port = 65535;
    EXPECT_EQ(ipx_.port, 65535);
}

TEST_F(IPXConfigTest, ServerWithHostname) {
    ipx_.enabled = true;
    ipx_.server = "dosbox.example.com";
    EXPECT_TRUE(ipx_.isValid());
}

TEST_F(IPXConfigTest, ServerWithIPAddress) {
    ipx_.enabled = true;
    ipx_.server = "10.0.0.1";
    EXPECT_TRUE(ipx_.isValid());
}

// ═══════════════════════════════════════════════════════════════════════════
// loadFrom
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(IPXConfigTest, LoadFromEmptyConfigKeepsDefaults) {
    auto path = writeTempFile("");
    parser_.loadFile(path);
    ipx_.loadFrom(parser_);

    EXPECT_FALSE(ipx_.enabled);
    EXPECT_TRUE(ipx_.server.empty());
    EXPECT_EQ(ipx_.port, 213);
}

TEST_F(IPXConfigTest, MultipleLoadsDontInterfere) {
    auto path1 = writeTempFile("[ipx]\nipx=true\nserver=host1\nport=1000\n");
    parser_.loadFile(path1);
    ipx_.loadFrom(parser_);
    EXPECT_EQ(ipx_.server, "host1");

    IPXConfig ipx2;
    auto path2 = writeTempFile("[ipx]\nipx=false\nserver=host2\nport=2000\n");
    ConfigParser parser2;
    parser2.loadFile(path2);
    ipx2.loadFrom(parser2);

    EXPECT_EQ(ipx_.server, "host1");
    EXPECT_EQ(ipx2.server, "host2");
}

TEST_F(IPXConfigTest, DefaultConfigIsValid) {
    EXPECT_TRUE(ipx_.isValid());
}

TEST_F(IPXConfigTest, PortPreservedAfterLoad) {
    auto path = writeTempFile("[ipx]\nport=9999\n");
    parser_.loadFile(path);
    ipx_.loadFrom(parser_);
    EXPECT_EQ(ipx_.port, 9999);
}

TEST_F(IPXConfigTest, ServerPreservedAfterLoad) {
    auto path = writeTempFile("[ipx]\nserver=myhost.local\n");
    parser_.loadFile(path);
    ipx_.loadFrom(parser_);
    EXPECT_EQ(ipx_.server, "myhost.local");
}

} // namespace
} // namespace legends
