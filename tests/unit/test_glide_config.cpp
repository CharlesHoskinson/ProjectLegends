// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for GlideConfig.

#include <gtest/gtest.h>
#include "app/glide_config.h"
#include "app/config_parser.h"
#include "test_utils/temp_file_fixture.h"

#include <string>

namespace legends {
namespace {

class GlideConfigTest : public test_utils::TempFileFixture {
protected:
    GlideConfig glide_;
    ConfigParser parser_;

    std::string writeTempFile(const std::string& content) {
        return test_utils::TempFileFixture::writeTempFile(content, "test_glide");
    }
};

// ═══════════════════════════════════════════════════════════════════════════
// Defaults
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(GlideConfigTest, DefaultEnabledIsFalse) {
    EXPECT_FALSE(glide_.enabled);
}

TEST_F(GlideConfigTest, DefaultWidthIs640) {
    EXPECT_EQ(glide_.width, 640);
}

TEST_F(GlideConfigTest, DefaultHeightIs480) {
    EXPECT_EQ(glide_.height, 480);
}

TEST_F(GlideConfigTest, DefaultLfbAccessIsTrue) {
    EXPECT_TRUE(glide_.lfb_access);
}

TEST_F(GlideConfigTest, DefaultSplashScreenIsEmpty) {
    EXPECT_TRUE(glide_.splash_screen.empty());
}

// ═══════════════════════════════════════════════════════════════════════════
// isValid
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(GlideConfigTest, IsValidWhenDisabled) {
    glide_.enabled = false;
    EXPECT_TRUE(glide_.isValid());
}

TEST_F(GlideConfigTest, IsValidWhenEnabledWithDefaultResolution) {
    glide_.enabled = true;
    EXPECT_TRUE(glide_.isValid());
}

TEST_F(GlideConfigTest, IsValidWhenEnabledWithZeroWidth) {
    glide_.enabled = true;
    glide_.width = 0;
    EXPECT_FALSE(glide_.isValid());
}

TEST_F(GlideConfigTest, IsValidWhenEnabledWithZeroHeight) {
    glide_.enabled = true;
    glide_.height = 0;
    EXPECT_FALSE(glide_.isValid());
}

// ═══════════════════════════════════════════════════════════════════════════
// requiresOpenGL
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(GlideConfigTest, RequiresOpenGLReturnsFalseWhenDisabled) {
    glide_.enabled = false;
    EXPECT_FALSE(glide_.requiresOpenGL());
}

TEST_F(GlideConfigTest, RequiresOpenGLReturnsTrueWhenEnabled) {
    glide_.enabled = true;
    EXPECT_TRUE(glide_.requiresOpenGL());
}

// ═══════════════════════════════════════════════════════════════════════════
// Resolutions and toggles
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(GlideConfigTest, Resolution800x600) {
    glide_.enabled = true;
    glide_.width = 800;
    glide_.height = 600;
    EXPECT_TRUE(glide_.isValid());
    EXPECT_EQ(glide_.width, 800);
    EXPECT_EQ(glide_.height, 600);
}

TEST_F(GlideConfigTest, Resolution1024x768) {
    glide_.enabled = true;
    glide_.width = 1024;
    glide_.height = 768;
    EXPECT_TRUE(glide_.isValid());
    EXPECT_EQ(glide_.width, 1024);
    EXPECT_EQ(glide_.height, 768);
}

TEST_F(GlideConfigTest, LfbAccessToggle) {
    glide_.lfb_access = false;
    EXPECT_FALSE(glide_.lfb_access);
    glide_.lfb_access = true;
    EXPECT_TRUE(glide_.lfb_access);
}

// ═══════════════════════════════════════════════════════════════════════════
// loadFrom
// ═══════════════════════════════════════════════════════════════════════════

TEST_F(GlideConfigTest, LoadFromEmptyConfigKeepsDefaults) {
    auto path = writeTempFile("");
    parser_.loadFile(path);
    glide_.loadFrom(parser_);

    EXPECT_FALSE(glide_.enabled);
    EXPECT_EQ(glide_.width, 640);
    EXPECT_EQ(glide_.height, 480);
    EXPECT_TRUE(glide_.lfb_access);
    EXPECT_TRUE(glide_.splash_screen.empty());
}

TEST_F(GlideConfigTest, MultipleLoadsDontInterfere) {
    auto path1 = writeTempFile("[glide]\nglide=true\nwidth=800\nheight=600\n");
    parser_.loadFile(path1);
    glide_.loadFrom(parser_);
    EXPECT_EQ(glide_.width, 800);

    GlideConfig glide2;
    auto path2 = writeTempFile("[glide]\nglide=false\nwidth=1024\nheight=768\n");
    ConfigParser parser2;
    parser2.loadFile(path2);
    glide2.loadFrom(parser2);

    EXPECT_EQ(glide_.width, 800);
    EXPECT_EQ(glide2.width, 1024);
}

} // namespace
} // namespace legends
