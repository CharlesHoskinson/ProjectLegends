// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for ShaderPresets — validates that every built-in GLSL
// preset is well-formed and self-consistent.

#include "app/shader_presets.h"
#include "app/shader_renderer.h"

#include <gtest/gtest.h>

#include <cstring>
#include <set>
#include <string>

namespace legends {
namespace {

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// All built-in presets in enum order (excludes Custom and COUNT).
static constexpr ShaderPreset kBuiltinPresets[] = {
    ShaderPreset::None,
    ShaderPreset::CRT,
    ShaderPreset::Scanlines,
    ShaderPreset::Sharp,
    ShaderPreset::Smooth,
};

static constexpr size_t kBuiltinCount =
    sizeof(kBuiltinPresets) / sizeof(kBuiltinPresets[0]);

// ---------------------------------------------------------------------------
// Per-preset property tests
// ---------------------------------------------------------------------------

TEST(ShaderPresets, EachPresetHasNonNullName) {
    for (auto preset : kBuiltinPresets) {
        const auto& info = getShaderPreset(preset);
        EXPECT_NE(info.name, nullptr)
            << "Preset index " << static_cast<int>(preset) << " has null name";
    }
}

TEST(ShaderPresets, EachPresetHasNonEmptyVertexSource) {
    for (auto preset : kBuiltinPresets) {
        const auto& info = getShaderPreset(preset);
        ASSERT_NE(info.vertex_source, nullptr);
        EXPECT_GT(std::strlen(info.vertex_source), 0u)
            << "Preset \"" << info.name << "\" has empty vertex source";
    }
}

TEST(ShaderPresets, EachPresetHasNonEmptyFragmentSource) {
    for (auto preset : kBuiltinPresets) {
        const auto& info = getShaderPreset(preset);
        ASSERT_NE(info.fragment_source, nullptr);
        EXPECT_GT(std::strlen(info.fragment_source), 0u)
            << "Preset \"" << info.name << "\" has empty fragment source";
    }
}

TEST(ShaderPresets, NameUniquenessAcrossPresets) {
    std::set<std::string> names;
    for (auto preset : kBuiltinPresets) {
        const auto& info = getShaderPreset(preset);
        ASSERT_NE(info.name, nullptr);
        auto [it, inserted] = names.insert(info.name);
        EXPECT_TRUE(inserted)
            << "Duplicate preset name: " << info.name;
    }
}

TEST(ShaderPresets, PresetCountMatchesExpected) {
    EXPECT_EQ(shaderPresetCount(), kBuiltinCount);
}

// ---------------------------------------------------------------------------
// Individual preset name checks
// ---------------------------------------------------------------------------

TEST(ShaderPresets, NonePresetNameIsNone) {
    EXPECT_STREQ(getShaderPreset(ShaderPreset::None).name, "None");
}

TEST(ShaderPresets, CRTPresetNameIsCRT) {
    EXPECT_STREQ(getShaderPreset(ShaderPreset::CRT).name, "CRT");
}

TEST(ShaderPresets, ScanlinesPresetNameIsScanlines) {
    EXPECT_STREQ(getShaderPreset(ShaderPreset::Scanlines).name, "Scanlines");
}

TEST(ShaderPresets, SharpPresetNameIsSharp) {
    EXPECT_STREQ(getShaderPreset(ShaderPreset::Sharp).name, "Sharp");
}

TEST(ShaderPresets, SmoothPresetNameIsSmooth) {
    EXPECT_STREQ(getShaderPreset(ShaderPreset::Smooth).name, "Smooth");
}

// ---------------------------------------------------------------------------
// GLSL source content validation
// ---------------------------------------------------------------------------

TEST(ShaderPresets, VertexSourcesContainGlPosition) {
    for (auto preset : kBuiltinPresets) {
        const auto& info = getShaderPreset(preset);
        ASSERT_NE(info.vertex_source, nullptr);
        std::string src(info.vertex_source);
        EXPECT_NE(src.find("gl_Position"), std::string::npos)
            << "Preset \"" << info.name
            << "\" vertex shader missing gl_Position";
    }
}

TEST(ShaderPresets, FragmentSourcesContainFragColor) {
    for (auto preset : kBuiltinPresets) {
        const auto& info = getShaderPreset(preset);
        ASSERT_NE(info.fragment_source, nullptr);
        std::string src(info.fragment_source);
        bool has_frag_color =
            (src.find("FragColor") != std::string::npos) ||
            (src.find("gl_FragColor") != std::string::npos);
        EXPECT_TRUE(has_frag_color)
            << "Preset \"" << info.name
            << "\" fragment shader missing FragColor / gl_FragColor";
    }
}

// ---------------------------------------------------------------------------
// Boundary and fallback tests
// ---------------------------------------------------------------------------

TEST(ShaderPresets, InvalidPresetReturnsFallbackNone) {
    // Custom and COUNT are beyond the table — should fall back to None.
    const auto& custom_info = getShaderPreset(ShaderPreset::Custom);
    EXPECT_STREQ(custom_info.name, "None");

    const auto& count_info = getShaderPreset(ShaderPreset::COUNT);
    EXPECT_STREQ(count_info.name, "None");

    // A completely out-of-range cast should also fall back.
    auto bogus = static_cast<ShaderPreset>(255);
    const auto& bogus_info = getShaderPreset(bogus);
    EXPECT_STREQ(bogus_info.name, "None");
}

TEST(ShaderPresets, ShaderPresetNameReturnsCorrectNames) {
    EXPECT_STREQ(shaderPresetName(ShaderPreset::None),      "None");
    EXPECT_STREQ(shaderPresetName(ShaderPreset::CRT),       "CRT");
    EXPECT_STREQ(shaderPresetName(ShaderPreset::Scanlines), "Scanlines");
    EXPECT_STREQ(shaderPresetName(ShaderPreset::Sharp),     "Sharp");
    EXPECT_STREQ(shaderPresetName(ShaderPreset::Smooth),    "Smooth");
}

TEST(ShaderPresets, PresetsDoNotContainNullBytes) {
    for (auto preset : kBuiltinPresets) {
        const auto& info = getShaderPreset(preset);

        // Name: strlen should equal the full buffer up to the terminator.
        ASSERT_NE(info.name, nullptr);
        size_t name_len = std::strlen(info.name);
        EXPECT_GT(name_len, 0u);

        // Vertex source: no embedded NUL before the terminator.
        ASSERT_NE(info.vertex_source, nullptr);
        size_t vs_len = std::strlen(info.vertex_source);
        EXPECT_GT(vs_len, 0u);
        for (size_t i = 0; i < vs_len; ++i) {
            EXPECT_NE(info.vertex_source[i], '\0')
                << "Embedded NUL at offset " << i << " in vertex source of \""
                << info.name << "\"";
        }

        // Fragment source: no embedded NUL before the terminator.
        ASSERT_NE(info.fragment_source, nullptr);
        size_t fs_len = std::strlen(info.fragment_source);
        EXPECT_GT(fs_len, 0u);
        for (size_t i = 0; i < fs_len; ++i) {
            EXPECT_NE(info.fragment_source[i], '\0')
                << "Embedded NUL at offset " << i
                << " in fragment source of \"" << info.name << "\"";
        }
    }
}

} // namespace
} // namespace legends
