// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// ShaderPresets — built-in GLSL shader sources for post-processing presets.

#pragma once

#include "app/shader_renderer.h" // for ShaderPreset enum

#include <cstdint>
#include <string>

namespace legends {

/// Holds the GLSL source strings for a single shader preset.
struct ShaderPresetInfo {
    const char* name;
    const char* vertex_source;
    const char* fragment_source;
};

/// Look up the shader sources for a given preset.
/// Returns the None (passthrough) preset for out-of-range values.
[[nodiscard]] const ShaderPresetInfo& getShaderPreset(ShaderPreset preset);

/// Human-readable name of the given preset.
[[nodiscard]] const char* shaderPresetName(ShaderPreset preset);

/// Number of usable presets (excludes Custom and COUNT).
[[nodiscard]] uint8_t shaderPresetCount();

} // namespace legends
