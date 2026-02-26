// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// ShaderPresets — embedded GLSL sources for every built-in post-processing
// preset.  Each entry carries a shared passthrough vertex shader and a
// unique fragment shader that implements the visual effect.

#include "app/shader_presets.h"

#include <cstdint>

namespace legends {

// ---------------------------------------------------------------------------
// Shared passthrough vertex shader
// ---------------------------------------------------------------------------
static constexpr const char* kPassthroughVertex = R"glsl(
#version 330 core
layout (location = 0) in vec2 aPos;
layout (location = 1) in vec2 aTexCoord;

out vec2 TexCoord;

void main() {
    gl_Position = vec4(aPos, 0.0, 1.0);
    TexCoord = aTexCoord;
}
)glsl";

// ---------------------------------------------------------------------------
// Fragment shaders
// ---------------------------------------------------------------------------

// None — passthrough: sample the texture with no modifications.
static constexpr const char* kNoneFragment = R"glsl(
#version 330 core
in vec2 TexCoord;
out vec4 FragColor;

uniform sampler2D screenTexture;

void main() {
    FragColor = texture(screenTexture, TexCoord);
}
)glsl";

// CRT — barrel distortion + phosphor dot simulation + vignette.
static constexpr const char* kCRTFragment = R"glsl(
#version 330 core
in vec2 TexCoord;
out vec4 FragColor;

uniform sampler2D screenTexture;
uniform vec2 resolution;

vec2 barrelDistortion(vec2 coord) {
    vec2 cc = coord - 0.5;
    float dist = dot(cc, cc);
    return coord + cc * dist * 0.15;
}

void main() {
    vec2 uv = barrelDistortion(TexCoord);

    // Discard pixels outside the barrel-distorted region.
    if (uv.x < 0.0 || uv.x > 1.0 || uv.y < 0.0 || uv.y > 1.0) {
        FragColor = vec4(0.0, 0.0, 0.0, 1.0);
        return;
    }

    vec3 color = texture(screenTexture, uv).rgb;

    // Phosphor-dot simulation: tint sub-pixels per column.
    float px = floor(mod(uv.x * resolution.x, 3.0));
    vec3 mask = vec3(1.0);
    if (px == 0.0)      mask = vec3(1.0, 0.7, 0.7);
    else if (px == 1.0) mask = vec3(0.7, 1.0, 0.7);
    else                 mask = vec3(0.7, 0.7, 1.0);
    color *= mask;

    // Vignette.
    vec2 vig = TexCoord * (1.0 - TexCoord);
    float vigFactor = clamp(pow(vig.x * vig.y * 15.0, 0.25), 0.0, 1.0);
    color *= vigFactor;

    FragColor = vec4(color, 1.0);
}
)glsl";

// Scanlines — horizontal darkening every other line.
static constexpr const char* kScanlinesFragment = R"glsl(
#version 330 core
in vec2 TexCoord;
out vec4 FragColor;

uniform sampler2D screenTexture;
uniform vec2 resolution;

void main() {
    vec3 color = texture(screenTexture, TexCoord).rgb;

    // Darken every other scanline.
    float scanline = sin(TexCoord.y * resolution.y * 3.14159) * 0.5 + 0.5;
    color *= 0.7 + 0.3 * scanline;

    FragColor = vec4(color, 1.0);
}
)glsl";

// Sharp — nearest-neighbour with subtle sharpening (unsharp mask).
static constexpr const char* kSharpFragment = R"glsl(
#version 330 core
in vec2 TexCoord;
out vec4 FragColor;

uniform sampler2D screenTexture;
uniform vec2 resolution;

void main() {
    vec2 texel = 1.0 / resolution;
    vec3 center = texture(screenTexture, TexCoord).rgb;
    vec3 top    = texture(screenTexture, TexCoord + vec2(0.0, -texel.y)).rgb;
    vec3 bottom = texture(screenTexture, TexCoord + vec2(0.0,  texel.y)).rgb;
    vec3 left   = texture(screenTexture, TexCoord + vec2(-texel.x, 0.0)).rgb;
    vec3 right  = texture(screenTexture, TexCoord + vec2( texel.x, 0.0)).rgb;

    // Simple unsharp mask: center + strength * (center - average_neighbours).
    vec3 avg = (top + bottom + left + right) * 0.25;
    float strength = 0.75;
    vec3 sharpened = center + strength * (center - avg);

    FragColor = vec4(clamp(sharpened, 0.0, 1.0), 1.0);
}
)glsl";

// Smooth — bilinear filtering with a slight blur.
static constexpr const char* kSmoothFragment = R"glsl(
#version 330 core
in vec2 TexCoord;
out vec4 FragColor;

uniform sampler2D screenTexture;
uniform vec2 resolution;

void main() {
    vec2 texel = 1.0 / resolution;

    // 3x3 box filter with weighted centre.
    vec3 sum = vec3(0.0);
    sum += texture(screenTexture, TexCoord + vec2(-texel.x, -texel.y)).rgb;
    sum += texture(screenTexture, TexCoord + vec2(     0.0, -texel.y)).rgb;
    sum += texture(screenTexture, TexCoord + vec2( texel.x, -texel.y)).rgb;
    sum += texture(screenTexture, TexCoord + vec2(-texel.x,      0.0)).rgb;
    sum += texture(screenTexture, TexCoord).rgb * 4.0;
    sum += texture(screenTexture, TexCoord + vec2( texel.x,      0.0)).rgb;
    sum += texture(screenTexture, TexCoord + vec2(-texel.x,  texel.y)).rgb;
    sum += texture(screenTexture, TexCoord + vec2(     0.0,  texel.y)).rgb;
    sum += texture(screenTexture, TexCoord + vec2( texel.x,  texel.y)).rgb;

    FragColor = vec4(sum / 12.0, 1.0);
}
)glsl";

// ---------------------------------------------------------------------------
// Preset table — indexed by ShaderPreset enum value.
// Each entry pairs the shared passthrough vertex shader with a unique
// fragment shader implementing the visual effect.
// ---------------------------------------------------------------------------
static const ShaderPresetInfo kPresets[] = {
    /* None      */ { "None",      kPassthroughVertex, kNoneFragment      },
    /* CRT       */ { "CRT",       kPassthroughVertex, kCRTFragment       },
    /* Scanlines */ { "Scanlines", kPassthroughVertex, kScanlinesFragment },
    /* Sharp     */ { "Sharp",     kPassthroughVertex, kSharpFragment     },
    /* Smooth    */ { "Smooth",    kPassthroughVertex, kSmoothFragment    },
};

static constexpr uint8_t kPresetCount =
    static_cast<uint8_t>(sizeof(kPresets) / sizeof(kPresets[0]));

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

const ShaderPresetInfo& getShaderPreset(ShaderPreset preset) {
    auto idx = static_cast<uint8_t>(preset);
    if (idx >= kPresetCount) {
        return kPresets[0]; // fall back to None
    }
    return kPresets[idx];
}

const char* shaderPresetName(ShaderPreset preset) {
    return getShaderPreset(preset).name;
}

uint8_t shaderPresetCount() {
    return kPresetCount;
}

} // namespace legends
