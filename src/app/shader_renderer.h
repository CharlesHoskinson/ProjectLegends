// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// ShaderRenderer — OpenGL shader rendering pipeline for post-processing.
// Manages fullscreen-quad rendering with configurable GLSL shaders for
// CRT emulation, scanlines, sharpening, and smoothing effects.

#pragma once

#include <cstdint>
#include <string>
#include <vector>

namespace legends {

/// Shader post-processing presets available out of the box.
enum class ShaderPreset : uint8_t {
    None = 0,
    CRT,
    Scanlines,
    Sharp,
    Smooth,
    Custom,
    COUNT
};

/// Owns the OpenGL resources for a single-pass post-processing pipeline.
/// Feed it raw RGB frame data and it renders through the active shader.
class ShaderRenderer {
public:
    ShaderRenderer();
    ~ShaderRenderer();

    ShaderRenderer(const ShaderRenderer&) = delete;
    ShaderRenderer& operator=(const ShaderRenderer&) = delete;

    /// Allocate GL resources (VAO, VBO, FBO, default texture).
    /// @param width   Framebuffer width in pixels.
    /// @param height  Framebuffer height in pixels.
    /// @return true on success.
    bool init(uint16_t width, uint16_t height);

    /// Release all GL resources.
    void destroy();

    /// @return true after a successful init() and before destroy().
    bool isInitialized() const { return initialized_; }

    /// Compile and activate a built-in shader preset.
    bool loadPreset(ShaderPreset preset);

    /// Compile and activate a shader loaded from a GLSL file on disk.
    bool loadCustomShader(const std::string& glsl_path);

    /// Upload an RGB frame and render it through the active shader.
    /// @param rgb_data  Pointer to tightly-packed RGB888 pixel data.
    /// @param width     Frame width in pixels.
    /// @param height    Frame height in pixels.
    void render(const uint8_t* rgb_data, uint16_t width, uint16_t height);

    /// @return The currently active preset.
    ShaderPreset currentPreset() const { return current_preset_; }

    /// @return Human-readable name of the active shader.
    const std::string& currentShaderName() const { return current_name_; }

    /// Cycle to the next built-in preset (wraps, skips Custom/COUNT).
    void nextPreset();

    /// Cycle to the previous built-in preset (wraps, skips Custom/COUNT).
    void prevPreset();

    /// @return true if shader post-processing is enabled.
    bool shadersEnabled() const { return shaders_enabled_; }

    /// Enable or disable shader post-processing.
    void setShadersEnabled(bool enabled) { shaders_enabled_ = enabled; }

private:
    bool compileShader(const std::string& vertex_src,
                       const std::string& fragment_src);
    void setupFullscreenQuad();
    void setupFramebuffer(uint16_t width, uint16_t height);

    bool initialized_ = false;
    bool shaders_enabled_ = true;
    ShaderPreset current_preset_ = ShaderPreset::None;
    std::string current_name_ = "None";

    uint32_t shader_program_ = 0;
    uint32_t vao_ = 0;
    uint32_t vbo_ = 0;
    uint32_t fbo_ = 0;
    uint32_t texture_ = 0;
    uint16_t fb_width_ = 0;
    uint16_t fb_height_ = 0;
};

} // namespace legends
