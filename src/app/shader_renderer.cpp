// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// ShaderRenderer — implementation of the OpenGL post-processing pipeline.
// Sets up a fullscreen quad, uploads RGB frames as textures, and renders
// them through the active GLSL shader program.

#include "app/shader_renderer.h"
#include "app/shader_presets.h"

#include <glad/glad.h>

#include <cstring>
#include <filesystem>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>

namespace legends {

// ---------------------------------------------------------------------------
// Fullscreen quad geometry (two triangles, CCW winding).
// Each vertex: { x, y, u, v }.
// ---------------------------------------------------------------------------
// clang-format off
static constexpr float kQuadVertices[] = {
    // position    texcoord
    -1.0f, -1.0f,  0.0f, 0.0f,
     1.0f, -1.0f,  1.0f, 0.0f,
     1.0f,  1.0f,  1.0f, 1.0f,

    -1.0f, -1.0f,  0.0f, 0.0f,
     1.0f,  1.0f,  1.0f, 1.0f,
    -1.0f,  1.0f,  0.0f, 1.0f,
};
// clang-format on

// ---------------------------------------------------------------------------
// Construction / destruction
// ---------------------------------------------------------------------------

ShaderRenderer::ShaderRenderer() = default;

ShaderRenderer::~ShaderRenderer() {
    destroy();
}

// ---------------------------------------------------------------------------
// Initialisation
// ---------------------------------------------------------------------------

bool ShaderRenderer::init(uint16_t width, uint16_t height) {
    if (initialized_) {
        return true;
    }

    setupFullscreenQuad();
    setupFramebuffer(width, height);

    // Start with the passthrough (None) shader.
    if (!loadPreset(ShaderPreset::None)) {
        destroy();
        return false;
    }

    initialized_ = true;
    return true;
}

void ShaderRenderer::destroy() {
    if (shader_program_) {
        glDeleteProgram(shader_program_);
        shader_program_ = 0;
    }
    if (vbo_) {
        glDeleteBuffers(1, &vbo_);
        vbo_ = 0;
    }
    if (vao_) {
        glDeleteVertexArrays(1, &vao_);
        vao_ = 0;
    }
    if (texture_) {
        glDeleteTextures(1, &texture_);
        texture_ = 0;
    }
    if (fbo_) {
        glDeleteFramebuffers(1, &fbo_);
        fbo_ = 0;
    }

    initialized_ = false;
}

// ---------------------------------------------------------------------------
// Preset management
// ---------------------------------------------------------------------------

bool ShaderRenderer::loadPreset(ShaderPreset preset) {
    const auto& info = getShaderPreset(preset);
    if (!compileShader(info.vertex_source, info.fragment_source)) {
        return false;
    }
    current_preset_ = preset;
    current_name_ = info.name;
    return true;
}

bool ShaderRenderer::loadCustomShader(const std::string& glsl_path) {
    static constexpr std::uintmax_t kMaxShaderBytes = 65536; // 64 KB (REQ-SEC-038)

    std::error_code ec;
    auto file_size = std::filesystem::file_size(glsl_path, ec);
    if (ec || file_size > kMaxShaderBytes) {
        return false;
    }

    std::ifstream file(glsl_path);
    if (!file.is_open()) {
        return false;
    }

    std::stringstream buf;
    buf << file.rdbuf();
    std::string fragment_src = buf.str();

    // Custom shaders reuse the shared passthrough vertex shader.
    const auto& none_info = getShaderPreset(ShaderPreset::None);
    if (!compileShader(none_info.vertex_source, fragment_src)) {
        return false;
    }

    current_preset_ = ShaderPreset::Custom;
    current_name_ = glsl_path;
    return true;
}

void ShaderRenderer::nextPreset() {
    // Cycle through built-in presets: None..Smooth (indices 0..4).
    auto idx = static_cast<uint8_t>(current_preset_);
    uint8_t count = shaderPresetCount();
    idx = static_cast<uint8_t>((idx + 1) % count);
    loadPreset(static_cast<ShaderPreset>(idx));
}

void ShaderRenderer::prevPreset() {
    auto idx = static_cast<uint8_t>(current_preset_);
    uint8_t count = shaderPresetCount();
    idx = static_cast<uint8_t>((idx + count - 1) % count);
    loadPreset(static_cast<ShaderPreset>(idx));
}

// ---------------------------------------------------------------------------
// Rendering
// ---------------------------------------------------------------------------

// Render pipeline: upload RGB frame as texture → bind shader + set uniforms
// → draw fullscreen quad to default framebuffer (screen).
void ShaderRenderer::render(const uint8_t* rgb_data,
                            uint16_t width, uint16_t height) {
    if (!initialized_ || !rgb_data) {
        return;
    }

    // If shaders are disabled, fall back to a plain passthrough blit.
    if (!shaders_enabled_ &&
        current_preset_ != ShaderPreset::None) {
        loadPreset(ShaderPreset::None);
    }

    // Upload the frame as a GL_RGB texture.
    glActiveTexture(GL_TEXTURE0);
    glBindTexture(GL_TEXTURE_2D, texture_);
    glTexImage2D(GL_TEXTURE_2D, 0, GL_RGB,
                 static_cast<GLsizei>(width),
                 static_cast<GLsizei>(height),
                 0, GL_RGB, GL_UNSIGNED_BYTE, rgb_data);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);

    // Bind the shader and set uniforms.
    glUseProgram(shader_program_);

    GLint tex_loc = glGetUniformLocation(shader_program_, "screenTexture");
    if (tex_loc >= 0) {
        glUniform1i(tex_loc, 0);
    }

    GLint res_loc = glGetUniformLocation(shader_program_, "resolution");
    if (res_loc >= 0) {
        glUniform2f(res_loc,
                    static_cast<GLfloat>(width),
                    static_cast<GLfloat>(height));
    }

    // Draw the fullscreen quad.
    glBindFramebuffer(GL_FRAMEBUFFER, 0);
    glViewport(0, 0,
               static_cast<GLsizei>(fb_width_),
               static_cast<GLsizei>(fb_height_));
    glClearColor(0.0f, 0.0f, 0.0f, 1.0f);
    glClear(GL_COLOR_BUFFER_BIT);

    glBindVertexArray(vao_);
    glDrawArrays(GL_TRIANGLES, 0, 6);
    glBindVertexArray(0);

    glUseProgram(0);
}

// ---------------------------------------------------------------------------
// Private helpers
// ---------------------------------------------------------------------------

bool ShaderRenderer::compileShader(const std::string& vertex_src,
                                   const std::string& fragment_src) {
    // -- Vertex shader -------------------------------------------------------
    GLuint vert = glCreateShader(GL_VERTEX_SHADER);
    const char* v_src = vertex_src.c_str();
    glShaderSource(vert, 1, &v_src, nullptr);
    glCompileShader(vert);

    GLint success = GL_FALSE;
    glGetShaderiv(vert, GL_COMPILE_STATUS, &success);
    if (success != GL_TRUE) {
        GLint log_len = 0;
        glGetShaderiv(vert, GL_INFO_LOG_LENGTH, &log_len);
        if (log_len > 0) {
            std::vector<GLchar> log(static_cast<size_t>(log_len));
            glGetShaderInfoLog(vert, log_len, nullptr, log.data());
            // TODO: forward to spdlog once integrated.
        }
        glDeleteShader(vert);
        return false;
    }

    // -- Fragment shader -----------------------------------------------------
    GLuint frag = glCreateShader(GL_FRAGMENT_SHADER);
    const char* f_src = fragment_src.c_str();
    glShaderSource(frag, 1, &f_src, nullptr);
    glCompileShader(frag);

    success = GL_FALSE;
    glGetShaderiv(frag, GL_COMPILE_STATUS, &success);
    if (success != GL_TRUE) {
        GLint log_len = 0;
        glGetShaderiv(frag, GL_INFO_LOG_LENGTH, &log_len);
        if (log_len > 0) {
            std::vector<GLchar> log(static_cast<size_t>(log_len));
            glGetShaderInfoLog(frag, log_len, nullptr, log.data());
        }
        glDeleteShader(vert);
        glDeleteShader(frag);
        return false;
    }

    // -- Link program --------------------------------------------------------
    GLuint program = glCreateProgram();
    glAttachShader(program, vert);
    glAttachShader(program, frag);
    glLinkProgram(program);

    success = GL_FALSE;
    glGetProgramiv(program, GL_LINK_STATUS, &success);
    if (success != GL_TRUE) {
        GLint log_len = 0;
        glGetProgramiv(program, GL_INFO_LOG_LENGTH, &log_len);
        if (log_len > 0) {
            std::vector<GLchar> log(static_cast<size_t>(log_len));
            glGetProgramInfoLog(program, log_len, nullptr, log.data());
        }
        glDeleteShader(vert);
        glDeleteShader(frag);
        glDeleteProgram(program);
        return false;
    }

    // Shaders are linked; intermediates can be freed.
    glDeleteShader(vert);
    glDeleteShader(frag);

    // Replace the previous program.
    if (shader_program_) {
        glDeleteProgram(shader_program_);
    }
    shader_program_ = program;
    return true;
}

// GL pipeline stage 1: Create VAO + VBO for the fullscreen quad geometry.
// Two triangles cover NDC [-1,1] with UV [0,1] for the post-processing pass.
void ShaderRenderer::setupFullscreenQuad() {
    glGenVertexArrays(1, &vao_);
    glBindVertexArray(vao_);

    glGenBuffers(1, &vbo_);
    glBindBuffer(GL_ARRAY_BUFFER, vbo_);
    glBufferData(GL_ARRAY_BUFFER,
                 static_cast<GLsizeiptr>(sizeof(kQuadVertices)),
                 kQuadVertices, GL_STATIC_DRAW);

    // Attribute 0: position (vec2)
    glVertexAttribPointer(0, 2, GL_FLOAT, GL_FALSE,
                          4 * static_cast<GLsizei>(sizeof(float)),
                          static_cast<const void*>(nullptr));
    glEnableVertexAttribArray(0);

    // Attribute 1: texcoord (vec2)
    glVertexAttribPointer(1, 2, GL_FLOAT, GL_FALSE,
                          4 * static_cast<GLsizei>(sizeof(float)),
                          reinterpret_cast<const void*>(
                              2 * sizeof(float)));
    glEnableVertexAttribArray(1);

    glBindVertexArray(0);
}

// GL pipeline stage 2: Create FBO + texture for frame upload.
// The texture receives RGB24 data each frame; the FBO is used for readback.
void ShaderRenderer::setupFramebuffer(uint16_t width, uint16_t height) {
    fb_width_ = width;
    fb_height_ = height;

    // Create the texture that will receive uploaded frames.
    glGenTextures(1, &texture_);
    glBindTexture(GL_TEXTURE_2D, texture_);
    glTexImage2D(GL_TEXTURE_2D, 0, GL_RGB,
                 static_cast<GLsizei>(width),
                 static_cast<GLsizei>(height),
                 0, GL_RGB, GL_UNSIGNED_BYTE, nullptr);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);

    // Create FBO and attach the texture.
    glGenFramebuffers(1, &fbo_);
    glBindFramebuffer(GL_FRAMEBUFFER, fbo_);
    glFramebufferTexture2D(GL_FRAMEBUFFER, GL_COLOR_ATTACHMENT0,
                           GL_TEXTURE_2D, texture_, 0);

    // Verify completeness (best-effort; stub always succeeds).
    glCheckFramebufferStatus(GL_FRAMEBUFFER);

    glBindFramebuffer(GL_FRAMEBUFFER, 0);
}

} // namespace legends
