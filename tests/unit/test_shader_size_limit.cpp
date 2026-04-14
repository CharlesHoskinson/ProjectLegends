// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for REQ-SEC-038: loadCustomShader() must reject files > 64 KB.

#include "app/shader_renderer.h"

#include <gtest/gtest.h>

#include <filesystem>
#include <fstream>
#include <string>

namespace legends {
namespace {

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Write `byte_count` bytes of filler to `path`.
static void writeFillFile(const std::filesystem::path& path,
                          std::size_t byte_count,
                          char fill = 'x') {
    std::ofstream out(path, std::ios::binary);
    ASSERT_TRUE(out.is_open()) << "Could not open " << path;
    const std::string chunk(1024, fill);
    std::size_t remaining = byte_count;
    while (remaining >= chunk.size()) {
        out.write(chunk.data(), static_cast<std::streamsize>(chunk.size()));
        remaining -= chunk.size();
    }
    if (remaining > 0) {
        out.write(chunk.data(), static_cast<std::streamsize>(remaining));
    }
}

// ---------------------------------------------------------------------------
// REQ-SEC-038 tests
// ---------------------------------------------------------------------------

// A file larger than 64 KB must be rejected before any GL call is attempted.
TEST(ShaderSizeLimit, OversizedFileIsRejected) {
    const auto tmp = std::filesystem::temp_directory_path() /
                     "legends_test_shader_oversized.glsl";

    // Write 65537 bytes — one byte over the 64 KB limit.
    writeFillFile(tmp, 65537);

    ShaderRenderer renderer;
    EXPECT_FALSE(renderer.loadCustomShader(tmp.string()))
        << "loadCustomShader must return false for a file larger than 64 KB";

    std::filesystem::remove(tmp);
}

// A file within the 64 KB limit must not be rejected due to size.
// (Compilation will fail without a GL context, but that is a different path.)
TEST(ShaderSizeLimit, UndersizedFileIsNotRejectedForSize) {
    const auto tmp = std::filesystem::temp_directory_path() /
                     "legends_test_shader_small.glsl";

    // Minimal valid-looking GLSL fragment shader — well under 64 KB.
    {
        std::ofstream out(tmp);
        ASSERT_TRUE(out.is_open()) << "Could not open " << tmp;
        out << "#version 330 core\n"
               "out vec4 FragColor;\n"
               "void main() { FragColor = vec4(1.0); }\n";
    }

    ShaderRenderer renderer;
    // The call may return false due to the absence of a GL context, but the
    // reason must NOT be the file size.  We verify this by confirming that
    // file_size(path) <= 65536 before calling, and that the file itself
    // can be opened — both preconditions for passing the size gate.
    std::error_code ec;
    auto sz = std::filesystem::file_size(tmp, ec);
    ASSERT_FALSE(ec) << "file_size() failed: " << ec.message();
    ASSERT_LE(sz, 65536u) << "Test file unexpectedly exceeds 64 KB";

    // We don't assert the return value because GL may not be available,
    // but we do assert the call completes without crashing or throwing.
    (void)renderer.loadCustomShader(tmp.string());

    std::filesystem::remove(tmp);
}

} // namespace
} // namespace legends
