// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Screenshot capture — PNG file output using stb_image_write.

#pragma once

#include <cstdint>
#include <string>
#include <string_view>

namespace legends {

/// Get the captures directory: <getDataDir()>/captures
[[nodiscard]] std::string getCaptureDir();

/// Generate a unique capture filename: capture_YYYYMMDD_HHMMSS_NNN.png
[[nodiscard]] std::string generateCaptureFilename();

/// Write an RGB24 buffer to a PNG file.
/// Returns true on success.
[[nodiscard]] bool writeScreenshotPNG(std::string_view path,
                        const uint8_t* rgb_data,
                        uint16_t width, uint16_t height);

} // namespace legends
