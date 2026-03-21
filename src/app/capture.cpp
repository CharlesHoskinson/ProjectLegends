// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Screenshot capture implementation.

// stb_image_write generates static helper functions that may not all be
// referenced — suppress the corresponding unused-function warnings.
#if defined(_MSC_VER)
#pragma warning(push)
#pragma warning(disable: 4505)
#elif defined(__GNUC__) || defined(__clang__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-function"
#endif

#define STB_IMAGE_WRITE_IMPLEMENTATION
#include "stb/stb_image_write.h"

#if defined(_MSC_VER)
#pragma warning(pop)
#elif defined(__GNUC__) || defined(__clang__)
#pragma GCC diagnostic pop
#endif

#include "app/capture.h"
#include "app/platform_dirs.h"

#include <gsl-lite/gsl-lite.hpp>

#include <chrono>
#include <cstdio>
#include <filesystem>
#include <iomanip>
#include <sstream>
#include <string>
#include <string_view>

namespace legends {

std::string getCaptureDir() {
    return getDataDir() + "/captures";
}

std::string generateCaptureFilename() {
    auto now = std::chrono::system_clock::now();
    auto time_t_now = std::chrono::system_clock::to_time_t(now);
    auto ms = std::chrono::duration_cast<std::chrono::milliseconds>(
        now.time_since_epoch()) % 1000;

    std::tm tm_buf{};
#if defined(_WIN32)
    localtime_s(&tm_buf, &time_t_now);
#else
    localtime_r(&time_t_now, &tm_buf);
#endif

    std::ostringstream oss;
    oss << "capture_"
        << std::put_time(&tm_buf, "%Y%m%d_%H%M%S")
        << "_" << std::setfill('0') << std::setw(3) << ms.count()
        << ".png";
    return oss.str();
}

bool writeScreenshotPNG(std::string_view path,
                        const uint8_t* rgb_data,
                        uint16_t width, uint16_t height) {
    gsl_Expects(rgb_data != nullptr);
    gsl_Expects(width > 0);
    gsl_Expects(height > 0);

    // stbi_write_png: comp=3 for RGB, stride = width * 3
    std::string path_str(path);
    int result = stbi_write_png(path_str.c_str(),
                                static_cast<int>(width),
                                static_cast<int>(height),
                                3,
                                rgb_data,
                                static_cast<int>(width) * 3);
    return result != 0;
}

} // namespace legends
