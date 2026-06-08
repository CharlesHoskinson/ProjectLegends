// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Screenshot capture implementation.

#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-function"
#elif defined(__GNUC__)
#pragma GCC diagnostic ignored "-Wunused-function"
#elif defined(_MSC_VER)
#pragma warning(disable: 4505)
#endif

#define STB_IMAGE_WRITE_IMPLEMENTATION
#include "stb/stb_image_write.h"

#include "app/capture.h"
#include "app/platform_dirs.h"

#include <legends/gsl.hpp>

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
    if (rgb_data == nullptr || width == 0 || height == 0 || path.empty()) {
        return false;
    }

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
