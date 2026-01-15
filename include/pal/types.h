// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// Platform Abstraction Layer - Common Types

#pragma once

#include <cstdint>

namespace pal {

/// Result codes for PAL operations
enum class Result {
    Success = 0,
    NotInitialized,
    AlreadyInitialized,
    InvalidParameter,
    NotSupported,
    DeviceNotFound,
    DeviceLost,
    OutOfMemory,
    BufferFull,
    AlreadyExists,
    AlreadyOpen,
    AlreadyLocked,
    InvalidOperation,
    InvalidState,
    Timeout,
    Unknown = -1
};

/// Pixel formats for software contexts
enum class PixelFormat {
    Unknown = 0,
    RGB565,      // 16-bit: 5-6-5
    RGB888,      // 24-bit: 8-8-8
    RGBA8888,    // 32-bit: 8-8-8-8
    BGRA8888,    // 32-bit: 8-8-8-8 (BGR order)
    Indexed8     // 8-bit indexed with palette
};

/// Convert Result to string for debugging
constexpr const char* toString(Result r) noexcept {
    switch (r) {
        case Result::Success:            return "Success";
        case Result::NotInitialized:     return "NotInitialized";
        case Result::AlreadyInitialized: return "AlreadyInitialized";
        case Result::InvalidParameter:   return "InvalidParameter";
        case Result::NotSupported:       return "NotSupported";
        case Result::DeviceNotFound:     return "DeviceNotFound";
        case Result::DeviceLost:         return "DeviceLost";
        case Result::OutOfMemory:        return "OutOfMemory";
        case Result::BufferFull:         return "BufferFull";
        case Result::AlreadyExists:      return "AlreadyExists";
        case Result::AlreadyOpen:        return "AlreadyOpen";
        case Result::AlreadyLocked:      return "AlreadyLocked";
        case Result::InvalidOperation:   return "InvalidOperation";
        case Result::InvalidState:       return "InvalidState";
        case Result::Timeout:            return "Timeout";
        case Result::Unknown:            return "Unknown";
    }
    return "Unknown";
}

/// Convert PixelFormat to string for debugging
constexpr const char* toString(PixelFormat fmt) noexcept {
    switch (fmt) {
        case PixelFormat::Unknown:  return "Unknown";
        case PixelFormat::RGB565:   return "RGB565";
        case PixelFormat::RGB888:   return "RGB888";
        case PixelFormat::RGBA8888: return "RGBA8888";
        case PixelFormat::BGRA8888: return "BGRA8888";
        case PixelFormat::Indexed8: return "Indexed8";
    }
    return "Unknown";
}

/// Get bytes per pixel for format
constexpr uint32_t bytesPerPixel(PixelFormat fmt) noexcept {
    switch (fmt) {
        case PixelFormat::RGB565:   return 2;
        case PixelFormat::RGB888:   return 3;
        case PixelFormat::RGBA8888: return 4;
        case PixelFormat::BGRA8888: return 4;
        case PixelFormat::Indexed8: return 1;
        default:                    return 0;
    }
}

/// Check if Result indicates success
constexpr bool succeeded(Result r) noexcept {
    return r == Result::Success;
}

/// Check if Result indicates failure
constexpr bool failed(Result r) noexcept {
    return r != Result::Success;
}

} // namespace pal
