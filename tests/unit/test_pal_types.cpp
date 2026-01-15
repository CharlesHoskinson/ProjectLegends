// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors

#include <gtest/gtest.h>
#include "pal/types.h"

namespace pal {
namespace {

// ═══════════════════════════════════════════════════════════════════════════
// Result Tests
// ═══════════════════════════════════════════════════════════════════════════

TEST(PalTypes, ResultSuccessIsZero) {
    EXPECT_EQ(static_cast<int>(Result::Success), 0);
}

TEST(PalTypes, ToStringResult) {
    EXPECT_STREQ(toString(Result::Success), "Success");
    EXPECT_STREQ(toString(Result::NotInitialized), "NotInitialized");
    EXPECT_STREQ(toString(Result::AlreadyInitialized), "AlreadyInitialized");
    EXPECT_STREQ(toString(Result::InvalidParameter), "InvalidParameter");
    EXPECT_STREQ(toString(Result::NotSupported), "NotSupported");
    EXPECT_STREQ(toString(Result::DeviceNotFound), "DeviceNotFound");
    EXPECT_STREQ(toString(Result::DeviceLost), "DeviceLost");
    EXPECT_STREQ(toString(Result::OutOfMemory), "OutOfMemory");
    EXPECT_STREQ(toString(Result::BufferFull), "BufferFull");
    EXPECT_STREQ(toString(Result::AlreadyExists), "AlreadyExists");
    EXPECT_STREQ(toString(Result::AlreadyOpen), "AlreadyOpen");
    EXPECT_STREQ(toString(Result::AlreadyLocked), "AlreadyLocked");
    EXPECT_STREQ(toString(Result::InvalidOperation), "InvalidOperation");
    EXPECT_STREQ(toString(Result::InvalidState), "InvalidState");
    EXPECT_STREQ(toString(Result::Timeout), "Timeout");
    EXPECT_STREQ(toString(Result::Unknown), "Unknown");
}

TEST(PalTypes, SucceededHelper) {
    EXPECT_TRUE(succeeded(Result::Success));
    EXPECT_FALSE(succeeded(Result::NotInitialized));
    EXPECT_FALSE(succeeded(Result::InvalidParameter));
    EXPECT_FALSE(succeeded(Result::Unknown));
}

TEST(PalTypes, FailedHelper) {
    EXPECT_FALSE(failed(Result::Success));
    EXPECT_TRUE(failed(Result::NotInitialized));
    EXPECT_TRUE(failed(Result::InvalidParameter));
    EXPECT_TRUE(failed(Result::Unknown));
}

// ═══════════════════════════════════════════════════════════════════════════
// PixelFormat Tests
// ═══════════════════════════════════════════════════════════════════════════

TEST(PalTypes, ToStringPixelFormat) {
    EXPECT_STREQ(toString(PixelFormat::Unknown), "Unknown");
    EXPECT_STREQ(toString(PixelFormat::RGB565), "RGB565");
    EXPECT_STREQ(toString(PixelFormat::RGB888), "RGB888");
    EXPECT_STREQ(toString(PixelFormat::RGBA8888), "RGBA8888");
    EXPECT_STREQ(toString(PixelFormat::BGRA8888), "BGRA8888");
    EXPECT_STREQ(toString(PixelFormat::Indexed8), "Indexed8");
}

TEST(PalTypes, BytesPerPixelRGB565) {
    EXPECT_EQ(bytesPerPixel(PixelFormat::RGB565), 2u);
}

TEST(PalTypes, BytesPerPixelRGB888) {
    EXPECT_EQ(bytesPerPixel(PixelFormat::RGB888), 3u);
}

TEST(PalTypes, BytesPerPixelRGBA8888) {
    EXPECT_EQ(bytesPerPixel(PixelFormat::RGBA8888), 4u);
}

TEST(PalTypes, BytesPerPixelBGRA8888) {
    EXPECT_EQ(bytesPerPixel(PixelFormat::BGRA8888), 4u);
}

TEST(PalTypes, BytesPerPixelIndexed8) {
    EXPECT_EQ(bytesPerPixel(PixelFormat::Indexed8), 1u);
}

TEST(PalTypes, BytesPerPixelUnknown) {
    EXPECT_EQ(bytesPerPixel(PixelFormat::Unknown), 0u);
}

} // namespace
} // namespace pal
