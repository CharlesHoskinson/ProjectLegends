// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Unit tests for ZMBVCodec — RAII wrapper around engine VideoCodec.
// REQ-CAPTURE-003: Video capture (ZMBV codec)

#include <gtest/gtest.h>
#include <legends/gsl.hpp>
#include "app/zmbv_codec.h"

#include <cstring>
#include <vector>

namespace legends {
namespace {

// ═══════════════════════════════════════════════════════════════════════════
// Construction & Initialization
// ═══════════════════════════════════════════════════════════════════════════

TEST(ZMBVCodecTest, ConstructDestruct) {
    ZMBVCodec codec;
    EXPECT_FALSE(codec.isInitialized());
}

TEST(ZMBVCodecTest, InitCompress_ValidDimensions) {
    ZMBVCodec codec;
    EXPECT_TRUE(codec.initCompress(640, 480));
    EXPECT_TRUE(codec.isInitialized());
}

TEST(ZMBVCodecTest, InitCompress_SmallDimensions) {
    ZMBVCodec codec;
    EXPECT_TRUE(codec.initCompress(16, 16));
    EXPECT_TRUE(codec.isInitialized());
}

// ═══════════════════════════════════════════════════════════════════════════
// Keyframe Encoding
// ═══════════════════════════════════════════════════════════════════════════

TEST(ZMBVCodecTest, EncodeKeyframe_NonEmpty) {
    ZMBVCodec codec;
    ASSERT_TRUE(codec.initCompress(64, 64));

    // Solid black frame
    std::vector<uint8_t> frame(64 * 64 * 3, 0);
    auto encoded = codec.encodeFrame(frame.data(), 64, 64, true);
    EXPECT_FALSE(encoded.empty()) << "Keyframe should produce output";
}

TEST(ZMBVCodecTest, EncodeDeltaFrame_SameData) {
    ZMBVCodec codec;
    ASSERT_TRUE(codec.initCompress(64, 64));

    std::vector<uint8_t> frame(64 * 64 * 3, 128);

    // First frame is keyframe
    auto keyframe = codec.encodeFrame(frame.data(), 64, 64, true);
    ASSERT_FALSE(keyframe.empty());

    // Delta of identical data should be smaller than keyframe
    auto delta = codec.encodeFrame(frame.data(), 64, 64, false);
    EXPECT_FALSE(delta.empty());
    EXPECT_LE(delta.size(), keyframe.size())
        << "Delta of identical frames should be <= keyframe size";
}

TEST(ZMBVCodecTest, CompressionRatio_SolidColor) {
    ZMBVCodec codec;
    ASSERT_TRUE(codec.initCompress(640, 480));

    // All-black 640x480 should compress very well
    std::vector<uint8_t> frame(640 * 480 * 3, 0);
    auto encoded = codec.encodeFrame(frame.data(), 640, 480, true);
    ASSERT_FALSE(encoded.empty());

    size_t raw_size = 640 * 480 * 3;
    // Solid color should compress to < 5% of raw
    EXPECT_LT(encoded.size(), raw_size / 20)
        << "Solid color should compress to < 5% of raw size";
}

// ═══════════════════════════════════════════════════════════════════════════
// Round-trip: Encode → Decode
// ═══════════════════════════════════════════════════════════════════════════

TEST(ZMBVCodecTest, RoundTrip_IdenticalOutput) {
    ZMBVCodec encoder;
    ZMBVCodec decoder;
    ASSERT_TRUE(encoder.initCompress(64, 64));
    ASSERT_TRUE(decoder.initDecompress(64, 64));

    // Create a pattern
    std::vector<uint8_t> frame(64 * 64 * 3);
    for (size_t i = 0; i < frame.size(); ++i) {
        frame[i] = static_cast<uint8_t>(i & 0xFF);
    }

    auto encoded = encoder.encodeFrame(frame.data(), 64, 64, true);
    ASSERT_FALSE(encoded.empty());

    std::vector<uint8_t> decoded(64 * 64 * 3);
    ASSERT_TRUE(decoder.decodeFrame(encoded.data(), encoded.size(),
                                     decoded.data(), decoded.size()));

    EXPECT_EQ(frame, decoded) << "Round-trip should produce identical output";
}

TEST(ZMBVCodecTest, MinimumDimensions_16x16) {
    ZMBVCodec codec;
    ASSERT_TRUE(codec.initCompress(16, 16));

    std::vector<uint8_t> frame(16 * 16 * 3, 42);
    auto encoded = codec.encodeFrame(frame.data(), 16, 16, true);
    EXPECT_FALSE(encoded.empty());
}

// ═══════════════════════════════════════════════════════════════════════════
// gsl-lite Contract Violations
// ═══════════════════════════════════════════════════════════════════════════

TEST(ZMBVCodecTest, NullPixels_EncodeThrowsFailFast) {
    ZMBVCodec codec;
    ASSERT_TRUE(codec.initCompress(64, 64));
    EXPECT_THROW(codec.encodeFrame(nullptr, 64, 64, true),
                 legends::gsl::fail_fast);
}

TEST(ZMBVCodecTest, EncodeBeforeInit_ThrowsFailFast) {
    ZMBVCodec codec;
    std::vector<uint8_t> frame(64 * 64 * 3, 0);
    EXPECT_THROW(codec.encodeFrame(frame.data(), 64, 64, true),
                 legends::gsl::fail_fast);
}

TEST(ZMBVCodecTest, ZeroDataSize_DecodeThrowsFailFast) {
    ZMBVCodec codec;
    ASSERT_TRUE(codec.initDecompress(64, 64));
    std::vector<uint8_t> output(64 * 64 * 3);
    uint8_t dummy = 0;
    EXPECT_THROW(codec.decodeFrame(&dummy, 0, output.data(), output.size()),
                 legends::gsl::fail_fast);
}

TEST(ZMBVCodecTest, ZeroDimensions_InitReturnsFalse) {
    ZMBVCodec codec;
    EXPECT_FALSE(codec.initCompress(0, 0));
}

} // namespace
} // namespace legends
