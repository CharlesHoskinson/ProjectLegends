// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// ZMBVCodec — RAII wrapper around engine's ZMBV VideoCodec.
// REQ-CAPTURE-003: Video capture with ZMBV compression.

#include "app/zmbv_codec.h"
#include "zmbv/zmbv.h"

#include <cstring>

namespace legends {

// ─────────────────────────────────────────────────────────────────────────────
// Lifecycle
// ─────────────────────────────────────────────────────────────────────────────

ZMBVCodec::ZMBVCodec() : codec_(std::make_unique<VideoCodec>()) {}

ZMBVCodec::~ZMBVCodec() = default;

ZMBVCodec::ZMBVCodec(ZMBVCodec&&) noexcept = default;
ZMBVCodec& ZMBVCodec::operator=(ZMBVCodec&&) noexcept = default;

// ─────────────────────────────────────────────────────────────────────────────
// Initialization
// ─────────────────────────────────────────────────────────────────────────────

bool ZMBVCodec::initCompress(uint16_t width, uint16_t height) {
    if (width == 0 || height == 0) return false;

    if (!codec_->SetupCompress(width, height)) return false;

    int needed = codec_->NeededSize(width, height, ZMBV_FORMAT_24BPP);
    compress_buf_.resize(static_cast<size_t>(needed));

    width_ = width;
    height_ = height;
    initialized_ = true;
    compress_mode_ = true;
    return true;
}

bool ZMBVCodec::initDecompress(uint16_t width, uint16_t height) {
    if (width == 0 || height == 0) return false;

    if (!codec_->SetupDecompress(width, height)) return false;

    width_ = width;
    height_ = height;
    initialized_ = true;
    compress_mode_ = false;
    return true;
}

// ─────────────────────────────────────────────────────────────────────────────
// Compression
// ─────────────────────────────────────────────────────────────────────────────

std::vector<uint8_t> ZMBVCodec::encodeFrame(std::span<const uint8_t> pixels,
                                              uint16_t width, uint16_t height,
                                              bool keyframe) {
    gsl_Expects(!pixels.empty());
    gsl_Expects(initialized_ && compress_mode_);

    int flags = keyframe ? 1 : 0;

    if (!codec_->PrepareCompressFrame(flags, ZMBV_FORMAT_24BPP, nullptr,
                                       compress_buf_.data(),
                                       static_cast<int>(compress_buf_.size()))) {
        return {};
    }

    // Feed lines top-to-bottom
    size_t pitch = static_cast<size_t>(width) * 3;
    for (uint16_t y = 0; y < height; ++y) {
        void* line = const_cast<uint8_t*>(pixels.data() + y * pitch);
        codec_->CompressLines(1, &line);
    }

    int written = codec_->FinishCompressFrame();
    if (written <= 0) return {};

    return {compress_buf_.data(), compress_buf_.data() + written};
}

// ─────────────────────────────────────────────────────────────────────────────
// Decompression
// ─────────────────────────────────────────────────────────────────────────────

bool ZMBVCodec::decodeFrame(std::span<const uint8_t> data,
                             std::span<uint8_t> output) {
    gsl_Expects(!data.empty());
    gsl_Expects(!output.empty());
    gsl_Expects(initialized_ && !compress_mode_);

    if (!codec_->DecompressFrame(const_cast<uint8_t*>(data.data()),
                                  static_cast<int>(data.size()))) {
        return false;
    }

    // Extract 24-bit RGB output
    size_t expected = static_cast<size_t>(width_) * height_ * 3;
    if (output.size() < expected) return false;

    codec_->Output_UpsideDown_24(output.data());
    return true;
}

} // namespace legends
