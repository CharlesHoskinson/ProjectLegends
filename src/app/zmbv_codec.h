// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// ZMBVCodec — RAII C++ wrapper around the DOSBox ZMBV VideoCodec.
// REQ-CAPTURE-003: Video capture with ZMBV compression.

#pragma once

#include <legends/gsl.hpp>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <span>
#include <vector>

// Forward-declare the engine's VideoCodec to avoid exposing its header
class VideoCodec;

namespace legends {

/// @brief RAII wrapper around the DOSBox ZMBV video codec.
///
/// Provides compress/decompress operations for video frames using the
/// ZMBV (Zip Motion Block Video) codec, the DOSBox-standard format for
/// lossless screen capture.
///
/// @requirement REQ-CAPTURE-003
class ZMBVCodec {
public:
    ZMBVCodec();
    ~ZMBVCodec();

    // Non-copyable, movable
    ZMBVCodec(const ZMBVCodec&) = delete;
    ZMBVCodec& operator=(const ZMBVCodec&) = delete;
    ZMBVCodec(ZMBVCodec&&) noexcept;
    ZMBVCodec& operator=(ZMBVCodec&&) noexcept;

    /// @brief Initialize the codec for compression.
    /// @param width Frame width in pixels (must be > 0)
    /// @param height Frame height in pixels (must be > 0)
    /// @return true on success, false on failure
    [[nodiscard]] bool initCompress(uint16_t width, uint16_t height);

    /// @brief Initialize the codec for decompression.
    /// @param width Frame width in pixels (must be > 0)
    /// @param height Frame height in pixels (must be > 0)
    /// @return true on success, false on failure
    [[nodiscard]] bool initDecompress(uint16_t width, uint16_t height);

    /// @brief Check if the codec is initialized for compression or decompression.
    /// @return true if initialized
    [[nodiscard]] bool isInitialized() const { return initialized_; }

    /// @brief Encode a single RGB24 frame.
    /// @param pixels RGB24 pixel data (width * height * 3 bytes)
    /// @param width Frame width
    /// @param height Frame height
    /// @param keyframe true to force keyframe, false for delta frame
    /// @return Encoded frame data (empty on failure)
    /// @pre !pixels.empty() (gsl_Expects)
    /// @pre isInitialized() (gsl_Expects)
    [[nodiscard]] std::vector<uint8_t> encodeFrame(std::span<const uint8_t> pixels,
                                      uint16_t width, uint16_t height,
                                      bool keyframe);

    /// @brief Decode a compressed frame into RGB24 output.
    /// @param data Compressed frame data
    /// @param output Output buffer (width * height * 3 bytes)
    /// @return true on success
    /// @pre data != nullptr (gsl_Expects)
    /// @pre output != nullptr (gsl_Expects)
    [[nodiscard]] bool decodeFrame(const uint8_t* data, size_t data_size,
                     uint8_t* output, size_t output_size);
    /// @pre !data.empty() (gsl_Expects)
    /// @pre !output.empty() (gsl_Expects)
    bool decodeFrame(std::span<const uint8_t> data,
                     std::span<uint8_t> output);

private:
    std::unique_ptr<VideoCodec> codec_;
    std::vector<uint8_t> compress_buf_;
    uint16_t width_ = 0;
    uint16_t height_ = 0;
    bool initialized_ = false;
    bool compress_mode_ = false;
};

} // namespace legends
