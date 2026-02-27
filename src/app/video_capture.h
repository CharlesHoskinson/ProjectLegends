// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// VideoCapture — AVI recording with ZMBV video and PCM audio.
// REQ-CAPTURE-003: Video capture (AVI/ZMBV)

#pragma once

#include <legends/gsl.hpp>
#include "app/zmbv_codec.h"

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <string>
#include <vector>

namespace legends {

/// @brief AVI video capture manager with ZMBV video codec and PCM audio.
///
/// Records emulator output to AVI files using:
/// - Video: ZMBV codec (DOSBox-standard lossless compression)
/// - Audio: PCM signed 16-bit little-endian stereo at 44100 Hz
///
/// Usage: startCapture() → addVideoFrame()/addAudioSamples() → stopCapture()
///
/// @requirement REQ-CAPTURE-003
class VideoCapture {
public:
    VideoCapture() = default;
    ~VideoCapture();

    // Non-copyable
    VideoCapture(const VideoCapture&) = delete;
    VideoCapture& operator=(const VideoCapture&) = delete;

    /// @brief Start recording to an AVI file.
    /// @param path Output file path
    /// @param width Video width in pixels
    /// @param height Video height in pixels
    /// @param fps Frames per second
    /// @return true on success, false if already recording or init fails
    /// @pre path is not empty (gsl_Expects)
    bool startCapture(const std::string& path, uint16_t width, uint16_t height,
                      uint32_t fps);

    /// @brief Stop recording and finalize the AVI file.
    ///
    /// Safe to call when not recording (no-op).
    void stopCapture();

    /// @brief Check if currently recording.
    /// @return true if recording is active
    bool isRecording() const { return recording_; }

    /// @brief Add a video frame to the recording.
    /// @param rgb RGB24 pixel data (width * height * 3 bytes)
    /// @param width Frame width
    /// @param height Frame height
    /// @return true on success
    /// @pre rgb != nullptr (gsl_Expects)
    bool addVideoFrame(const uint8_t* rgb, uint16_t width, uint16_t height);

    /// @brief Add audio samples to the recording.
    /// @param pcm PCM signed 16-bit samples (interleaved stereo)
    /// @param count Number of samples (not bytes)
    /// @return true on success
    /// @pre pcm != nullptr (gsl_Expects)
    /// @pre count > 0 (gsl_Expects)
    bool addAudioSamples(const int16_t* pcm, size_t count);

    /// @brief Number of video frames written.
    /// @return Frame count
    uint64_t framesWritten() const { return frames_written_; }

private:
    void writeRIFFHeader();
    void writeAVIMainHeader();
    void writeVideoStreamHeader();
    void writeAudioStreamHeader();
    void finalizeIndex();

    void writeU32LE(uint32_t val);
    void writeU16LE(uint16_t val);
    void writeTag(const char tag[4]);

    ZMBVCodec codec_;
    std::FILE* file_ = nullptr;
    bool recording_ = false;

    uint16_t width_ = 0;
    uint16_t height_ = 0;
    uint32_t fps_ = 30;
    uint64_t frames_written_ = 0;
    uint64_t audio_bytes_written_ = 0;

    // AVI chunk bookkeeping
    long riff_size_pos_ = 0;
    long movi_start_pos_ = 0;
    long movi_size_pos_ = 0;

    // Index entries for AVI idx1 chunk
    struct IndexEntry {
        char chunk_id[4];
        uint32_t flags;
        uint32_t offset;
        uint32_t size;
    };
    std::vector<IndexEntry> index_entries_;

    static constexpr uint32_t kKeyframeInterval = 300;  // Keyframe every 300 frames (5s @ 60fps)
    static constexpr uint32_t kAudioSampleRate = 44100;
    static constexpr uint16_t kAudioChannels = 2;
    static constexpr uint16_t kAudioBitsPerSample = 16;
};

} // namespace legends
