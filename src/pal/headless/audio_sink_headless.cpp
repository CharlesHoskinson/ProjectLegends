// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// Platform Abstraction Layer - Headless Audio Sink Implementation

#include "pal/audio_sink.h"
#include <algorithm>
#include <cstring>
#include <memory>
#include <vector>

namespace pal {
namespace headless {

/// Headless audio sink - accepts samples into memory buffer
class AudioSinkHeadless : public IAudioSink {
public:
    AudioSinkHeadless() = default;
    ~AudioSinkHeadless() override { close(); }

    // ═══════════════════════════════════════════════════════════════════════
    // Lifecycle
    // ═══════════════════════════════════════════════════════════════════════

    Result open(const AudioConfig& config) override {
        if (open_) {
            return Result::AlreadyOpen;
        }

        config_ = config;

        // Calculate buffer capacity: buffer_ms worth of frames
        // frame = channels samples
        capacity_frames_ = (config.sample_rate * config.buffer_ms) / 1000;

        // Allocate buffer for samples
        try {
            buffer_.resize(static_cast<size_t>(capacity_frames_) * config.channels);
        } catch (...) {
            return Result::OutOfMemory;
        }

        queued_frames_ = 0;
        write_pos_ = 0;
        paused_ = false;
        open_ = true;

        return Result::Success;
    }

    void close() override {
        buffer_.clear();
        buffer_.shrink_to_fit();
        capacity_frames_ = 0;
        queued_frames_ = 0;
        write_pos_ = 0;
        paused_ = false;
        open_ = false;
    }

    bool isOpen() const override {
        return open_;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Push Model
    // ═══════════════════════════════════════════════════════════════════════

    Result pushSamples(const int16_t* samples, uint32_t frame_count) override {
        if (!open_) {
            return Result::NotInitialized;
        }
        if (samples == nullptr && frame_count > 0) {
            return Result::InvalidParameter;
        }
        if (frame_count == 0) {
            return Result::Success;
        }

        // Check if buffer has space
        uint32_t available = capacity_frames_ - queued_frames_;
        if (frame_count > available) {
            return Result::BufferFull;
        }

        // Copy samples to buffer
        uint32_t samples_to_copy = frame_count * config_.channels;
        size_t buffer_size = buffer_.size();

        for (uint32_t i = 0; i < samples_to_copy; ++i) {
            buffer_[(write_pos_ + i) % buffer_size] = samples[i];
        }

        write_pos_ = (write_pos_ + samples_to_copy) % buffer_size;
        queued_frames_ += frame_count;
        total_frames_pushed_ += frame_count;

        return Result::Success;
    }

    uint32_t getQueuedFrames() const override {
        return queued_frames_;
    }

    uint32_t getBufferCapacity() const override {
        return capacity_frames_;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Playback Control
    // ═══════════════════════════════════════════════════════════════════════

    Result pause(bool pause) override {
        if (!open_) {
            return Result::NotInitialized;
        }
        paused_ = pause;
        return Result::Success;
    }

    bool isPaused() const override {
        return paused_;
    }

    Result setVolume(float volume) override {
        volume_ = std::clamp(volume, 0.0f, 1.0f);
        return Result::Success;
    }

    float getVolume() const override {
        return volume_;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Configuration Query
    // ═══════════════════════════════════════════════════════════════════════

    AudioConfig getConfig() const override {
        return config_;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Test API
    // ═══════════════════════════════════════════════════════════════════════

    /// Drain frames from buffer (simulates playback)
    void drainFrames(uint32_t count) {
        count = std::min(count, queued_frames_);
        queued_frames_ -= count;
    }

    /// Clear all queued samples
    void clearBuffer() {
        queued_frames_ = 0;
        write_pos_ = 0;
    }

    /// Get total frames pushed since open (for testing)
    uint64_t getTotalFramesPushed() const {
        return total_frames_pushed_;
    }

    /// Get raw buffer (for testing)
    const int16_t* getBuffer() const {
        return buffer_.data();
    }

private:
    bool open_ = false;
    bool paused_ = false;
    float volume_ = 1.0f;
    AudioConfig config_{};

    std::vector<int16_t> buffer_;
    uint32_t capacity_frames_ = 0;
    uint32_t queued_frames_ = 0;
    size_t write_pos_ = 0;
    uint64_t total_frames_pushed_ = 0;
};

} // namespace headless

// Factory function (called by platform_headless.cpp)
std::unique_ptr<IAudioSink> createAudioSinkHeadless() {
    return std::make_unique<headless::AudioSinkHeadless>();
}

} // namespace pal
