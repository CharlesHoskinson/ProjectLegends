// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// Platform Abstraction Layer - SDL2 Audio Sink Implementation

#include "pal/audio_sink.h"
#include <SDL.h>
#include <algorithm>
#include <atomic>
#include <cstring>
#include <memory>
#include <vector>

namespace pal {
namespace sdl2 {

/// Lock-free ring buffer for audio samples
class AudioRingBuffer {
public:
    explicit AudioRingBuffer(size_t capacity_samples)
        : buffer_(capacity_samples), capacity_(capacity_samples) {}

    /// Push samples into the buffer (producer thread)
    /// @return Number of samples actually pushed
    size_t push(const int16_t* samples, size_t count) {
        size_t write = write_pos_.load(std::memory_order_relaxed);
        size_t read = read_pos_.load(std::memory_order_acquire);

        size_t available = capacity_ - (write - read);
        size_t to_write = std::min(count, available);

        if (to_write == 0) {
            return 0;
        }

        size_t write_idx = write % capacity_;
        size_t first_chunk = std::min(to_write, capacity_ - write_idx);
        size_t second_chunk = to_write - first_chunk;

        std::memcpy(&buffer_[write_idx], samples, first_chunk * sizeof(int16_t));
        if (second_chunk > 0) {
            std::memcpy(&buffer_[0], samples + first_chunk, second_chunk * sizeof(int16_t));
        }

        write_pos_.store(write + to_write, std::memory_order_release);
        return to_write;
    }

    /// Pull samples from the buffer (consumer thread / audio callback)
    /// @return Number of samples actually pulled
    size_t pull(int16_t* dest, size_t count) {
        size_t read = read_pos_.load(std::memory_order_relaxed);
        size_t write = write_pos_.load(std::memory_order_acquire);

        size_t available = write - read;
        size_t to_read = std::min(count, available);

        if (to_read == 0) {
            return 0;
        }

        size_t read_idx = read % capacity_;
        size_t first_chunk = std::min(to_read, capacity_ - read_idx);
        size_t second_chunk = to_read - first_chunk;

        std::memcpy(dest, &buffer_[read_idx], first_chunk * sizeof(int16_t));
        if (second_chunk > 0) {
            std::memcpy(dest + first_chunk, &buffer_[0], second_chunk * sizeof(int16_t));
        }

        read_pos_.store(read + to_read, std::memory_order_release);
        return to_read;
    }

    size_t available() const {
        size_t write = write_pos_.load(std::memory_order_acquire);
        size_t read = read_pos_.load(std::memory_order_relaxed);
        return write - read;
    }

    size_t free_space() const {
        return capacity_ - available();
    }

    void clear() {
        read_pos_.store(0, std::memory_order_relaxed);
        write_pos_.store(0, std::memory_order_relaxed);
    }

private:
    std::vector<int16_t> buffer_;
    size_t capacity_;
    std::atomic<size_t> read_pos_{0};
    std::atomic<size_t> write_pos_{0};
};

/// SDL2 audio sink using push model with ring buffer
class AudioSinkSDL2 : public IAudioSink {
public:
    AudioSinkSDL2() = default;
    ~AudioSinkSDL2() override { close(); }

    // ═══════════════════════════════════════════════════════════════════════
    // Lifecycle
    // ═══════════════════════════════════════════════════════════════════════

    Result open(const AudioConfig& config) override {
        if (device_id_ != 0) {
            return Result::AlreadyOpen;
        }

        config_ = config;

        // Calculate buffer size in samples
        // buffer_ms worth of samples * channels
        uint32_t buffer_samples = (config.sample_rate * config.buffer_ms / 1000) * config.channels;
        // Use 4x buffer for ring buffer to handle timing variations
        ring_buffer_ = std::make_unique<AudioRingBuffer>(buffer_samples * 4);

        // Set up SDL audio spec
        SDL_AudioSpec desired{};
        desired.freq = static_cast<int>(config.sample_rate);
        desired.format = AUDIO_S16SYS;
        desired.channels = static_cast<Uint8>(config.channels);
        desired.samples = static_cast<Uint16>(buffer_samples / config.channels);
        desired.callback = audioCallback;
        desired.userdata = this;

        SDL_AudioSpec obtained{};
        device_id_ = SDL_OpenAudioDevice(nullptr, 0, &desired, &obtained, 0);

        if (device_id_ == 0) {
            ring_buffer_.reset();
            return Result::DeviceNotFound;
        }

        // Update config with actual values
        config_.sample_rate = static_cast<uint32_t>(obtained.freq);
        config_.channels = obtained.channels;

        // Calculate capacity in frames
        capacity_frames_ = (config_.sample_rate * config_.buffer_ms) / 1000;

        // Start playback
        SDL_PauseAudioDevice(device_id_, 0);
        paused_ = false;

        return Result::Success;
    }

    void close() override {
        if (device_id_ != 0) {
            SDL_CloseAudioDevice(device_id_);
            device_id_ = 0;
        }
        ring_buffer_.reset();
        paused_ = false;
    }

    bool isOpen() const override {
        return device_id_ != 0;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Push Model
    // ═══════════════════════════════════════════════════════════════════════

    Result pushSamples(const int16_t* samples, uint32_t frame_count) override {
        if (device_id_ == 0) {
            return Result::NotInitialized;
        }
        if (samples == nullptr && frame_count > 0) {
            return Result::InvalidParameter;
        }
        if (frame_count == 0) {
            return Result::Success;
        }

        size_t sample_count = static_cast<size_t>(frame_count) * config_.channels;
        size_t pushed = ring_buffer_->push(samples, sample_count);

        if (pushed < sample_count) {
            return Result::BufferFull;
        }

        return Result::Success;
    }

    uint32_t getQueuedFrames() const override {
        if (!ring_buffer_) {
            return 0;
        }
        return static_cast<uint32_t>(ring_buffer_->available() / config_.channels);
    }

    uint32_t getBufferCapacity() const override {
        return capacity_frames_;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Playback Control
    // ═══════════════════════════════════════════════════════════════════════

    Result pause(bool pause) override {
        if (device_id_ == 0) {
            return Result::NotInitialized;
        }

        SDL_PauseAudioDevice(device_id_, pause ? 1 : 0);
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

private:
    static void SDLCALL audioCallback(void* userdata, Uint8* stream, int len) {
        auto* sink = static_cast<AudioSinkSDL2*>(userdata);
        size_t sample_count = static_cast<size_t>(len) / sizeof(int16_t);

        int16_t* output = reinterpret_cast<int16_t*>(stream);
        size_t got = sink->ring_buffer_->pull(output, sample_count);

        // Apply volume
        if (sink->volume_ < 1.0f) {
            for (size_t i = 0; i < got; ++i) {
                output[i] = static_cast<int16_t>(output[i] * sink->volume_);
            }
        }

        // Silence for underrun
        if (got < sample_count) {
            std::memset(output + got, 0, (sample_count - got) * sizeof(int16_t));
        }
    }

    SDL_AudioDeviceID device_id_ = 0;
    std::unique_ptr<AudioRingBuffer> ring_buffer_;
    AudioConfig config_{};
    uint32_t capacity_frames_ = 0;
    bool paused_ = false;
    float volume_ = 1.0f;
};

} // namespace sdl2

// Factory function
std::unique_ptr<IAudioSink> createAudioSinkSDL2() {
    return std::make_unique<sdl2::AudioSinkSDL2>();
}

} // namespace pal
