// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// Platform Abstraction Layer - SDL3 Audio Sink Implementation
//
// SDL3 uses a push-based audio model with SDL_AudioStream instead of
// the callback-based model from SDL2. This is simpler and more intuitive.

#include "pal/audio_sink.h"
#include <SDL3/SDL.h>
#include <algorithm>
#include <memory>
#include <vector>

namespace pal {
namespace sdl3 {

/// SDL3 audio sink using SDL_AudioStream (push model)
class AudioSinkSDL3 : public IAudioSink {
public:
    AudioSinkSDL3() = default;
    ~AudioSinkSDL3() override { close(); }

    // ═══════════════════════════════════════════════════════════════════════
    // Lifecycle
    // ═══════════════════════════════════════════════════════════════════════

    Result open(const AudioConfig& config) override {
        if (stream_) {
            return Result::AlreadyOpen;
        }

        config_ = config;

        // Set up SDL3 audio spec
        SDL_AudioSpec spec{};
        spec.freq = static_cast<int>(config.sample_rate);
        spec.format = SDL_AUDIO_S16;
        spec.channels = static_cast<int>(config.channels);

        // SDL3: Create audio stream bound to default playback device
        stream_ = SDL_OpenAudioDeviceStream(
            SDL_AUDIO_DEVICE_DEFAULT_PLAYBACK,
            &spec,
            nullptr,  // No callback needed - push model
            nullptr
        );

        if (!stream_) {
            return Result::DeviceNotFound;
        }

        // Calculate capacity in frames based on buffer_ms
        capacity_frames_ = (config_.sample_rate * config_.buffer_ms) / 1000;

        // Start playback
        SDL_ResumeAudioStreamDevice(stream_);
        paused_ = false;

        return Result::Success;
    }

    void close() override {
        if (stream_) {
            SDL_DestroyAudioStream(stream_);
            stream_ = nullptr;
        }
        paused_ = false;
    }

    bool isOpen() const override {
        return stream_ != nullptr;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Push Model
    // ═══════════════════════════════════════════════════════════════════════

    Result pushSamples(const int16_t* samples, uint32_t frame_count) override {
        if (!stream_) {
            return Result::NotInitialized;
        }
        if (samples == nullptr && frame_count > 0) {
            return Result::InvalidParameter;
        }
        if (frame_count == 0) {
            return Result::Success;
        }

        // Apply volume if not 1.0
        if (volume_ < 1.0f) {
            // Create temporary buffer with volume applied
            size_t sample_count = static_cast<size_t>(frame_count) * config_.channels;
            temp_buffer_.resize(sample_count);
            for (size_t i = 0; i < sample_count; ++i) {
                temp_buffer_[i] = static_cast<int16_t>(samples[i] * volume_);
            }
            samples = temp_buffer_.data();
        }

        size_t bytes = static_cast<size_t>(frame_count) * config_.channels * sizeof(int16_t);

        // SDL3: Push directly to audio stream
        if (!SDL_PutAudioStreamData(stream_, samples, static_cast<int>(bytes))) {
            return Result::BufferFull;
        }

        return Result::Success;
    }

    uint32_t getQueuedFrames() const override {
        if (!stream_) {
            return 0;
        }
        int bytes = SDL_GetAudioStreamQueued(stream_);
        return static_cast<uint32_t>(bytes) / (config_.channels * sizeof(int16_t));
    }

    uint32_t getBufferCapacity() const override {
        return capacity_frames_;
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Playback Control
    // ═══════════════════════════════════════════════════════════════════════

    Result pause(bool pause) override {
        if (!stream_) {
            return Result::NotInitialized;
        }

        if (pause) {
            SDL_PauseAudioStreamDevice(stream_);
        } else {
            SDL_ResumeAudioStreamDevice(stream_);
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

private:
    SDL_AudioStream* stream_ = nullptr;
    AudioConfig config_{};
    uint32_t capacity_frames_ = 0;
    bool paused_ = false;
    float volume_ = 1.0f;
    std::vector<int16_t> temp_buffer_;  // For volume adjustment
};

} // namespace sdl3

// Factory function
std::unique_ptr<IAudioSink> createAudioSinkSDL3() {
    return std::make_unique<sdl3::AudioSinkSDL3>();
}

} // namespace pal
