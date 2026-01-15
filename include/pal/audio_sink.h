// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024 ProjectLegends Contributors
//
// Platform Abstraction Layer - Audio Sink Interface

#pragma once

#include "pal/types.h"
#include <cstdint>

namespace pal {

/// Configuration for audio output
struct AudioConfig {
    uint32_t sample_rate = 44100;  // Samples per second
    uint16_t channels = 2;          // 1 = mono, 2 = stereo
    uint16_t buffer_ms = 50;        // Target latency in milliseconds
};

/// Push-based audio output interface
///
/// Emulation produces samples and pushes them to this sink.
/// The sink drains samples to the audio device.
///
/// This is the push model - emulation timing is authoritative.
/// The audio device does NOT drive emulation timing.
class IAudioSink {
public:
    virtual ~IAudioSink() = default;

    // ═══════════════════════════════════════════════════════════════════════
    // Lifecycle
    // ═══════════════════════════════════════════════════════════════════════

    /// Open audio device with given configuration
    /// @return Success, DeviceNotFound, AlreadyOpen
    virtual Result open(const AudioConfig& config) = 0;

    /// Close audio device (safe to call if not open)
    virtual void close() = 0;

    /// Check if audio device is open
    virtual bool isOpen() const = 0;

    // ═══════════════════════════════════════════════════════════════════════
    // Push Model - Emulation pushes samples
    // ═══════════════════════════════════════════════════════════════════════

    /// Push audio samples to the sink
    ///
    /// @param samples Interleaved 16-bit signed PCM samples
    /// @param frame_count Number of frames (samples per channel)
    /// @return Success, InvalidParameter (null), BufferFull, NotInitialized
    ///
    /// @note This call is non-blocking. If buffer is full, returns BufferFull.
    /// @note Samples are interleaved: L0, R0, L1, R1, ... for stereo
    virtual Result pushSamples(const int16_t* samples, uint32_t frame_count) = 0;

    /// Get number of frames currently queued in buffer
    virtual uint32_t getQueuedFrames() const = 0;

    /// Get total buffer capacity in frames
    virtual uint32_t getBufferCapacity() const = 0;

    // ═══════════════════════════════════════════════════════════════════════
    // Playback Control
    // ═══════════════════════════════════════════════════════════════════════

    /// Pause or resume audio playback
    /// @param pause True to pause, false to resume
    /// @return Success, NotInitialized
    virtual Result pause(bool pause) = 0;

    /// Check if playback is paused
    virtual bool isPaused() const = 0;

    /// Set output volume
    /// @param volume 0.0 (mute) to 1.0 (full volume), values outside clamped
    /// @return Success
    virtual Result setVolume(float volume) = 0;

    /// Get current volume
    virtual float getVolume() const = 0;

    // ═══════════════════════════════════════════════════════════════════════
    // Configuration Query
    // ═══════════════════════════════════════════════════════════════════════

    /// Get the active audio configuration
    virtual AudioConfig getConfig() const = 0;
};

} // namespace pal
