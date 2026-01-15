/**
 * @file audio.h
 * @brief Platform-agnostic audio interface for DOSBox library mode.
 *
 * This interface abstracts audio output, allowing DOSBox to run headless
 * or with different audio backends (SDL2, SDL3, custom).
 *
 * ## Design Principles
 * 1. **Producer/Consumer Model**: Core produces samples, backend consumes
 * 2. **Determinism**: Core calls push_samples() during step(), never driven by callback
 * 3. **No SDL Dependencies**: Pure C++ interface
 *
 * ## Critical Thread Safety Rule
 * The backend's audio callback MUST NEVER call back into the emulation.
 * This is essential for determinism and avoiding deadlocks.
 *
 * ## Usage
 * ```cpp
 * // Headless mode (testing, AI agents)
 * auto audio = std::make_unique<NullAudio>();
 * audio->open({44100, 2, 1024});
 * // ... emulation produces samples via push_samples()
 *
 * // SDL mode (normal audio output)
 * auto audio = std::make_unique<SDLAudio>();
 * audio->open({44100, 2, 1024});
 * // ... emulation produces samples
 * // Backend plays samples via SDL audio callback
 * ```
 *
 * @copyright GPL-2.0-or-later
 */

#ifndef DOSBOX_PLATFORM_AUDIO_H
#define DOSBOX_PLATFORM_AUDIO_H

#include <cstdint>
#include <cstddef>
#include <span>

namespace dosbox {
namespace platform {

// ═══════════════════════════════════════════════════════════════════════════════
// Audio Format
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Audio sample format enumeration.
 */
enum class AudioFormat : uint8_t {
    S16 = 0,     ///< Signed 16-bit samples (most common)
    F32 = 1,     ///< 32-bit float samples (-1.0 to 1.0)
};

/**
 * @brief Audio specification for opening the audio device.
 */
struct AudioSpec {
    uint32_t sample_rate = 44100;   ///< Sample rate in Hz (e.g., 44100, 48000)
    uint8_t channels = 2;           ///< Number of channels (1=mono, 2=stereo)
    uint16_t samples = 1024;        ///< Buffer size in samples per channel
    AudioFormat format = AudioFormat::S16;  ///< Sample format

    /**
     * @brief Get bytes per sample (per channel).
     */
    size_t bytes_per_sample() const {
        return format == AudioFormat::S16 ? 2 : 4;
    }

    /**
     * @brief Get total buffer size in bytes.
     */
    size_t buffer_size_bytes() const {
        return static_cast<size_t>(samples) * channels * bytes_per_sample();
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
// Audio Interface
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Abstract audio interface for DOSBox sound output.
 *
 * Implementations:
 * - NullAudio: Discards samples (testing, headless)
 * - BufferAudio: Stores samples in ring buffer (analysis)
 * - SDL2Audio: Uses SDL2 audio subsystem
 * - SDL3Audio: Uses SDL3 audio subsystem
 *
 * ## Producer/Consumer Model
 *
 * ```
 * ┌─────────────────┐         ┌─────────────────┐
 * │   Emulation     │         │   Backend       │
 * │   (Producer)    │ ──────> │   (Consumer)    │
 * │                 │  push   │                 │
 * │  step() calls   │ samples │  callback pulls │
 * │  push_samples() │         │  from buffer    │
 * └─────────────────┘         └─────────────────┘
 * ```
 *
 * The emulation core produces samples at a deterministic rate during step().
 * The backend consumes samples via its own callback (SDL audio callback, etc.).
 * The ring buffer decouples the two for timing flexibility.
 *
 * ## Thread Safety
 * - open(), close(), pause(): Call from main thread only
 * - push_samples(): Call from emulation thread
 * - get_queued_samples(), get_buffer_capacity(): Thread-safe
 */
class IAudio {
public:
    virtual ~IAudio() = default;

    // ─────────────────────────────────────────────────────────────────────────
    // Lifecycle
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Open the audio device with the given specification.
     *
     * @param spec Desired audio format and buffer size
     * @return true if opened successfully
     */
    virtual bool open(const AudioSpec& spec) = 0;

    /**
     * @brief Close the audio device.
     *
     * Safe to call even if not open.
     */
    virtual void close() = 0;

    /**
     * @brief Check if the audio device is open.
     */
    virtual bool is_open() const = 0;

    /**
     * @brief Get the actual audio spec (may differ from requested).
     */
    virtual AudioSpec get_spec() const = 0;

    // ─────────────────────────────────────────────────────────────────────────
    // Sample Production (called by emulation core)
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Push audio samples from the emulator.
     *
     * Called by the mixer during emulation stepping.
     * Samples are interleaved for stereo (L, R, L, R, ...).
     *
     * @param samples Signed 16-bit samples
     * @return Number of samples actually accepted (may be less if buffer full)
     */
    virtual size_t push_samples(std::span<const int16_t> samples) = 0;

    /**
     * @brief Push float audio samples from the emulator.
     *
     * Alternative for float format audio.
     *
     * @param samples Float samples (-1.0 to 1.0)
     * @return Number of samples actually accepted
     */
    virtual size_t push_samples_float(std::span<const float> samples) {
        (void)samples;
        return 0;  // Default: not supported
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Buffer State (for throttling)
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Get the number of samples currently queued.
     *
     * Used by the host to throttle emulation if audio buffer is getting full.
     */
    virtual size_t get_queued_samples() const = 0;

    /**
     * @brief Get the total buffer capacity in samples.
     */
    virtual size_t get_buffer_capacity() const = 0;

    /**
     * @brief Get buffer fill ratio (0.0 = empty, 1.0 = full).
     */
    float get_buffer_fill_ratio() const {
        size_t capacity = get_buffer_capacity();
        if (capacity == 0) return 0.0f;
        return static_cast<float>(get_queued_samples()) / static_cast<float>(capacity);
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Playback Control
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Pause or resume audio playback.
     *
     * When paused, the backend stops consuming samples but the buffer
     * is preserved. Used during save/load or when emulation is paused.
     *
     * @param paused true to pause, false to resume
     */
    virtual void pause(bool paused) = 0;

    /**
     * @brief Check if audio is paused.
     */
    virtual bool is_paused() const = 0;

    /**
     * @brief Clear all queued samples.
     *
     * Called when seeking or resetting emulation state.
     */
    virtual void clear() = 0;
};

// ═══════════════════════════════════════════════════════════════════════════════
// Null Audio (No-op implementation)
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Null audio that discards all samples.
 *
 * Useful for headless mode, benchmarking, or when audio is not needed.
 * Tracks sample count for verification but doesn't store data.
 */
class NullAudio : public IAudio {
public:
    bool open(const AudioSpec& spec) override {
        spec_ = spec;
        is_open_ = true;
        paused_ = false;
        total_samples_ = 0;
        return true;
    }

    void close() override {
        is_open_ = false;
    }

    bool is_open() const override {
        return is_open_;
    }

    AudioSpec get_spec() const override {
        return spec_;
    }

    size_t push_samples(std::span<const int16_t> samples) override {
        if (!is_open_ || paused_) return 0;
        total_samples_ += samples.size();
        return samples.size();
    }

    size_t get_queued_samples() const override {
        return 0;  // Always empty (immediately consumed)
    }

    size_t get_buffer_capacity() const override {
        return spec_.samples * spec_.channels * 4;  // 4x buffer
    }

    void pause(bool paused) override {
        paused_ = paused;
    }

    bool is_paused() const override {
        return paused_;
    }

    void clear() override {
        // No buffer to clear
    }

    /// Total samples received (for testing)
    uint64_t total_samples() const { return total_samples_; }

private:
    AudioSpec spec_;
    bool is_open_ = false;
    bool paused_ = false;
    uint64_t total_samples_ = 0;
};

} // namespace platform
} // namespace dosbox

#endif // DOSBOX_PLATFORM_AUDIO_H
