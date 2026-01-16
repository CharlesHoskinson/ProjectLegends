/**
 * @file headless.h
 * @brief Headless platform backend implementations for testing and AI agents.
 *
 * Provides concrete implementations of platform interfaces that:
 * - Store frames for programmatic capture and analysis
 * - Buffer audio samples for verification
 * - Work without any display/audio hardware
 *
 * ## Use Cases
 * - Unit and integration testing
 * - AI agent training and evaluation
 * - Server-side emulation
 * - Automated game testing
 *
 * @copyright GPL-2.0-or-later
 */

#ifndef DOSBOX_PLATFORM_HEADLESS_H
#define DOSBOX_PLATFORM_HEADLESS_H

#include "dosbox/platform/display.h"
#include "dosbox/platform/audio.h"
#include "dosbox/platform/input.h"
#include "dosbox/platform/timing.h"
#include "dosbox/platform/platform.h"

#include <vector>
#include <mutex>
#include <atomic>

namespace dosbox {
namespace platform {

// ═══════════════════════════════════════════════════════════════════════════════
// Headless Display
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Headless display that captures frames for programmatic access.
 *
 * Unlike NullDisplay which discards frames, HeadlessDisplay stores
 * the most recent frame for capture and analysis. Useful for:
 * - Screenshot comparison in tests
 * - AI vision model input
 * - Automated UI testing
 *
 * ## Thread Safety
 * Frame capture uses a mutex for safe access from other threads.
 *
 * ## Memory Usage
 * Stores one frame at a time. For 1920x1080 BGRA, that's ~8MB.
 */
class HeadlessDisplay : public IDisplay {
public:
    HeadlessDisplay() = default;
    ~HeadlessDisplay() override = default;

    // ─────────────────────────────────────────────────────────────────────────
    // IDisplay Implementation
    // ─────────────────────────────────────────────────────────────────────────

    void set_mode(uint16_t width, uint16_t height,
                  PixelFormat format, bool fullscreen) override;

    void set_aspect_ratio(float ratio) override;

    FrameInfo get_frame_info() const override;

    void upload_frame(std::span<const uint8_t> pixels,
                      const FrameInfo& info) override;

    void present() override;

    bool supports_hardware_present() const override { return false; }

    void set_palette(std::span<const uint8_t> palette) override;

    std::vector<uint8_t> capture_frame() const override;

    bool has_frame() const override;

    // ─────────────────────────────────────────────────────────────────────────
    // Headless-Specific API
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Get the current palette (for indexed modes).
     */
    std::vector<uint8_t> get_palette() const;

    /**
     * @brief Capture frame converted to RGBA8888 format.
     *
     * Handles palette expansion for indexed modes.
     * Useful for feeding to image processing or AI models.
     */
    std::vector<uint8_t> capture_frame_rgba() const;

    /**
     * @brief Get total number of frames uploaded.
     */
    uint64_t frame_count() const { return frame_count_.load(); }

    /**
     * @brief Get total number of presents called.
     */
    uint64_t present_count() const { return present_count_.load(); }

    /**
     * @brief Clear the captured frame buffer.
     */
    void clear_frame();

    /**
     * @brief Enable/disable frame storage (for performance).
     *
     * When disabled, frames are counted but not stored.
     */
    void set_capture_enabled(bool enabled) { capture_enabled_ = enabled; }
    bool is_capture_enabled() const { return capture_enabled_; }

private:
    mutable std::mutex mutex_;
    FrameInfo info_;
    float aspect_ratio_ = 4.0f / 3.0f;
    std::vector<uint8_t> frame_buffer_;
    std::vector<uint8_t> palette_;  // 256 * 4 = 1024 bytes (RGBA)
    std::atomic<uint64_t> frame_count_{0};
    std::atomic<uint64_t> present_count_{0};
    std::atomic<bool> has_frame_{false};
    bool capture_enabled_ = true;
};

// ═══════════════════════════════════════════════════════════════════════════════
// Buffer Audio
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Audio backend that buffers samples for analysis.
 *
 * Unlike NullAudio which discards samples, BufferAudio stores them
 * in a ring buffer. Useful for:
 * - Audio output verification in tests
 * - Waveform analysis
 * - Audio-based game state detection
 *
 * ## Thread Safety
 * Push/pop operations are thread-safe via mutex.
 *
 * ## Memory Usage
 * Default 1 second buffer at 44100Hz stereo S16 = ~176KB.
 */
class BufferAudio : public IAudio {
public:
    /**
     * @brief Construct with specified buffer duration.
     *
     * @param buffer_seconds How many seconds of audio to buffer (default 1.0)
     */
    explicit BufferAudio(float buffer_seconds = 1.0f);
    ~BufferAudio() override = default;

    // ─────────────────────────────────────────────────────────────────────────
    // IAudio Implementation
    // ─────────────────────────────────────────────────────────────────────────

    bool open(const AudioSpec& spec) override;
    void close() override;
    bool is_open() const override;
    AudioSpec get_spec() const override;

    size_t push_samples(std::span<const int16_t> samples) override;
    size_t push_samples_float(std::span<const float> samples) override;

    size_t get_queued_samples() const override;
    size_t get_buffer_capacity() const override;

    void pause(bool paused) override;
    bool is_paused() const override;
    void clear() override;

    // ─────────────────────────────────────────────────────────────────────────
    // Buffer-Specific API
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Pop samples from the buffer (simulates playback consumption).
     *
     * @param count Number of samples to pop
     * @return Samples removed from buffer
     */
    std::vector<int16_t> pop_samples(size_t count);

    /**
     * @brief Peek at buffered samples without removing them.
     *
     * @param count Number of samples to peek
     * @return Copy of samples (may be less than requested)
     */
    std::vector<int16_t> peek_samples(size_t count) const;

    /**
     * @brief Get all buffered samples.
     */
    std::vector<int16_t> get_all_samples() const;

    /**
     * @brief Get total samples ever pushed.
     */
    uint64_t total_samples_pushed() const { return total_pushed_.load(); }

    /**
     * @brief Get total samples ever popped/consumed.
     */
    uint64_t total_samples_popped() const { return total_popped_.load(); }

    /**
     * @brief Calculate RMS (root mean square) of buffered audio.
     *
     * Useful for detecting silence or audio activity.
     */
    float calculate_rms() const;

    /**
     * @brief Check if audio is effectively silent (RMS below threshold).
     */
    bool is_silent(float threshold = 0.01f) const;

private:
    mutable std::mutex mutex_;
    AudioSpec spec_;
    float buffer_seconds_;
    std::vector<int16_t> buffer_;
    size_t write_pos_ = 0;
    size_t read_pos_ = 0;
    size_t queued_ = 0;
    size_t capacity_ = 0;
    bool is_open_ = false;
    bool paused_ = false;
    std::atomic<uint64_t> total_pushed_{0};
    std::atomic<uint64_t> total_popped_{0};
};

// ═══════════════════════════════════════════════════════════════════════════════
// Thread-Safe Queue Input
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Thread-safe input queue for multi-threaded scenarios.
 *
 * Extends QueueInput with mutex protection for safe access from
 * multiple threads (e.g., input injection from a separate thread).
 */
class ThreadSafeInput : public IInput {
public:
    ThreadSafeInput() = default;
    ~ThreadSafeInput() override = default;

    void push_event(const InputEvent& event) override;
    std::optional<InputEvent> poll_event() override;
    bool has_events() const override;
    void clear() override;

    bool is_mouse_captured() const override;
    void set_mouse_captured(bool captured) override;
    KeyMod get_modifiers() const override;
    void set_modifiers(KeyMod mods);

    size_t queue_size() const;

private:
    mutable std::mutex mutex_;
    std::queue<InputEvent> events_;
    bool mouse_captured_ = false;
    KeyMod modifiers_ = KeyMod::None;
};

// ═══════════════════════════════════════════════════════════════════════════════
// Headless Backend Factory
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Complete headless backend with capture capabilities.
 *
 * Owns all the platform interface implementations.
 */
struct HeadlessBackend {
    HeadlessDisplay display;
    BufferAudio audio;
    ThreadSafeInput input;
    VirtualTiming timing;

    /**
     * @brief Construct with specified audio buffer duration.
     */
    explicit HeadlessBackend(float audio_buffer_seconds = 1.0f)
        : display()
        , audio(audio_buffer_seconds)
        , input()
        , timing()
    {}

    // Non-copyable due to mutex/atomic in BufferAudio
    HeadlessBackend(const HeadlessBackend&) = delete;
    HeadlessBackend& operator=(const HeadlessBackend&) = delete;

    // Movable
    HeadlessBackend(HeadlessBackend&&) = default;
    HeadlessBackend& operator=(HeadlessBackend&&) = default;

    /**
     * @brief Get as PlatformBackend for use with DOSBox.
     */
    PlatformBackend as_platform_backend() {
        return PlatformBackend{
            &display,
            &audio,
            &input,
            &timing
        };
    }

    /**
     * @brief Reset all components to initial state.
     */
    void reset() {
        display.clear_frame();
        audio.clear();
        input.clear();
        timing.reset();
    }
};

/**
 * @brief Create a new headless backend instance.
 *
 * @param audio_buffer_seconds Audio buffer duration
 * @return Unique pointer to headless backend
 */
inline std::unique_ptr<HeadlessBackend> make_headless_backend(
    float audio_buffer_seconds = 1.0f)
{
    return std::make_unique<HeadlessBackend>(audio_buffer_seconds);
}

} // namespace platform
} // namespace dosbox

#endif // DOSBOX_PLATFORM_HEADLESS_H
