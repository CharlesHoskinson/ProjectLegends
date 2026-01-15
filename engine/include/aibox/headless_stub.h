/**
 * @file headless_stub.h
 * @brief Headless mode API for AIBox.
 *
 * This header defines the virtual tick system and headless mode utilities
 * for running DOSBox-X without SDL dependencies.
 *
 * When AIBOX_HEADLESS is defined:
 * - SDL_GetTicks() returns virtual ticks instead of wall-clock time
 * - GFX_* functions are no-ops (rendering is captured via FFI)
 * - MAPPER_* functions are no-ops (input is injected via FFI)
 * - Timing is fully deterministic for reproducible AI training
 *
 * ## Platform Timing Integration (PR #17)
 * The headless stub now integrates with the platform::ITiming interface
 * from PR #15. This allows the timing source to be configured per-context.
 */

#ifndef AIBOX_HEADLESS_STUB_H
#define AIBOX_HEADLESS_STUB_H

#include <cstdint>

// Forward declaration to avoid circular dependency
namespace dosbox {
namespace platform {
    class ITiming;
    class IDisplay;
    class IInput;
    class IAudio;
    struct InputEvent;
}
}

namespace aibox {
namespace headless {

/**
 * @brief Get current virtual tick count.
 *
 * Virtual ticks advance only when aibox_step() is called,
 * providing deterministic timing independent of wall-clock.
 *
 * @return Current virtual tick count in milliseconds
 */
uint64_t GetTicks() noexcept;

/**
 * @brief Advance virtual tick counter.
 *
 * Called internally by aibox_step() to advance virtual time.
 * Each tick represents 1 millisecond of virtual time.
 *
 * @param delta_ms Number of milliseconds to advance
 */
void AdvanceTicks(uint32_t delta_ms) noexcept;

/**
 * @brief Reset virtual tick counter to zero.
 *
 * Called during aibox_create() or aibox_init() to reset timing.
 */
void ResetTicks() noexcept;

/**
 * @brief Check if running in headless mode.
 *
 * @return true if AIBOX_HEADLESS is defined, false otherwise
 */
constexpr bool IsHeadless() noexcept {
#ifdef AIBOX_HEADLESS
    return true;
#else
    return false;
#endif
}

/**
 * @brief Video mode information for headless capture.
 */
struct VideoMode {
    int width;          /**< Width in pixels */
    int height;         /**< Height in pixels */
    int bpp;            /**< Bits per pixel (8 for indexed, 32 for RGBA) */
    bool is_indexed;    /**< True if using palette-indexed mode */
};

/**
 * @brief Get current video mode.
 *
 * @return Current video mode settings
 */
VideoMode GetVideoMode() noexcept;

/**
 * @brief Set video mode (called by VGA emulation).
 *
 * @param mode Video mode to set
 */
void SetVideoMode(const VideoMode& mode) noexcept;

// ─────────────────────────────────────────────────────────────────────────────
// Platform Timing Integration (PR #17)
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Set the timing provider for SDL timing calls.
 *
 * When set, SDL_GetTicks() and SDL_Delay() will use this provider
 * instead of the default virtual ticks.
 *
 * @param timing Timing provider, or nullptr to use default virtual ticks
 */
void SetTimingProvider(dosbox::platform::ITiming* timing) noexcept;

/**
 * @brief Get the current timing provider.
 *
 * @return Current timing provider, or nullptr if using default
 */
dosbox::platform::ITiming* GetTimingProvider() noexcept;

/**
 * @brief Check if a custom timing provider is set.
 */
bool HasTimingProvider() noexcept;

// ─────────────────────────────────────────────────────────────────────────────
// Platform Display Integration (PR #18)
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Set the display provider for GFX_* calls.
 *
 * When set, GFX_EndUpdate() and GFX_SetSize() will use this provider
 * instead of the default VideoMode storage.
 *
 * @param display Display provider, or nullptr to use default
 */
void SetDisplayProvider(dosbox::platform::IDisplay* display) noexcept;

/**
 * @brief Get the current display provider.
 *
 * @return Current display provider, or nullptr if using default
 */
dosbox::platform::IDisplay* GetDisplayProvider() noexcept;

/**
 * @brief Check if a custom display provider is set.
 */
bool HasDisplayProvider() noexcept;

/**
 * @brief Notify display of a frame upload (called by VGA subsystem).
 *
 * This is called internally when the VGA subsystem produces a new frame.
 * If a display provider is set, the frame data is forwarded to it.
 *
 * @param pixels Raw pixel data
 * @param size Size of pixel data in bytes
 * @param width Frame width
 * @param height Frame height
 * @param bpp Bits per pixel
 */
void UploadFrame(const uint8_t* pixels, size_t size,
                 int width, int height, int bpp) noexcept;

/**
 * @brief Set the palette for indexed modes.
 *
 * @param palette 256 RGB entries (768 bytes)
 */
void SetPalette(const uint8_t* palette, size_t size) noexcept;

// ─────────────────────────────────────────────────────────────────────────────
// Platform Input Integration (PR #19)
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Set the input provider for event handling.
 *
 * When set, input events are polled from this provider during GFX_Events()
 * and can be injected via PushInputEvent().
 *
 * @param input Input provider, or nullptr to disable
 */
void SetInputProvider(dosbox::platform::IInput* input) noexcept;

/**
 * @brief Get the current input provider.
 *
 * @return Current input provider, or nullptr if none set
 */
dosbox::platform::IInput* GetInputProvider() noexcept;

/**
 * @brief Check if an input provider is set.
 */
bool HasInputProvider() noexcept;

/**
 * @brief Push an input event to the current provider.
 *
 * Convenience function to inject keyboard/mouse events.
 *
 * @param event Event to push
 * @return true if event was pushed, false if no provider
 */
bool PushInputEvent(const dosbox::platform::InputEvent& event) noexcept;

/**
 * @brief Push a key event.
 *
 * @param keycode Platform-independent key code
 * @param pressed true for key down, false for key up
 * @return true if event was pushed
 */
bool PushKeyEvent(uint16_t keycode, bool pressed) noexcept;

/**
 * @brief Push a mouse motion event.
 *
 * @param dx Relative X motion
 * @param dy Relative Y motion
 * @return true if event was pushed
 */
bool PushMouseMotion(int16_t dx, int16_t dy) noexcept;

/**
 * @brief Push a mouse button event.
 *
 * @param button Button number (0=left, 1=middle, 2=right)
 * @param pressed true for button down, false for button up
 * @return true if event was pushed
 */
bool PushMouseButton(uint8_t button, bool pressed) noexcept;

// ─────────────────────────────────────────────────────────────────────────────
// Platform Audio Integration (PR #20)
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Set the audio provider for sound output.
 *
 * When set, audio samples produced during emulation are pushed to this provider.
 *
 * @param audio Audio provider, or nullptr to disable
 */
void SetAudioProvider(dosbox::platform::IAudio* audio) noexcept;

/**
 * @brief Get the current audio provider.
 *
 * @return Current audio provider, or nullptr if none set
 */
dosbox::platform::IAudio* GetAudioProvider() noexcept;

/**
 * @brief Check if an audio provider is set.
 */
bool HasAudioProvider() noexcept;

/**
 * @brief Push audio samples to the current provider.
 *
 * Called by the mixer during emulation to output audio.
 *
 * @param samples Interleaved signed 16-bit samples
 * @param count Number of samples (total, including all channels)
 * @return Number of samples accepted, or 0 if no provider
 */
size_t PushAudioSamples(const int16_t* samples, size_t count) noexcept;

/**
 * @brief Get the number of queued audio samples.
 *
 * @return Number of samples in buffer, or 0 if no provider
 */
size_t GetQueuedAudioSamples() noexcept;

/**
 * @brief Clear all queued audio samples.
 */
void ClearAudioBuffer() noexcept;

/**
 * @brief Pause or resume audio playback.
 *
 * @param paused true to pause, false to resume
 */
void PauseAudio(bool paused) noexcept;

} // namespace headless
} // namespace aibox

#endif /* AIBOX_HEADLESS_STUB_H */
