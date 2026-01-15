/**
 * @file headless_stub.cpp
 * @brief Headless mode stubs for AIBox.
 *
 * This file provides no-op implementations for SDL-dependent functions
 * when building in headless mode (AIBOX_HEADLESS defined).
 *
 * The "Lobotomy" - surgically severs the SDL UI from the DOSBox core:
 * - GFX_* functions: Video output stubs
 * - MAPPER_* functions: Keyboard mapper stubs
 * - SDL_GetTicks: Virtual tick system for deterministic timing
 *
 * ## Platform Timing Integration (PR #17)
 * The stub now supports pluggable timing via platform::ITiming interface.
 */

#include "aibox/headless_stub.h"
#include "dosbox/platform/timing.h"
#include "dosbox/platform/display.h"
#include "dosbox/platform/input.h"
#include "dosbox/platform/audio.h"
#include <atomic>
#include <cstdint>
#include <span>
#include <vector>

namespace aibox {
namespace headless {

// ============================================================================
// Virtual Tick System
// ============================================================================

namespace {
    // Virtual tick counter for deterministic timing (fallback)
    // Uses relaxed ordering since exact timing is not critical
    std::atomic<uint64_t> g_virtual_ticks{0};

    // Current video mode
    VideoMode g_video_mode{320, 200, 8, true};

    // Platform timing provider (PR #17)
    // When set, SDL_GetTicks/SDL_Delay use this instead of virtual ticks
    std::atomic<dosbox::platform::ITiming*> g_timing_provider{nullptr};

    // Platform display provider (PR #18)
    // When set, GFX_* calls use this instead of default VideoMode
    std::atomic<dosbox::platform::IDisplay*> g_display_provider{nullptr};

    // Palette storage for indexed modes (256 * 4 = 1024 bytes RGBA)
    std::vector<uint8_t> g_palette(1024, 0);

    // Platform input provider (PR #19)
    // When set, input events are pushed/polled through this provider
    std::atomic<dosbox::platform::IInput*> g_input_provider{nullptr};

    // Platform audio provider (PR #20)
    // When set, audio samples are pushed through this provider
    std::atomic<dosbox::platform::IAudio*> g_audio_provider{nullptr};
}

uint64_t GetTicks() noexcept {
    // Use platform timing provider if available
    auto* provider = g_timing_provider.load(std::memory_order_acquire);
    if (provider) {
        return provider->get_ticks();
    }
    return g_virtual_ticks.load(std::memory_order_relaxed);
}

void AdvanceTicks(uint32_t delta_ms) noexcept {
    // If using platform timing provider, advance through it
    auto* provider = g_timing_provider.load(std::memory_order_acquire);
    if (provider) {
        provider->advance_time(delta_ms);
        return;
    }
    g_virtual_ticks.fetch_add(delta_ms, std::memory_order_relaxed);
}

void ResetTicks() noexcept {
    g_virtual_ticks.store(0, std::memory_order_relaxed);
    // Note: Platform timing provider reset is handled by the provider owner
}

VideoMode GetVideoMode() noexcept {
    return g_video_mode;
}

void SetVideoMode(const VideoMode& mode) noexcept {
    g_video_mode = mode;
}

// ============================================================================
// Platform Timing Integration (PR #17)
// ============================================================================

void SetTimingProvider(dosbox::platform::ITiming* timing) noexcept {
    g_timing_provider.store(timing, std::memory_order_release);
}

dosbox::platform::ITiming* GetTimingProvider() noexcept {
    return g_timing_provider.load(std::memory_order_acquire);
}

bool HasTimingProvider() noexcept {
    return g_timing_provider.load(std::memory_order_acquire) != nullptr;
}

// ============================================================================
// Platform Display Integration (PR #18)
// ============================================================================

void SetDisplayProvider(dosbox::platform::IDisplay* display) noexcept {
    g_display_provider.store(display, std::memory_order_release);
}

dosbox::platform::IDisplay* GetDisplayProvider() noexcept {
    return g_display_provider.load(std::memory_order_acquire);
}

bool HasDisplayProvider() noexcept {
    return g_display_provider.load(std::memory_order_acquire) != nullptr;
}

void UploadFrame(const uint8_t* pixels, size_t size,
                 int width, int height, int bpp) noexcept {
    auto* provider = g_display_provider.load(std::memory_order_acquire);
    if (provider && pixels && size > 0) {
        dosbox::platform::FrameInfo info;
        info.width = static_cast<uint16_t>(width);
        info.height = static_cast<uint16_t>(height);
        info.is_text_mode = false;

        // Map bpp to pixel format
        switch (bpp) {
            case 8:
                info.format = dosbox::platform::PixelFormat::Indexed8;
                break;
            case 15:
            case 16:
                info.format = dosbox::platform::PixelFormat::RGB565;
                break;
            case 24:
                info.format = dosbox::platform::PixelFormat::RGB888;
                break;
            case 32:
                info.format = dosbox::platform::PixelFormat::BGRA8888;
                break;
            default:
                info.format = dosbox::platform::PixelFormat::Indexed8;
                break;
        }

        info.pitch = info.min_pitch();

        provider->upload_frame(std::span<const uint8_t>(pixels, size), info);
    }
}

void SetPalette(const uint8_t* palette, size_t size) noexcept {
    auto* provider = g_display_provider.load(std::memory_order_acquire);

    if (provider && palette && size > 0) {
        // Convert RGB palette to RGBA (provider expects RGBA format)
        if (size == 768) {  // 256 * 3 RGB entries
            g_palette.resize(1024);  // 256 * 4 RGBA entries
            for (size_t i = 0; i < 256; ++i) {
                g_palette[i * 4 + 0] = palette[i * 3 + 0];  // R
                g_palette[i * 4 + 1] = palette[i * 3 + 1];  // G
                g_palette[i * 4 + 2] = palette[i * 3 + 2];  // B
                g_palette[i * 4 + 3] = 255;                  // A
            }
            provider->set_palette(std::span<const uint8_t>(g_palette.data(), g_palette.size()));
        } else if (size == 1024) {  // Already RGBA
            provider->set_palette(std::span<const uint8_t>(palette, size));
        }
    }
}

// ============================================================================
// Platform Input Integration (PR #19)
// ============================================================================

void SetInputProvider(dosbox::platform::IInput* input) noexcept {
    g_input_provider.store(input, std::memory_order_release);
}

dosbox::platform::IInput* GetInputProvider() noexcept {
    return g_input_provider.load(std::memory_order_acquire);
}

bool HasInputProvider() noexcept {
    return g_input_provider.load(std::memory_order_acquire) != nullptr;
}

bool PushInputEvent(const dosbox::platform::InputEvent& event) noexcept {
    auto* provider = g_input_provider.load(std::memory_order_acquire);
    if (provider) {
        provider->push_event(event);
        return true;
    }
    return false;
}

bool PushKeyEvent(uint16_t keycode, bool pressed) noexcept {
    auto* provider = g_input_provider.load(std::memory_order_acquire);
    if (provider) {
        auto code = static_cast<dosbox::platform::KeyCode>(keycode);
        if (pressed) {
            provider->push_event(dosbox::platform::InputEvent::key_down(code));
        } else {
            provider->push_event(dosbox::platform::InputEvent::key_up(code));
        }
        return true;
    }
    return false;
}

bool PushMouseMotion(int16_t dx, int16_t dy) noexcept {
    auto* provider = g_input_provider.load(std::memory_order_acquire);
    if (provider) {
        provider->push_event(dosbox::platform::InputEvent::motion(dx, dy));
        return true;
    }
    return false;
}

bool PushMouseButton(uint8_t button, bool pressed) noexcept {
    auto* provider = g_input_provider.load(std::memory_order_acquire);
    if (provider) {
        auto btn = static_cast<dosbox::platform::MouseButton>(button);
        if (pressed) {
            provider->push_event(dosbox::platform::InputEvent::button_down(btn));
        } else {
            provider->push_event(dosbox::platform::InputEvent::button_up(btn));
        }
        return true;
    }
    return false;
}

// ============================================================================
// Platform Audio Integration (PR #20)
// ============================================================================

void SetAudioProvider(dosbox::platform::IAudio* audio) noexcept {
    g_audio_provider.store(audio, std::memory_order_release);
}

dosbox::platform::IAudio* GetAudioProvider() noexcept {
    return g_audio_provider.load(std::memory_order_acquire);
}

bool HasAudioProvider() noexcept {
    return g_audio_provider.load(std::memory_order_acquire) != nullptr;
}

size_t PushAudioSamples(const int16_t* samples, size_t count) noexcept {
    auto* provider = g_audio_provider.load(std::memory_order_acquire);
    if (provider && samples && count > 0) {
        return provider->push_samples(std::span<const int16_t>(samples, count));
    }
    return 0;
}

size_t GetQueuedAudioSamples() noexcept {
    auto* provider = g_audio_provider.load(std::memory_order_acquire);
    if (provider) {
        return provider->get_queued_samples();
    }
    return 0;
}

void ClearAudioBuffer() noexcept {
    auto* provider = g_audio_provider.load(std::memory_order_acquire);
    if (provider) {
        provider->clear();
    }
}

void PauseAudio(bool paused) noexcept {
    auto* provider = g_audio_provider.load(std::memory_order_acquire);
    if (provider) {
        provider->pause(paused);
    }
}

} // namespace headless
} // namespace aibox

// ============================================================================
// Headless Stubs (Only compiled when AIBOX_HEADLESS is defined)
// ============================================================================

#ifdef AIBOX_HEADLESS

extern "C" {

// ----------------------------------------------------------------------------
// Video Stubs (GFX_* functions)
// ----------------------------------------------------------------------------

/**
 * @brief No-op video initialization.
 * The real GFX_Init() would create an SDL window.
 */
void GFX_Init() {
    // Intentionally empty - no window needed
}

/**
 * @brief Frame update notification.
 *
 * In headless mode, this calls present() on the display provider if set.
 * Actual frame data is uploaded via UploadFrame() from the VGA subsystem.
 *
 * @param changedLines Bitmap of changed scanlines (ignored)
 */
void GFX_EndUpdate(const uint16_t* changedLines) {
    (void)changedLines;

    // Present to display provider if set (PR #18)
    auto* provider = aibox::headless::GetDisplayProvider();
    if (provider) {
        provider->present();
    }
}

/**
 * @brief No-op window title update.
 *
 * @param cycles Current CPU cycles
 * @param frameskip Frameskip setting
 * @param paused Whether emulation is paused
 */
void GFX_SetTitle(int32_t cycles, int frameskip, bool paused) {
    (void)cycles;
    (void)frameskip;
    (void)paused;
    // No window, no title
}

/**
 * @brief No-op event polling.
 *
 * This is the "heartbeat" of the emulator. In SDL mode, this would
 * poll for keyboard/mouse events. In headless mode, we do nothing
 * because input is injected directly via aibox_key_event() and
 * aibox_mouse_event().
 */
void GFX_Events() {
    // Heartbeat called every frame - no SDL events to poll
}

/**
 * @brief VGA mode change notification.
 *
 * Updates internal video mode and notifies display provider if set.
 *
 * @param width New width
 * @param height New height
 * @param bpp Bits per pixel
 */
void GFX_SetSize(int width, int height, int bpp) {
    aibox::headless::VideoMode mode;
    mode.width = width;
    mode.height = height;
    mode.bpp = bpp;
    mode.is_indexed = (bpp <= 8);
    aibox::headless::SetVideoMode(mode);

    // Notify display provider of mode change (PR #18)
    auto* provider = aibox::headless::GetDisplayProvider();
    if (provider) {
        dosbox::platform::PixelFormat format;
        switch (bpp) {
            case 8:  format = dosbox::platform::PixelFormat::Indexed8; break;
            case 15:
            case 16: format = dosbox::platform::PixelFormat::RGB565; break;
            case 24: format = dosbox::platform::PixelFormat::RGB888; break;
            case 32: format = dosbox::platform::PixelFormat::BGRA8888; break;
            default: format = dosbox::platform::PixelFormat::Indexed8; break;
        }
        provider->set_mode(static_cast<uint16_t>(width),
                           static_cast<uint16_t>(height),
                           format, false);
    }
}

// ----------------------------------------------------------------------------
// Mapper Stubs (MAPPER_* functions)
// ----------------------------------------------------------------------------

/**
 * @brief No-op mapper initialization.
 * The real MAPPER_Init() would set up key bindings via SDL.
 */
void MAPPER_Init() {
    // No physical keyboard mappings in headless mode
}

/**
 * @brief No-op mapper key handler.
 *
 * @param pressed Whether the key is pressed
 */
void MAPPER_Run(bool pressed) {
    (void)pressed;
    // Input is injected directly via aibox_key_event()
}

/**
 * @brief No-op mapper check.
 * Called periodically to check for hotkeys.
 */
void MAPPER_Check() {
    // No hotkeys in headless mode
}

// ----------------------------------------------------------------------------
// SDL Tick Replacement
// ----------------------------------------------------------------------------

/**
 * @brief Virtual tick implementation of SDL_GetTicks.
 *
 * Returns virtual ticks instead of wall-clock time.
 * This makes emulation fully deterministic.
 *
 * @return Current virtual tick count (milliseconds)
 */
uint32_t SDL_GetTicks() {
    uint64_t ticks = aibox::headless::GetTicks();
    // Wrap at 32-bit boundary like real SDL_GetTicks
    return static_cast<uint32_t>(ticks & 0xFFFFFFFF);
}

/**
 * @brief SDL delay implementation.
 *
 * In deterministic mode (default), this is a no-op.
 * If a non-deterministic timing provider is set, it will actually delay.
 *
 * @param ms Milliseconds to delay
 */
void SDL_Delay(uint32_t ms) {
    auto* provider = aibox::headless::GetTimingProvider();
    if (provider && !provider->is_deterministic()) {
        // Non-deterministic timing - actually delay
        provider->delay(ms);
    }
    // Deterministic timing - no actual delay (virtual time)
}

} // extern "C"

#endif // AIBOX_HEADLESS
