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

// Cross-platform weak symbol support
// On GCC/Clang: __attribute__((weak)) allows override at link time
// On MSVC: selectany provides similar semantics for functions
#if defined(_MSC_VER)
    #define WEAK_SYMBOL __declspec(selectany)
    // MSVC doesn't support weak functions directly, use inline+selectany pattern
    #define WEAK_FUNCTION inline
#elif defined(__GNUC__) || defined(__clang__)
    #define WEAK_SYMBOL __attribute__((weak))
    #define WEAK_FUNCTION __attribute__((weak))
#else
    #define WEAK_SYMBOL
    #define WEAK_FUNCTION
#endif

namespace aibox {
namespace headless {

// ============================================================================
// Virtual Tick System
// ============================================================================

namespace {
struct HeadlessState {
    std::atomic<uint64_t> virtual_ticks{0};
    VideoMode video_mode{320, 200, 8, true};
    std::atomic<dosbox::platform::ITiming*> timing_provider{nullptr};
    std::atomic<dosbox::platform::IDisplay*> display_provider{nullptr};
    std::vector<uint8_t> palette{std::vector<uint8_t>(1024, 0)};
    std::atomic<dosbox::platform::IInput*> input_provider{nullptr};
    std::atomic<dosbox::platform::IAudio*> audio_provider{nullptr};

    void reset() {
        virtual_ticks.store(0, std::memory_order_relaxed);
        video_mode = {320, 200, 8, true};
        timing_provider.store(nullptr, std::memory_order_release);
        display_provider.store(nullptr, std::memory_order_release);
        palette.assign(1024, 0);
        input_provider.store(nullptr, std::memory_order_release);
        audio_provider.store(nullptr, std::memory_order_release);
    }
};

HeadlessState g_state;
} // anon namespace

uint64_t GetTicks() noexcept {
    // Use platform timing provider if available
    auto* provider = g_state.timing_provider.load(std::memory_order_acquire);
    if (provider) {
        return provider->get_ticks();
    }
    return g_state.virtual_ticks.load(std::memory_order_relaxed);
}

void AdvanceTicks(uint32_t delta_ms) noexcept {
    // If using platform timing provider, advance through it
    auto* provider = g_state.timing_provider.load(std::memory_order_acquire);
    if (provider) {
        provider->advance_time(delta_ms);
        return;
    }
    g_state.virtual_ticks.fetch_add(delta_ms, std::memory_order_relaxed);
}

void ResetTicks() noexcept {
    g_state.virtual_ticks.store(0, std::memory_order_relaxed);
    // Note: Platform timing provider reset is handled by the provider owner
}

VideoMode GetVideoMode() noexcept {
    return g_state.video_mode;
}

void SetVideoMode(const VideoMode& mode) noexcept {
    g_state.video_mode = mode;
}

// ============================================================================
// Platform Timing Integration (PR #17)
// ============================================================================

void SetTimingProvider(dosbox::platform::ITiming* timing) noexcept {
    g_state.timing_provider.store(timing, std::memory_order_release);
}

dosbox::platform::ITiming* GetTimingProvider() noexcept {
    return g_state.timing_provider.load(std::memory_order_acquire);
}

bool HasTimingProvider() noexcept {
    return g_state.timing_provider.load(std::memory_order_acquire) != nullptr;
}

// ============================================================================
// Platform Display Integration (PR #18)
// ============================================================================

void SetDisplayProvider(dosbox::platform::IDisplay* display) noexcept {
    g_state.display_provider.store(display, std::memory_order_release);
}

dosbox::platform::IDisplay* GetDisplayProvider() noexcept {
    return g_state.display_provider.load(std::memory_order_acquire);
}

bool HasDisplayProvider() noexcept {
    return g_state.display_provider.load(std::memory_order_acquire) != nullptr;
}

void UploadFrame(const uint8_t* pixels, size_t size,
                 int width, int height, int bpp) noexcept {
    auto* provider = g_state.display_provider.load(std::memory_order_acquire);
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
    auto* provider = g_state.display_provider.load(std::memory_order_acquire);

    if (provider && palette && size > 0) {
        // Convert RGB palette to RGBA (provider expects RGBA format)
        if (size == 768) {  // 256 * 3 RGB entries
            g_state.palette.resize(1024);  // 256 * 4 RGBA entries
            for (size_t i = 0; i < 256; ++i) {
                g_state.palette[i * 4 + 0] = palette[i * 3 + 0];  // R
                g_state.palette[i * 4 + 1] = palette[i * 3 + 1];  // G
                g_state.palette[i * 4 + 2] = palette[i * 3 + 2];  // B
                g_state.palette[i * 4 + 3] = 255;                  // A
            }
            provider->set_palette(std::span<const uint8_t>(g_state.palette.data(), g_state.palette.size()));
        } else if (size == 1024) {  // Already RGBA
            provider->set_palette(std::span<const uint8_t>(palette, size));
        }
    }
}

// ============================================================================
// Platform Input Integration (PR #19)
// ============================================================================

void SetInputProvider(dosbox::platform::IInput* input) noexcept {
    g_state.input_provider.store(input, std::memory_order_release);
}

dosbox::platform::IInput* GetInputProvider() noexcept {
    return g_state.input_provider.load(std::memory_order_acquire);
}

bool HasInputProvider() noexcept {
    return g_state.input_provider.load(std::memory_order_acquire) != nullptr;
}

bool PushInputEvent(const dosbox::platform::InputEvent& event) noexcept {
    auto* provider = g_state.input_provider.load(std::memory_order_acquire);
    if (provider) {
        provider->push_event(event);
        return true;
    }
    return false;
}

bool PushKeyEvent(uint16_t keycode, bool pressed) noexcept {
    auto* provider = g_state.input_provider.load(std::memory_order_acquire);
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
    auto* provider = g_state.input_provider.load(std::memory_order_acquire);
    if (provider) {
        provider->push_event(dosbox::platform::InputEvent::motion(dx, dy));
        return true;
    }
    return false;
}

bool PushMouseButton(uint8_t button, bool pressed) noexcept {
    auto* provider = g_state.input_provider.load(std::memory_order_acquire);
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
    g_state.audio_provider.store(audio, std::memory_order_release);
}

dosbox::platform::IAudio* GetAudioProvider() noexcept {
    return g_state.audio_provider.load(std::memory_order_acquire);
}

bool HasAudioProvider() noexcept {
    return g_state.audio_provider.load(std::memory_order_acquire) != nullptr;
}

size_t PushAudioSamples(const int16_t* samples, size_t count) noexcept {
    auto* provider = g_state.audio_provider.load(std::memory_order_acquire);
    if (provider && samples && count > 0) {
        return provider->push_samples(std::span<const int16_t>(samples, count));
    }
    return 0;
}

size_t GetQueuedAudioSamples() noexcept {
    auto* provider = g_state.audio_provider.load(std::memory_order_acquire);
    if (provider) {
        return provider->get_queued_samples();
    }
    return 0;
}

void ClearAudioBuffer() noexcept {
    auto* provider = g_state.audio_provider.load(std::memory_order_acquire);
    if (provider) {
        provider->clear();
    }
}

void PauseAudio(bool paused) noexcept {
    auto* provider = g_state.audio_provider.load(std::memory_order_acquire);
    if (provider) {
        provider->pause(paused);
    }
}

void ResetState() noexcept {
    g_state.reset();
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
 * Note: Marked weak so real SDL2 symbols override when linked.
 *
 * @return Current virtual tick count (milliseconds)
 */
WEAK_FUNCTION uint32_t SDL_GetTicks() {
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
 * Note: Marked weak so real SDL2 symbols override when linked.
 *
 * @param ms Milliseconds to delay
 */
WEAK_FUNCTION void SDL_Delay(uint32_t ms) {
    auto* provider = aibox::headless::GetTimingProvider();
    if (provider && !provider->is_deterministic()) {
        // Non-deterministic timing - actually delay
        provider->delay(ms);
    }
    // Deterministic timing - no actual delay (virtual time)
}

// ----------------------------------------------------------------------------
// Phase 3: Enhanced Features Forwarding Stubs
// These stubs satisfy the linker when the real engine modules (printer.cpp,
// ipx.cpp, midi.cpp) are not compiled into the headless/test build.
// ----------------------------------------------------------------------------

// Printer stubs (real implementations in printer.cpp, behind C_PRINTER)
void dosbox_printer_set_output_dir(const char* path) { (void)path; }
int  dosbox_printer_is_active() { return 0; }
void dosbox_printer_flush() {}

// IPX stubs (real implementations in ipx.cpp, behind C_IPX)
void dosbox_ipx_set_enabled(int enable) { (void)enable; }
int  dosbox_ipx_connect(const char* server, uint16_t port) { (void)server; (void)port; return 0; }
void dosbox_ipx_disconnect() {}
int  dosbox_ipx_is_connected() { return 0; }

// MIDI stubs (real implementations in midi.cpp)
void dosbox_midi_set_device(const char* device_type) { (void)device_type; }
void dosbox_midi_set_soundfont(const char* sf2_path) { (void)sf2_path; }
void dosbox_midi_set_romdir(const char* rom_dir) { (void)rom_dir; }
int  dosbox_midi_capture_audio(int16_t* buf, size_t count, size_t* out) {
    (void)buf; (void)count;
    if (out) *out = 0;
    return 1;
}

} // extern "C"

#endif // AIBOX_HEADLESS
