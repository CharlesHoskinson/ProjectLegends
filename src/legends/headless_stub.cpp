/**
 * @file headless_stub.cpp
 * @brief Headless mode stubs for Legends.
 *
 * This file provides no-op implementations for SDL-dependent functions
 * when building in headless mode (LEGENDS_HEADLESS defined).
 *
 * The "Lobotomy" - surgically severs the SDL UI from the DOSBox core:
 * - GFX_* functions: Video output stubs
 * - MAPPER_* functions: Keyboard mapper stubs
 * - SDL_GetTicks: Virtual tick system for deterministic timing
 */

#include "legends/headless_stub.h"
#include <atomic>
#include <cstdint>

namespace legends {
namespace headless {

// ============================================================================
// Virtual Tick System
// ============================================================================

namespace {
    // Virtual tick counter for deterministic timing
    // Uses relaxed ordering since exact timing is not critical
    std::atomic<uint64_t> g_virtual_ticks{0};

    // Current video mode
    VideoMode g_video_mode{320, 200, 8, true};
}

uint64_t GetTicks() noexcept {
    return g_virtual_ticks.load(std::memory_order_relaxed);
}

void AdvanceTicks(uint32_t delta_ms) noexcept {
    g_virtual_ticks.fetch_add(delta_ms, std::memory_order_relaxed);
}

void ResetTicks() noexcept {
    g_virtual_ticks.store(0, std::memory_order_relaxed);
}

VideoMode GetVideoMode() noexcept {
    return g_video_mode;
}

void SetVideoMode(const VideoMode& mode) noexcept {
    g_video_mode = mode;
}

} // namespace headless
} // namespace legends

// ============================================================================
// Headless Stubs (Only compiled when LEGENDS_HEADLESS is defined)
// ============================================================================

#ifdef LEGENDS_HEADLESS

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
 * @brief No-op frame update.
 *
 * The real GFX_EndUpdate() would blit to the SDL window.
 * In headless mode, the framebuffer is captured via legends_video_capture().
 *
 * @param changedLines Bitmap of changed scanlines (ignored)
 */
void GFX_EndUpdate(const uint16_t* changedLines) {
    (void)changedLines;
    // Framebuffer is captured directly via FFI, no blit needed
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
 * because input is injected directly via legends_key_event() and
 * legends_mouse_event().
 */
void GFX_Events() {
    // Heartbeat called every frame - no SDL events to poll
}

/**
 * @brief No-op VGA mode change notification.
 *
 * @param width New width
 * @param height New height
 * @param bpp Bits per pixel
 */
void GFX_SetSize(int width, int height, int bpp) {
    legends::headless::VideoMode mode;
    mode.width = width;
    mode.height = height;
    mode.bpp = bpp;
    mode.is_indexed = (bpp <= 8);
    legends::headless::SetVideoMode(mode);
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
    // Input is injected directly via legends_key_event()
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
    uint64_t ticks = legends::headless::GetTicks();
    // Wrap at 32-bit boundary like real SDL_GetTicks
    return static_cast<uint32_t>(ticks & 0xFFFFFFFF);
}

/**
 * @brief No-op SDL delay.
 *
 * In headless mode, we don't wait for wall-clock time.
 * The virtual tick system handles timing.
 *
 * @param ms Milliseconds to delay (ignored)
 */
void SDL_Delay(uint32_t ms) {
    (void)ms;
    // Virtual time - no actual delay
}

} // extern "C"

#endif // LEGENDS_HEADLESS
