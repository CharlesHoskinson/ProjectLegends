/**
 * @file headless_stub.h
 * @brief Headless mode API for Legends.
 *
 * This header defines the virtual tick system and headless mode utilities
 * for running DOSBox-X without SDL dependencies.
 *
 * When LEGENDS_HEADLESS is defined:
 * - SDL_GetTicks() returns virtual ticks instead of wall-clock time
 * - GFX_* functions are no-ops (rendering is captured via FFI)
 * - MAPPER_* functions are no-ops (input is injected via FFI)
 * - Timing is fully deterministic for reproducible AI training
 */

#ifndef LEGENDS_HEADLESS_STUB_H
#define LEGENDS_HEADLESS_STUB_H

#include <cstdint>

namespace legends {
namespace headless {

/**
 * @brief Get current virtual tick count.
 *
 * Virtual ticks advance only when legends_step() is called,
 * providing deterministic timing independent of wall-clock.
 *
 * @return Current virtual tick count in milliseconds
 */
uint64_t GetTicks() noexcept;

/**
 * @brief Advance virtual tick counter.
 *
 * Called internally by legends_step() to advance virtual time.
 * Each tick represents 1 millisecond of virtual time.
 *
 * @param delta_ms Number of milliseconds to advance
 */
void AdvanceTicks(uint32_t delta_ms) noexcept;

/**
 * @brief Reset virtual tick counter to zero.
 *
 * Called during legends_create() or legends_init() to reset timing.
 */
void ResetTicks() noexcept;

/**
 * @brief Check if running in headless mode.
 *
 * @return true if LEGENDS_HEADLESS is defined, false otherwise
 */
constexpr bool IsHeadless() noexcept {
#ifdef LEGENDS_HEADLESS
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

} // namespace headless
} // namespace legends

#endif /* LEGENDS_HEADLESS_STUB_H */
