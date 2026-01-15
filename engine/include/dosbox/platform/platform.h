/**
 * @file platform.h
 * @brief Convenience header for all platform interfaces.
 *
 * Include this header to get all platform abstraction interfaces:
 * - IDisplay: Display/rendering abstraction
 * - IAudio: Audio output abstraction
 * - IInput: Input handling abstraction
 * - ITiming: Timing/delay abstraction
 *
 * @copyright GPL-2.0-or-later
 */

#ifndef DOSBOX_PLATFORM_PLATFORM_H
#define DOSBOX_PLATFORM_PLATFORM_H

#include "dosbox/platform/display.h"
#include "dosbox/platform/audio.h"
#include "dosbox/platform/input.h"
#include "dosbox/platform/timing.h"

namespace dosbox {
namespace platform {

/**
 * @brief Platform backend configuration.
 *
 * Groups all platform interfaces for easy management.
 */
struct PlatformBackend {
    IDisplay* display = nullptr;   ///< Display interface (required)
    IAudio* audio = nullptr;       ///< Audio interface (optional)
    IInput* input = nullptr;       ///< Input interface (optional)
    ITiming* timing = nullptr;     ///< Timing interface (required)

    /**
     * @brief Check if minimum required interfaces are set.
     */
    bool is_valid() const {
        return display != nullptr && timing != nullptr;
    }
};

/**
 * @brief Create a headless backend with null/virtual implementations.
 *
 * Useful for testing, AI agents, and server deployments.
 *
 * @return Platform backend with headless implementations
 *
 * @note Caller is responsible for managing lifetime of returned objects.
 */
inline PlatformBackend create_headless_backend() {
    static NullDisplay display;
    static NullAudio audio;
    static QueueInput input;
    static VirtualTiming timing;

    PlatformBackend backend;
    backend.display = &display;
    backend.audio = &audio;
    backend.input = &input;
    backend.timing = &timing;
    return backend;
}

} // namespace platform
} // namespace dosbox

#endif // DOSBOX_PLATFORM_PLATFORM_H
