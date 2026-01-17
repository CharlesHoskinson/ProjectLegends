/**
 * @file legends_embed_internal.h
 * @brief Internal types exposed for testing only - NOT part of public API
 *
 * This header exposes internal implementation details from legends_embed_api.cpp
 * for unit testing purposes. It should NEVER be included in production code
 * outside of the legends layer or test code.
 *
 * @warning DO NOT use these types in application code. They may change
 *          without notice between versions.
 */

#ifndef LEGENDS_EMBED_INTERNAL_H
#define LEGENDS_EMBED_INTERNAL_H

#include <cstdint>
#include <cstddef>

namespace legends::internal {

// ============================================================================
// Wire Format Constants (must match legends_embed_api.cpp)
// ============================================================================

constexpr size_t WIRE_INPUT_EVENT_SIZE = 24;  // type(1) + pad(7) + sequence(8) + data(8)
constexpr size_t WIRE_DMA_CHANNEL_SIZE = 4;   // count(2) + flags(1) + pad(1)

// ============================================================================
// Input Event Types (must match legends_embed_api.cpp)
// ============================================================================

enum class InputEventType : uint8_t {
    Key = 0,
    Mouse = 1
};

struct InputEvent {
    InputEventType type;
    uint64_t sequence;
    union {
        struct {
            uint8_t scancode;
            bool is_down;
            bool is_extended;
        } key;
        struct {
            int16_t delta_x;
            int16_t delta_y;
            uint8_t buttons;
        } mouse;
    };
};

// ============================================================================
// Serialization Functions (for testing portable format)
// These are declared here but implemented in legends_embed_api.cpp
// Link against the legends library to use them in tests.
// ============================================================================

// Portable serialization for InputEvent
void serialize_input_event(uint8_t* dst, const InputEvent& evt);
InputEvent deserialize_input_event(const uint8_t* src);

// ============================================================================
// Capacity Constants
// ============================================================================

constexpr size_t MAX_INPUT_EVENTS = 320;
constexpr size_t EFFECTIVE_INPUT_CAPACITY = MAX_INPUT_EVENTS - 1;  // 319

} // namespace legends::internal

#endif // LEGENDS_EMBED_INTERNAL_H
