/**
 * @file instance_state.h
 * @brief Per-instance state struct definitions (internal only)
 *
 * Extracted from the anonymous namespace in legends_embed_api.cpp
 * so that struct legends_instance can aggregate them and tests can
 * reference them.
 *
 * @warning INTERNAL HEADER - NOT part of the public API.
 *          Do not include from application code.
 */

#ifndef LEGENDS_INTERNAL_INSTANCE_STATE_H
#define LEGENDS_INTERNAL_INSTANCE_STATE_H

#include <array>
#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "legends/legends_embed.h"
#include "legends/vision_framebuffer.h"
#include "cp437_font_8x16.h"

namespace legends::internal {

// ============================================================================
// Log Level Constants
// ============================================================================

constexpr int LOG_LEVEL_ERROR = 0;
constexpr int LOG_LEVEL_WARN  = 1;
constexpr int LOG_LEVEL_INFO  = 2;
constexpr int LOG_LEVEL_DEBUG = 3;

// ============================================================================
// Log State
// ============================================================================

struct LogState {
    legends_log_callback_t callback = nullptr;
    void* userdata = nullptr;

    void reset() {
        callback = nullptr;
        userdata = nullptr;
    }

    void log(int level, const char* message) const {
        if (callback != nullptr && message != nullptr) {
            try {
                callback(level, message, userdata);
            } catch (...) {
                // Cannot propagate exceptions across C ABI boundary
            }
        }
    }

    void error(const char* message) const { log(LOG_LEVEL_ERROR, message); }
    void warn(const char* message) const { log(LOG_LEVEL_WARN, message); }
    void info(const char* message) const { log(LOG_LEVEL_INFO, message); }
    void debug(const char* message) const { log(LOG_LEVEL_DEBUG, message); }
};

// ============================================================================
// Time State
// ============================================================================

struct TimeState {
    uint64_t total_cycles = 0;
    uint64_t emu_time_us = 0;
    uint32_t cycles_per_ms = 3000;

    void reset() {
        total_cycles = 0;
        emu_time_us = 0;
    }

    uint64_t cycles_to_us(uint64_t cycles) const {
        return (cycles * 1000) / cycles_per_ms;
    }

    uint64_t ms_to_cycles(uint32_t ms) const {
        return static_cast<uint64_t>(ms) * cycles_per_ms;
    }
};

// ============================================================================
// Frame State
// ============================================================================

struct FrameState {
    bool is_text_mode = true;
    uint8_t columns = 80;
    uint8_t rows = 25;

    static constexpr size_t MAX_TEXT_CELLS = 80 * 50;
    std::array<uint16_t, MAX_TEXT_CELLS> text_buffer{};

    uint8_t cursor_x = 0;
    uint8_t cursor_y = 0;
    bool cursor_visible = true;
    uint8_t cursor_start = 6;
    uint8_t cursor_end = 7;
    uint8_t active_page = 0;

    uint16_t gfx_width = 320;
    uint16_t gfx_height = 200;
    std::vector<uint8_t> indexed_pixels;
    legends::vision::VgaPalette palette;

    std::vector<uint8_t> font_data;   // 256 × char_height bytes of 1bpp glyphs
    uint8_t char_height = 16;         // Scanlines per character (from engine)

    bool dirty = true;

    void reset() {
        is_text_mode = true;
        columns = 80;
        rows = 25;
        text_buffer.fill(0x0720);
        cursor_x = 0;
        cursor_y = 0;
        cursor_visible = true;
        cursor_start = 6;
        cursor_end = 7;
        active_page = 0;
        gfx_width = 320;
        gfx_height = 200;
        indexed_pixels.clear();
        palette = legends::vision::VgaPalette{};
        font_data.clear();
        char_height = 16;
        dirty = true;
    }

    void init_test_pattern() {
        for (size_t row = 0; row < rows; ++row) {
            for (size_t col = 0; col < columns; ++col) {
                size_t idx = row * columns + col;
                if (row == 0) {
                    const char* prompt = "C:\\>";
                    if (col < 4) {
                        text_buffer[idx] = static_cast<uint16_t>(prompt[col]) | 0x0700;
                    } else {
                        text_buffer[idx] = 0x0720;
                    }
                } else {
                    text_buffer[idx] = 0x0720;
                }
            }
        }
        cursor_x = 4;
        cursor_y = 0;
        dirty = true;
    }

    /// Load embedded CP437 8x16 font into font_data.
    /// Used as fallback when engine VGA font is not available.
    void load_embedded_font() {
        char_height = 16;
        font_data.assign(CP437_FONT_8x16.begin(), CP437_FONT_8x16.end());
    }

    [[nodiscard]] size_t text_cell_count() const noexcept {
        return static_cast<size_t>(columns) * rows;
    }

    [[nodiscard]] size_t rgb_buffer_size() const noexcept {
        return static_cast<size_t>(gfx_width) * gfx_height * 3;
    }
};

// ============================================================================
// Input Types and State
// ============================================================================

enum class InputEventType : uint8_t { Key = 0, Mouse = 1 };

struct InputEvent {
    InputEventType type;
    uint64_t sequence;

    struct KeyEventData {
        uint8_t scancode;
        bool is_down;
        bool is_extended;
    };

    struct MouseEventData {
        int16_t delta_x;
        int16_t delta_y;
        uint8_t buttons;
    };

    union {
        KeyEventData key;
        MouseEventData mouse;
    };
};

struct InputState {
    static constexpr size_t MAX_INPUT_EVENTS = 320;
    static constexpr size_t EFFECTIVE_CAPACITY = MAX_INPUT_EVENTS - 1;
    std::array<InputEvent, MAX_INPUT_EVENTS> queue{};
    size_t head = 0;
    size_t tail = 0;
    uint64_t next_sequence = 0;
    uint8_t mouse_buttons = 0;

    [[nodiscard]] size_t size() const noexcept {
        return (tail >= head) ? (tail - head) : (MAX_INPUT_EVENTS - head + tail);
    }

    [[nodiscard]] bool full() const noexcept {
        return size() >= EFFECTIVE_CAPACITY;
    }

    [[nodiscard]] bool empty() const noexcept {
        return head == tail;
    }

    bool enqueue_key(uint8_t scancode, bool is_down, bool is_extended) {
        if (full()) return false;
        auto& evt = queue[tail];
        evt.type = InputEventType::Key;
        evt.sequence = next_sequence++;
        evt.key.scancode = scancode;
        evt.key.is_down = is_down;
        evt.key.is_extended = is_extended;
        tail = (tail + 1) % MAX_INPUT_EVENTS;
        return true;
    }

    bool enqueue_mouse(int16_t dx, int16_t dy, uint8_t buttons) {
        if (full()) return false;
        auto& evt = queue[tail];
        evt.type = InputEventType::Mouse;
        evt.sequence = next_sequence++;
        evt.mouse.delta_x = dx;
        evt.mouse.delta_y = dy;
        evt.mouse.buttons = buttons;
        tail = (tail + 1) % MAX_INPUT_EVENTS;
        mouse_buttons = buttons;
        return true;
    }

    bool dequeue(InputEvent* out) {
        if (empty()) return false;
        *out = queue[head];
        head = (head + 1) % MAX_INPUT_EVENTS;
        return true;
    }

    bool peek(InputEvent* out) const {
        if (empty()) return false;
        *out = queue[head];
        return true;
    }

    void pop() {
        if (!empty()) {
            head = (head + 1) % MAX_INPUT_EVENTS;
        }
    }

    bool enqueue_raw(const InputEvent& evt) {
        if (full()) return false;
        queue[tail] = evt;
        tail = (tail + 1) % MAX_INPUT_EVENTS;
        if (evt.type == InputEventType::Mouse) {
            mouse_buttons = evt.mouse.buttons;
        }
        return true;
    }

    void clear() {
        head = tail = 0;
        next_sequence = 0;
        mouse_buttons = 0;
    }

    void reset() {
        clear();
    }
};

// ============================================================================
// Event Queue, PIC, DMA State
// ============================================================================

enum class EventKind : uint8_t {
    PIT_TICK = 0,
    KBD_SCAN = 1,
    DMA_TC = 2,
    TIMER_CB = 3,
    IRQ_CHECK = 4,
};

struct ScheduledEvent {
    uint32_t id;
    uint64_t deadline;
    EventKind kind;
    uint8_t payload;
    uint8_t tie_key;
    uint8_t _pad;
};

struct PICState {
    uint8_t irr;
    uint8_t imr;
    uint8_t isr;
    uint8_t vector_base;
    uint8_t cascade_irq;
    uint8_t _pad[3];
};

struct DMAChannelState {
    uint16_t count;
    uint8_t enabled : 1;
    uint8_t masked : 1;
    uint8_t request : 1;
    uint8_t tc_reached : 1;
    uint8_t autoinit : 1;
    uint8_t _pad : 3;
    uint8_t _pad2;
};

struct EventQueueState {
    static constexpr size_t MAX_EVENTS = 64;
    std::array<ScheduledEvent, MAX_EVENTS> events{};
    size_t event_count = 0;
    uint32_t next_event_id = 0;

    void reset() {
        event_count = 0;
        next_event_id = 0;
    }
};

// ============================================================================
// Wire Format Constants
// ============================================================================

constexpr size_t WIRE_INPUT_EVENT_SIZE = 24;
constexpr size_t WIRE_DMA_CHANNEL_SIZE = 4;

// ============================================================================
// Serialization Functions (implemented in legends_embed_api.cpp)
// ============================================================================

void serialize_input_event(uint8_t* dst, const InputEvent& evt);
InputEvent deserialize_input_event(const uint8_t* src);

} // namespace legends::internal

#endif // LEGENDS_INTERNAL_INSTANCE_STATE_H
