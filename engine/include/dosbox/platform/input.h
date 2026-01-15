/**
 * @file input.h
 * @brief Platform-agnostic input interface for DOSBox library mode.
 *
 * This interface abstracts keyboard, mouse, and joystick input, allowing
 * DOSBox to run headless (programmatic input) or with different backends.
 *
 * ## Design Principles
 * 1. **Event-Based**: Input events are queued and processed during step()
 * 2. **Determinism**: Events are timestamped for replay
 * 3. **No SDL Dependencies**: Pure C++ interface
 *
 * ## Input Flow
 * ```
 * Host Input ──> IInput::push_event() ──> Event Queue ──> Emulation processes
 *                                                         during step()
 * ```
 *
 * ## Usage
 * ```cpp
 * // Programmatic input (AI agents, testing)
 * input->push_key(KeyCode::A, true);   // Press A
 * input->push_key(KeyCode::A, false);  // Release A
 *
 * // Mouse input
 * input->push_mouse_motion(10, -5);    // Relative motion
 * input->push_mouse_button(MouseButton::Left, true);
 * ```
 *
 * @copyright GPL-2.0-or-later
 */

#ifndef DOSBOX_PLATFORM_INPUT_H
#define DOSBOX_PLATFORM_INPUT_H

#include <cstdint>
#include <cstddef>
#include <optional>
#include <queue>

namespace dosbox {
namespace platform {

// ═══════════════════════════════════════════════════════════════════════════════
// Key Codes
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Platform-independent key codes.
 *
 * Based on USB HID scan codes for consistency across platforms.
 * Maps directly to DOS scan codes internally.
 */
enum class KeyCode : uint16_t {
    Unknown = 0,

    // Letters
    A = 4, B = 5, C = 6, D = 7, E = 8, F = 9, G = 10, H = 11,
    I = 12, J = 13, K = 14, L = 15, M = 16, N = 17, O = 18, P = 19,
    Q = 20, R = 21, S = 22, T = 23, U = 24, V = 25, W = 26, X = 27,
    Y = 28, Z = 29,

    // Numbers
    Num1 = 30, Num2 = 31, Num3 = 32, Num4 = 33, Num5 = 34,
    Num6 = 35, Num7 = 36, Num8 = 37, Num9 = 38, Num0 = 39,

    // Function keys
    Return = 40, Escape = 41, Backspace = 42, Tab = 43, Space = 44,

    // Punctuation
    Minus = 45, Equals = 46, LeftBracket = 47, RightBracket = 48,
    Backslash = 49, Semicolon = 51, Apostrophe = 52,
    Grave = 53, Comma = 54, Period = 55, Slash = 56,

    // Lock keys
    CapsLock = 57, NumLock = 83, ScrollLock = 71,

    // Function keys F1-F12
    F1 = 58, F2 = 59, F3 = 60, F4 = 61, F5 = 62, F6 = 63,
    F7 = 64, F8 = 65, F9 = 66, F10 = 67, F11 = 68, F12 = 69,

    // Navigation
    PrintScreen = 70, Pause = 72, Insert = 73, Home = 74,
    PageUp = 75, Delete = 76, End = 77, PageDown = 78,
    Right = 79, Left = 80, Down = 81, Up = 82,

    // Numpad
    KpDivide = 84, KpMultiply = 85, KpMinus = 86, KpPlus = 87,
    KpEnter = 88, Kp1 = 89, Kp2 = 90, Kp3 = 91, Kp4 = 92,
    Kp5 = 93, Kp6 = 94, Kp7 = 95, Kp8 = 96, Kp9 = 97,
    Kp0 = 98, KpPeriod = 99,

    // Modifiers
    LeftControl = 224, LeftShift = 225, LeftAlt = 226, LeftGui = 227,
    RightControl = 228, RightShift = 229, RightAlt = 230, RightGui = 231,
};

/**
 * @brief Modifier key flags (bitfield).
 */
enum class KeyMod : uint16_t {
    None = 0,
    LeftShift = 1 << 0,
    RightShift = 1 << 1,
    LeftCtrl = 1 << 2,
    RightCtrl = 1 << 3,
    LeftAlt = 1 << 4,
    RightAlt = 1 << 5,
    LeftGui = 1 << 6,
    RightGui = 1 << 7,
    NumLock = 1 << 8,
    CapsLock = 1 << 9,
    ScrollLock = 1 << 10,

    // Convenience combinations
    Shift = LeftShift | RightShift,
    Ctrl = LeftCtrl | RightCtrl,
    Alt = LeftAlt | RightAlt,
    Gui = LeftGui | RightGui,
};

inline KeyMod operator|(KeyMod a, KeyMod b) {
    return static_cast<KeyMod>(static_cast<uint16_t>(a) | static_cast<uint16_t>(b));
}

inline KeyMod operator&(KeyMod a, KeyMod b) {
    return static_cast<KeyMod>(static_cast<uint16_t>(a) & static_cast<uint16_t>(b));
}

inline bool has_mod(KeyMod mods, KeyMod flag) {
    return (mods & flag) != KeyMod::None;
}

// ═══════════════════════════════════════════════════════════════════════════════
// Mouse
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Mouse button enumeration.
 */
enum class MouseButton : uint8_t {
    Left = 0,
    Middle = 1,
    Right = 2,
    X1 = 3,
    X2 = 4,
};

// ═══════════════════════════════════════════════════════════════════════════════
// Input Events
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Input event type.
 */
enum class InputEventType : uint8_t {
    KeyDown,
    KeyUp,
    MouseMotion,
    MouseButtonDown,
    MouseButtonUp,
    MouseWheel,
    JoystickAxis,
    JoystickButton,
};

/**
 * @brief Unified input event structure.
 *
 * Tagged union for all input event types.
 */
struct InputEvent {
    InputEventType type;
    uint64_t timestamp = 0;  ///< Emulation cycle when event should be processed

    union {
        struct {
            KeyCode code;
            KeyMod mods;
            bool repeat;     ///< True if key repeat (not initial press)
        } key;

        struct {
            int16_t dx;      ///< Relative X motion
            int16_t dy;      ///< Relative Y motion
        } mouse_motion;

        struct {
            MouseButton button;
            int16_t x;       ///< Position at click (optional)
            int16_t y;
        } mouse_button;

        struct {
            int16_t dx;      ///< Horizontal scroll
            int16_t dy;      ///< Vertical scroll
        } mouse_wheel;

        struct {
            uint8_t joystick_id;
            uint8_t axis;
            int16_t value;   ///< -32768 to 32767
        } joystick_axis;

        struct {
            uint8_t joystick_id;
            uint8_t button;
            bool pressed;
        } joystick_button;
    };

    // ─────────────────────────────────────────────────────────────────────────
    // Factory methods for creating events
    // ─────────────────────────────────────────────────────────────────────────

    static InputEvent key_down(KeyCode code, KeyMod mods = KeyMod::None, bool repeat = false) {
        InputEvent e;
        e.type = InputEventType::KeyDown;
        e.key.code = code;
        e.key.mods = mods;
        e.key.repeat = repeat;
        return e;
    }

    static InputEvent key_up(KeyCode code, KeyMod mods = KeyMod::None) {
        InputEvent e;
        e.type = InputEventType::KeyUp;
        e.key.code = code;
        e.key.mods = mods;
        e.key.repeat = false;
        return e;
    }

    static InputEvent motion(int16_t dx, int16_t dy) {
        InputEvent e;
        e.type = InputEventType::MouseMotion;
        e.mouse_motion.dx = dx;
        e.mouse_motion.dy = dy;
        return e;
    }

    static InputEvent button_down(MouseButton button, int16_t x = 0, int16_t y = 0) {
        InputEvent e;
        e.type = InputEventType::MouseButtonDown;
        e.mouse_button.button = button;
        e.mouse_button.x = x;
        e.mouse_button.y = y;
        return e;
    }

    static InputEvent button_up(MouseButton button, int16_t x = 0, int16_t y = 0) {
        InputEvent e;
        e.type = InputEventType::MouseButtonUp;
        e.mouse_button.button = button;
        e.mouse_button.x = x;
        e.mouse_button.y = y;
        return e;
    }

    static InputEvent wheel(int16_t dx, int16_t dy) {
        InputEvent e;
        e.type = InputEventType::MouseWheel;
        e.mouse_wheel.dx = dx;
        e.mouse_wheel.dy = dy;
        return e;
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
// Input Interface
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Abstract input interface for DOSBox.
 *
 * Implementations:
 * - QueueInput: Basic queue (programmatic input)
 * - SDL2Input: Pumps SDL2 events
 *
 * ## Thread Safety
 * - push_*() methods: Thread-safe (can be called from any thread)
 * - poll_event(): Call from emulation thread only
 */
class IInput {
public:
    virtual ~IInput() = default;

    // ─────────────────────────────────────────────────────────────────────────
    // Event Queue
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Push a raw input event.
     *
     * @param event The event to queue
     */
    virtual void push_event(const InputEvent& event) = 0;

    /**
     * @brief Poll the next input event.
     *
     * Called by the emulation during step() to process input.
     *
     * @return Next event, or nullopt if queue is empty
     */
    virtual std::optional<InputEvent> poll_event() = 0;

    /**
     * @brief Check if there are pending events.
     */
    virtual bool has_events() const = 0;

    /**
     * @brief Clear all pending events.
     */
    virtual void clear() = 0;

    // ─────────────────────────────────────────────────────────────────────────
    // Convenience Methods
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Push a key press/release.
     */
    void push_key(KeyCode code, bool pressed, KeyMod mods = KeyMod::None) {
        if (pressed) {
            push_event(InputEvent::key_down(code, mods));
        } else {
            push_event(InputEvent::key_up(code, mods));
        }
    }

    /**
     * @brief Push mouse relative motion.
     */
    void push_mouse_motion(int16_t dx, int16_t dy) {
        push_event(InputEvent::motion(dx, dy));
    }

    /**
     * @brief Push mouse button press/release.
     */
    void push_mouse_button(MouseButton button, bool pressed) {
        if (pressed) {
            push_event(InputEvent::button_down(button));
        } else {
            push_event(InputEvent::button_up(button));
        }
    }

    /**
     * @brief Push mouse wheel event.
     */
    void push_mouse_wheel(int16_t dy) {
        push_event(InputEvent::wheel(0, dy));
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Input Capture State
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Check if mouse is captured (relative mode).
     */
    virtual bool is_mouse_captured() const { return false; }

    /**
     * @brief Set mouse capture state.
     */
    virtual void set_mouse_captured(bool captured) { (void)captured; }

    /**
     * @brief Get current modifier key state.
     */
    virtual KeyMod get_modifiers() const { return KeyMod::None; }
};

// ═══════════════════════════════════════════════════════════════════════════════
// Queue Input (Basic implementation)
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Simple queue-based input implementation.
 *
 * Useful for programmatic input injection (testing, AI agents).
 * Not thread-safe; use mutex if calling from multiple threads.
 */
class QueueInput : public IInput {
public:
    void push_event(const InputEvent& event) override {
        events_.push(event);
    }

    std::optional<InputEvent> poll_event() override {
        if (events_.empty()) {
            return std::nullopt;
        }
        InputEvent event = events_.front();
        events_.pop();
        return event;
    }

    bool has_events() const override {
        return !events_.empty();
    }

    void clear() override {
        while (!events_.empty()) {
            events_.pop();
        }
    }

    bool is_mouse_captured() const override {
        return mouse_captured_;
    }

    void set_mouse_captured(bool captured) override {
        mouse_captured_ = captured;
    }

    KeyMod get_modifiers() const override {
        return modifiers_;
    }

    void set_modifiers(KeyMod mods) {
        modifiers_ = mods;
    }

    size_t queue_size() const {
        return events_.size();
    }

private:
    std::queue<InputEvent> events_;
    bool mouse_captured_ = false;
    KeyMod modifiers_ = KeyMod::None;
};

} // namespace platform
} // namespace dosbox

#endif // DOSBOX_PLATFORM_INPUT_H
