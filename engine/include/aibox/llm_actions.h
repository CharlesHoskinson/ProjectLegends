/**
 * @file llm_actions.h
 * @brief Action vocabulary for LLM interaction with DOSBox-X.
 *
 * Defines a simple, unambiguous action vocabulary that LLMs can use
 * to control the emulator: type, click, wait, hypercall, special_key.
 */

#pragma once

#include "llm_frame.h"

#include <cstdint>
#include <optional>
#include <string>
#include <variant>
#include <vector>

namespace aibox::llm {

// ─────────────────────────────────────────────────────────────────────────────
// Action Types
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Type action: inject keystrokes.
 *
 * Simulates typing a string of characters. Supports escape sequences:
 * - \\n for Enter
 * - \\t for Tab
 * - \\\\ for backslash
 */
struct TypeAction {
    std::string text;              ///< Text to type
    uint32_t delay_between_ms{0};  ///< Delay between keystrokes (default: 0)

    [[nodiscard]] bool operator==(const TypeAction& other) const noexcept {
        return text == other.text && delay_between_ms == other.delay_between_ms;
    }

    [[nodiscard]] bool operator!=(const TypeAction& other) const noexcept {
        return !(*this == other);
    }
};

/**
 * @brief Mouse button identifier.
 */
enum class MouseButton : uint8_t {
    Left = 0,
    Right = 1,
    Middle = 2
};

/**
 * @brief Convert MouseButton to string.
 */
[[nodiscard]] constexpr const char* to_string(MouseButton button) noexcept {
    switch (button) {
        case MouseButton::Left:   return "left";
        case MouseButton::Right:  return "right";
        case MouseButton::Middle: return "middle";
        default:                  return "unknown";
    }
}

/**
 * @brief Click action: mouse click at position.
 */
struct ClickAction {
    int16_t x{0};                           ///< X coordinate
    int16_t y{0};                           ///< Y coordinate
    MouseButton button{MouseButton::Left};  ///< Button to click
    bool double_click{false};               ///< True for double-click
    bool text_coordinates{true};            ///< True if x,y are text cell coordinates

    [[nodiscard]] bool operator==(const ClickAction& other) const noexcept {
        return x == other.x && y == other.y &&
               button == other.button &&
               double_click == other.double_click &&
               text_coordinates == other.text_coordinates;
    }

    [[nodiscard]] bool operator!=(const ClickAction& other) const noexcept {
        return !(*this == other);
    }
};

/**
 * @brief Wait action: advance emulation time.
 */
struct WaitAction {
    uint32_t milliseconds{0};    ///< Time to wait
    bool wait_for_idle{false};   ///< True to wait until CPU idle

    [[nodiscard]] bool operator==(const WaitAction& other) const noexcept {
        return milliseconds == other.milliseconds && wait_for_idle == other.wait_for_idle;
    }

    [[nodiscard]] bool operator!=(const WaitAction& other) const noexcept {
        return !(*this == other);
    }
};

/**
 * @brief Hypercall action: trigger hypercall to host.
 */
struct HypercallAction {
    uint16_t command_id{0};          ///< Command ID
    uint32_t param_a{0};             ///< Parameter A
    uint32_t param_b{0};             ///< Parameter B
    bool wait_for_response{true};    ///< True to block until status available

    [[nodiscard]] bool operator==(const HypercallAction& other) const noexcept {
        return command_id == other.command_id &&
               param_a == other.param_a &&
               param_b == other.param_b &&
               wait_for_response == other.wait_for_response;
    }

    [[nodiscard]] bool operator!=(const HypercallAction& other) const noexcept {
        return !(*this == other);
    }
};

/**
 * @brief Special key enumeration.
 */
enum class SpecialKey : uint8_t {
    Enter = 0,
    Escape,
    Tab,
    Backspace,
    Up,
    Down,
    Left,
    Right,
    Home,
    End,
    PageUp,
    PageDown,
    Insert,
    Delete,
    F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12,
    CtrlC,
    CtrlZ,
    CtrlBreak,
    AltF4,
    AltEnter
};

/**
 * @brief Convert SpecialKey to string.
 */
[[nodiscard]] constexpr const char* to_string(SpecialKey key) noexcept {
    switch (key) {
        case SpecialKey::Enter:     return "Enter";
        case SpecialKey::Escape:    return "Escape";
        case SpecialKey::Tab:       return "Tab";
        case SpecialKey::Backspace: return "Backspace";
        case SpecialKey::Up:        return "Up";
        case SpecialKey::Down:      return "Down";
        case SpecialKey::Left:      return "Left";
        case SpecialKey::Right:     return "Right";
        case SpecialKey::Home:      return "Home";
        case SpecialKey::End:       return "End";
        case SpecialKey::PageUp:    return "PageUp";
        case SpecialKey::PageDown:  return "PageDown";
        case SpecialKey::Insert:    return "Insert";
        case SpecialKey::Delete:    return "Delete";
        case SpecialKey::F1:        return "F1";
        case SpecialKey::F2:        return "F2";
        case SpecialKey::F3:        return "F3";
        case SpecialKey::F4:        return "F4";
        case SpecialKey::F5:        return "F5";
        case SpecialKey::F6:        return "F6";
        case SpecialKey::F7:        return "F7";
        case SpecialKey::F8:        return "F8";
        case SpecialKey::F9:        return "F9";
        case SpecialKey::F10:       return "F10";
        case SpecialKey::F11:       return "F11";
        case SpecialKey::F12:       return "F12";
        case SpecialKey::CtrlC:     return "CtrlC";
        case SpecialKey::CtrlZ:     return "CtrlZ";
        case SpecialKey::CtrlBreak: return "CtrlBreak";
        case SpecialKey::AltF4:     return "AltF4";
        case SpecialKey::AltEnter:  return "AltEnter";
        default:                    return "Unknown";
    }
}

/**
 * @brief Parse special key from string.
 *
 * @param name Key name (case-insensitive)
 * @return Parsed key or nullopt if invalid
 */
[[nodiscard]] std::optional<SpecialKey> parse_special_key(const std::string& name);

/**
 * @brief Get scancode for special key.
 *
 * @param key Special key
 * @param[out] extended True if key requires E0 prefix
 * @return Scancode value
 */
[[nodiscard]] uint8_t get_scancode(SpecialKey key, bool& extended) noexcept;

/**
 * @brief Special key action: send special key combination.
 */
struct SpecialKeyAction {
    SpecialKey key{SpecialKey::Enter};

    [[nodiscard]] bool operator==(const SpecialKeyAction& other) const noexcept {
        return key == other.key;
    }

    [[nodiscard]] bool operator!=(const SpecialKeyAction& other) const noexcept {
        return !(*this == other);
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// Action Variant
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Action variant type.
 */
using Action = std::variant<
    TypeAction,
    ClickAction,
    WaitAction,
    HypercallAction,
    SpecialKeyAction
>;

/**
 * @brief Action type enumeration.
 */
enum class ActionType : uint8_t {
    Type = 0,
    Click = 1,
    Wait = 2,
    Hypercall = 3,
    SpecialKey = 4
};

/**
 * @brief Convert ActionType to string.
 */
[[nodiscard]] constexpr const char* to_string(ActionType type) noexcept {
    switch (type) {
        case ActionType::Type:       return "type";
        case ActionType::Click:      return "click";
        case ActionType::Wait:       return "wait";
        case ActionType::Hypercall:  return "hypercall";
        case ActionType::SpecialKey: return "special_key";
        default:                     return "unknown";
    }
}

/**
 * @brief Get the type of an action.
 */
[[nodiscard]] inline ActionType get_action_type(const Action& action) noexcept {
    return std::visit([](auto&& arg) -> ActionType {
        using T = std::decay_t<decltype(arg)>;
        if constexpr (std::is_same_v<T, TypeAction>) {
            return ActionType::Type;
        } else if constexpr (std::is_same_v<T, ClickAction>) {
            return ActionType::Click;
        } else if constexpr (std::is_same_v<T, WaitAction>) {
            return ActionType::Wait;
        } else if constexpr (std::is_same_v<T, HypercallAction>) {
            return ActionType::Hypercall;
        } else if constexpr (std::is_same_v<T, SpecialKeyAction>) {
            return ActionType::SpecialKey;
        } else {
            return ActionType::Type;  // Fallback
        }
    }, action);
}

// ─────────────────────────────────────────────────────────────────────────────
// Action Result
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Action execution status.
 */
enum class ActionStatus : uint8_t {
    Success = 0,
    Error = 1,
    Timeout = 2,
    Skipped = 3
};

/**
 * @brief Convert ActionStatus to string.
 */
[[nodiscard]] constexpr const char* to_string(ActionStatus status) noexcept {
    switch (status) {
        case ActionStatus::Success: return "ok";
        case ActionStatus::Error:   return "error";
        case ActionStatus::Timeout: return "timeout";
        case ActionStatus::Skipped: return "skipped";
        default:                    return "unknown";
    }
}

/**
 * @brief Action execution result.
 */
struct ActionResult {
    size_t action_index{0};           ///< Index in batch
    ActionStatus status{ActionStatus::Success};  ///< Execution status
    std::string error_message;        ///< Error message (empty if success)
    uint64_t duration_us{0};          ///< Execution time in microseconds

    [[nodiscard]] bool success() const noexcept {
        return status == ActionStatus::Success;
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// Action Batch
// ─────────────────────────────────────────────────────────────────────────────

/// Maximum actions in a single batch
constexpr size_t MaxBatchSize = 100;

/// Maximum text length for type action
constexpr size_t MaxTypeLength = 1024;

/// Default timeout for batch execution
constexpr uint32_t DefaultTimeoutMs = 5000;

/// Maximum timeout for batch execution
constexpr uint32_t MaxTimeoutMs = 60000;

/**
 * @brief Batch action request.
 */
struct ActionBatch {
    std::vector<Action> actions;      ///< Actions to execute
    uint32_t timeout_ms{DefaultTimeoutMs};  ///< Max total execution time
    bool return_frame{true};          ///< Include frame in response
    bool stop_on_error{true};         ///< Stop batch on first error

    /**
     * @brief Validate the batch.
     *
     * @return Error message or nullopt if valid
     */
    [[nodiscard]] std::optional<std::string> validate() const;

    /**
     * @brief Parse from JSON.
     *
     * @param json JSON string
     * @return Parsed batch or error message
     */
    [[nodiscard]] static std::variant<ActionBatch, std::string> from_json(
        const std::string& json
    );
};

// ─────────────────────────────────────────────────────────────────────────────
// Batch Response
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Batch action response.
 */
struct ActionBatchResponse {
    bool success{true};                       ///< True if all actions succeeded
    std::vector<ActionResult> results;        ///< Per-action results
    std::optional<TokenEfficientFrame> frame; ///< Frame (if requested)
    uint64_t total_duration_us{0};            ///< Total execution time

    /**
     * @brief Serialize to JSON.
     */
    [[nodiscard]] std::string to_json() const;

    /**
     * @brief Get number of successful actions.
     */
    [[nodiscard]] size_t success_count() const noexcept;

    /**
     * @brief Get first error result (if any).
     */
    [[nodiscard]] const ActionResult* first_error() const noexcept;
};

// ─────────────────────────────────────────────────────────────────────────────
// Character to Scancode Conversion
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Scancode event (press or release).
 */
struct ScancodeEvent {
    uint8_t scancode{0};   ///< Scancode value
    bool pressed{true};    ///< True for key press, false for release
    bool extended{false};  ///< True if E0 prefix required
};

/**
 * @brief Convert a character to scancode sequence.
 *
 * @param c Character to convert
 * @return Sequence of scancode events (may include shift)
 */
[[nodiscard]] std::vector<ScancodeEvent> char_to_scancodes(char c);

/**
 * @brief Convert a string to scancode sequence.
 *
 * @param text Text to convert
 * @return Sequence of scancode events
 */
[[nodiscard]] std::vector<ScancodeEvent> text_to_scancodes(const std::string& text);

/**
 * @brief Convert special key to scancode sequence.
 *
 * @param key Special key
 * @return Sequence of scancode events
 */
[[nodiscard]] std::vector<ScancodeEvent> special_key_to_scancodes(SpecialKey key);

} // namespace aibox::llm
