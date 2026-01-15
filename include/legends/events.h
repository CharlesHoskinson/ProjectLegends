/**
 * @file events.h
 * @brief Event type definitions for the Legends event system.
 *
 * Defines all event types used for communication between DOSBox-X
 * internal subsystems and external consumers. These types are designed
 * for zero-copy semantics within the same process.
 */

#pragma once

#include <cstdint>
#include <cstring>
#include <array>

namespace legends::events {

// ─────────────────────────────────────────────────────────────────────────────
// Text Mode Events
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Represents a single text mode cell.
 *
 * Contains character and attribute information for one cell in text mode.
 * The character is stored as a Unicode codepoint (converted from CP437).
 */
struct TextCell {
    char16_t character;    ///< Unicode character (converted from CP437)
    uint8_t  foreground;   ///< Foreground color (0-15)
    uint8_t  background;   ///< Background color (0-7, or 0-15 with blink disabled)
    bool     blink;        ///< Blink attribute

    [[nodiscard]] bool operator==(const TextCell& other) const noexcept {
        return character == other.character &&
               foreground == other.foreground &&
               background == other.background &&
               blink == other.blink;
    }

    [[nodiscard]] bool operator!=(const TextCell& other) const noexcept {
        return !(*this == other);
    }
};

static_assert(sizeof(TextCell) == 6, "TextCell should be 6 bytes");

/**
 * @brief Complete text mode screen state.
 *
 * Contains the full screen buffer plus cursor information.
 * Uses a fixed-size array for common 80x25 mode, with support
 * for other text modes via the flexible array approach.
 */
struct TextModeScreen {
    static constexpr size_t MaxCells = 80 * 50;  ///< Max supported: 80x50

    uint8_t  columns;           ///< Number of columns (typically 80)
    uint8_t  rows;              ///< Number of rows (typically 25)
    uint8_t  cursor_x;          ///< Cursor column position
    uint8_t  cursor_y;          ///< Cursor row position
    bool     cursor_visible;    ///< Cursor visibility
    uint64_t timestamp_us;      ///< Microseconds since emulator start

    std::array<TextCell, MaxCells> cells;  ///< Row-major cell array

    /**
     * @brief Get cell at specific position.
     * @param x Column (0-based)
     * @param y Row (0-based)
     * @return Reference to cell
     */
    [[nodiscard]] const TextCell& at(uint8_t x, uint8_t y) const noexcept {
        return cells[static_cast<size_t>(y) * columns + x];
    }

    [[nodiscard]] TextCell& at(uint8_t x, uint8_t y) noexcept {
        return cells[static_cast<size_t>(y) * columns + x];
    }

    /**
     * @brief Get total number of cells.
     */
    [[nodiscard]] size_t cell_count() const noexcept {
        return static_cast<size_t>(columns) * rows;
    }
};

/**
 * @brief A single cell change for differential updates.
 */
struct TextCellChange {
    uint16_t index;  ///< Cell index (row * columns + col)
    TextCell cell;   ///< New cell value
};

/**
 * @brief Differential text mode update (optimized).
 *
 * Instead of sending the full screen buffer, this event type
 * sends only the cells that have changed since the last update.
 */
struct TextModeDiff {
    static constexpr size_t MaxChanges = 256;  ///< Max changes per diff

    uint32_t frame_number;      ///< Frame sequence number
    uint8_t  cursor_x;          ///< Updated cursor column
    uint8_t  cursor_y;          ///< Updated cursor row
    bool     cursor_changed;    ///< True if cursor moved
    uint64_t timestamp_us;      ///< Microseconds since emulator start

    uint16_t changed_count;     ///< Number of changed cells
    std::array<TextCellChange, MaxChanges> changes;  ///< Array of changed cells

    /**
     * @brief Add a change to the diff.
     * @return true if added, false if full
     */
    bool add_change(uint16_t index, const TextCell& cell) noexcept {
        if (changed_count >= MaxChanges) {
            return false;
        }
        changes[changed_count].index = index;
        changes[changed_count].cell = cell;
        ++changed_count;
        return true;
    }

    /**
     * @brief Check if diff is full.
     */
    [[nodiscard]] bool is_full() const noexcept {
        return changed_count >= MaxChanges;
    }

    /**
     * @brief Clear all changes.
     */
    void clear() noexcept {
        changed_count = 0;
        cursor_changed = false;
    }
};

/**
 * @brief Text mode event types.
 */
enum class TextModeEventType : uint8_t {
    FullScreen,     ///< Complete screen refresh
    Differential,   ///< Only changed cells
    CursorMove,     ///< Cursor position changed only
    ModeChange      ///< Text mode parameters changed
};

// ─────────────────────────────────────────────────────────────────────────────
// Program Lifecycle Events
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief DOS program execution state.
 */
enum class ProgramState : uint8_t {
    Loading,        ///< Program being loaded into memory
    Started,        ///< Execution has begun
    Running,        ///< Actively executing
    Suspended,      ///< Waiting for input or I/O
    Terminating,    ///< Program is exiting
    Halted          ///< Program has stopped (normal or error)
};

/**
 * @brief Get string representation of ProgramState.
 */
[[nodiscard]] constexpr const char* to_string(ProgramState state) noexcept {
    switch (state) {
        case ProgramState::Loading:     return "Loading";
        case ProgramState::Started:     return "Started";
        case ProgramState::Running:     return "Running";
        case ProgramState::Suspended:   return "Suspended";
        case ProgramState::Terminating: return "Terminating";
        case ProgramState::Halted:      return "Halted";
    }
    return "Unknown";
}

/**
 * @brief Termination reason codes.
 */
enum class TerminationReason : uint8_t {
    NormalExit,     ///< INT 21h AH=4Ch or RET from main
    CtrlBreak,      ///< User pressed Ctrl+Break
    CriticalError,  ///< Critical error handler invoked
    Exception,      ///< CPU exception (divide by zero, etc.)
    ParentKill,     ///< Parent process terminated child
    Unknown         ///< Unexpected termination
};

/**
 * @brief Get string representation of TerminationReason.
 */
[[nodiscard]] constexpr const char* to_string(TerminationReason reason) noexcept {
    switch (reason) {
        case TerminationReason::NormalExit:     return "NormalExit";
        case TerminationReason::CtrlBreak:      return "CtrlBreak";
        case TerminationReason::CriticalError:  return "CriticalError";
        case TerminationReason::Exception:      return "Exception";
        case TerminationReason::ParentKill:     return "ParentKill";
        case TerminationReason::Unknown:        return "Unknown";
    }
    return "Unknown";
}

/**
 * @brief Program started event.
 *
 * Emitted when a DOS program begins execution.
 */
struct ProgramStartedEvent {
    static constexpr size_t MaxPathLength = 128;
    static constexpr size_t MaxArgsLength = 128;

    uint64_t timestamp_us;                        ///< Event timestamp
    uint16_t psp_segment;                         ///< Program Segment Prefix location
    uint16_t environment_seg;                     ///< Environment block segment
    uint32_t load_address;                        ///< Linear address where loaded
    uint32_t program_size;                        ///< Size in bytes

    std::array<char, MaxPathLength> path;         ///< DOS path to executable
    std::array<char, MaxArgsLength> arguments;    ///< Command line arguments

    /**
     * @brief Set the program path.
     */
    void set_path(const char* p) noexcept {
        if (p) {
            std::strncpy(path.data(), p, MaxPathLength - 1);
            path[MaxPathLength - 1] = '\0';
        } else {
            path[0] = '\0';
        }
    }

    /**
     * @brief Set the command line arguments.
     */
    void set_arguments(const char* args) noexcept {
        if (args) {
            std::strncpy(arguments.data(), args, MaxArgsLength - 1);
            arguments[MaxArgsLength - 1] = '\0';
        } else {
            arguments[0] = '\0';
        }
    }
};

/**
 * @brief Program halted event.
 *
 * Emitted when a DOS program terminates or is killed.
 */
struct ProgramHaltedEvent {
    static constexpr size_t MaxPathLength = 128;

    uint64_t          timestamp_us;         ///< Event timestamp
    ProgramState      final_state;          ///< Final state when halted
    TerminationReason reason;               ///< Why the program ended
    uint8_t           exit_code;            ///< Return code (0-255)
    uint32_t          instructions_executed; ///< Total instruction count
    uint32_t          runtime_ms;           ///< Wall-clock runtime in ms

    std::array<char, MaxPathLength> path;   ///< Path of terminated program

    /**
     * @brief Set the program path.
     */
    void set_path(const char* p) noexcept {
        if (p) {
            std::strncpy(path.data(), p, MaxPathLength - 1);
            path[MaxPathLength - 1] = '\0';
        } else {
            path[0] = '\0';
        }
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// Input Events
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Keyboard scan codes (AT set 1).
 *
 * Standard AT keyboard scan codes as used by DOS programs.
 */
enum class ScanCode : uint8_t {
    None = 0x00,
    Escape = 0x01,
    Key1 = 0x02, Key2 = 0x03, Key3 = 0x04, Key4 = 0x05,
    Key5 = 0x06, Key6 = 0x07, Key7 = 0x08, Key8 = 0x09,
    Key9 = 0x0A, Key0 = 0x0B, Minus = 0x0C, Equals = 0x0D,
    Backspace = 0x0E, Tab = 0x0F,
    Q = 0x10, W = 0x11, E = 0x12, R = 0x13, T = 0x14,
    Y = 0x15, U = 0x16, I = 0x17, O = 0x18, P = 0x19,
    LeftBracket = 0x1A, RightBracket = 0x1B, Enter = 0x1C,
    LeftCtrl = 0x1D,
    A = 0x1E, S = 0x1F, D = 0x20, F = 0x21, G = 0x22,
    H = 0x23, J = 0x24, K = 0x25, L = 0x26,
    Semicolon = 0x27, Quote = 0x28, Backtick = 0x29,
    LeftShift = 0x2A, Backslash = 0x2B,
    Z = 0x2C, X = 0x2D, C = 0x2E, V = 0x2F, B = 0x30,
    N = 0x31, M = 0x32, Comma = 0x33, Period = 0x34,
    Slash = 0x35, RightShift = 0x36,
    NumpadMultiply = 0x37, LeftAlt = 0x38, Space = 0x39,
    CapsLock = 0x3A,
    F1 = 0x3B, F2 = 0x3C, F3 = 0x3D, F4 = 0x3E,
    F5 = 0x3F, F6 = 0x40, F7 = 0x41, F8 = 0x42,
    F9 = 0x43, F10 = 0x44,
    NumLock = 0x45, ScrollLock = 0x46,
    Numpad7 = 0x47, Numpad8 = 0x48, Numpad9 = 0x49,
    NumpadMinus = 0x4A,
    Numpad4 = 0x4B, Numpad5 = 0x4C, Numpad6 = 0x4D,
    NumpadPlus = 0x4E,
    Numpad1 = 0x4F, Numpad2 = 0x50, Numpad3 = 0x51,
    Numpad0 = 0x52, NumpadPeriod = 0x53,
    F11 = 0x57, F12 = 0x58,

    // Extended keys (use with is_extended flag)
    Extended = 0xE0
};

/**
 * @brief Keyboard modifier flags.
 */
enum class KeyModifiers : uint8_t {
    None  = 0,
    Shift = 1 << 0,
    Ctrl  = 1 << 1,
    Alt   = 1 << 2
};

/**
 * @brief Combine modifier flags.
 */
[[nodiscard]] constexpr KeyModifiers operator|(KeyModifiers a, KeyModifiers b) noexcept {
    return static_cast<KeyModifiers>(
        static_cast<uint8_t>(a) | static_cast<uint8_t>(b));
}

[[nodiscard]] constexpr KeyModifiers operator&(KeyModifiers a, KeyModifiers b) noexcept {
    return static_cast<KeyModifiers>(
        static_cast<uint8_t>(a) & static_cast<uint8_t>(b));
}

/**
 * @brief Check if modifier is set.
 */
[[nodiscard]] constexpr bool has_modifier(KeyModifiers mods, KeyModifiers flag) noexcept {
    return (static_cast<uint8_t>(mods) & static_cast<uint8_t>(flag)) != 0;
}

/**
 * @brief Keyboard event.
 *
 * Represents a key press or release event.
 */
struct KeyboardEvent {
    uint64_t     timestamp_us;   ///< Event timestamp
    ScanCode     scan_code;      ///< Scan code of the key
    bool         is_pressed;     ///< true = key down, false = key up
    bool         is_extended;    ///< true = has 0xE0 prefix
    KeyModifiers modifiers;      ///< Current modifier state
};

/**
 * @brief Mouse button flags.
 */
enum class MouseButtons : uint8_t {
    None   = 0,
    Left   = 1 << 0,
    Right  = 1 << 1,
    Middle = 1 << 2
};

/**
 * @brief Combine button flags.
 */
[[nodiscard]] constexpr MouseButtons operator|(MouseButtons a, MouseButtons b) noexcept {
    return static_cast<MouseButtons>(
        static_cast<uint8_t>(a) | static_cast<uint8_t>(b));
}

[[nodiscard]] constexpr MouseButtons operator&(MouseButtons a, MouseButtons b) noexcept {
    return static_cast<MouseButtons>(
        static_cast<uint8_t>(a) & static_cast<uint8_t>(b));
}

/**
 * @brief Check if button is pressed.
 */
[[nodiscard]] constexpr bool has_button(MouseButtons buttons, MouseButtons flag) noexcept {
    return (static_cast<uint8_t>(buttons) & static_cast<uint8_t>(flag)) != 0;
}

/**
 * @brief Mouse event.
 *
 * Represents mouse movement or button state change.
 */
struct MouseEvent {
    uint64_t     timestamp_us;   ///< Event timestamp
    int16_t      delta_x;        ///< Relative X movement
    int16_t      delta_y;        ///< Relative Y movement
    int8_t       wheel_delta;    ///< Scroll wheel movement
    MouseButtons buttons;        ///< Current button state
    MouseButtons changed;        ///< Buttons that changed this event
};

// ─────────────────────────────────────────────────────────────────────────────
// Event Type Enumeration
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief All event types in the system.
 */
enum class EventType : uint8_t {
    TextScreen,         ///< Full text mode screen
    TextDiff,           ///< Differential text mode update
    ProgramStarted,     ///< Program started execution
    ProgramHalted,      ///< Program terminated
    Keyboard,           ///< Keyboard input
    Mouse               ///< Mouse input
};

/**
 * @brief Get string representation of EventType.
 */
[[nodiscard]] constexpr const char* to_string(EventType type) noexcept {
    switch (type) {
        case EventType::TextScreen:     return "TextScreen";
        case EventType::TextDiff:       return "TextDiff";
        case EventType::ProgramStarted: return "ProgramStarted";
        case EventType::ProgramHalted:  return "ProgramHalted";
        case EventType::Keyboard:       return "Keyboard";
        case EventType::Mouse:          return "Mouse";
    }
    return "Unknown";
}

} // namespace legends::events
