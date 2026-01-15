/**
 * @file llm_frame.h
 * @brief Token-efficient frame representation for LLM consumption.
 *
 * Provides structures optimized for LLM interaction with DOSBox-X.
 * Prioritizes token efficiency, clear serialization, and batch operations.
 */

#pragma once

#include <cstdint>
#include <optional>
#include <string>
#include <vector>

namespace aibox::llm {

// ─────────────────────────────────────────────────────────────────────────────
// Video Mode
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Video mode indicator for LLM.
 */
enum class VideoMode : uint8_t {
    Text40x25 = 0,       ///< 40-column text mode
    Text80x25 = 1,       ///< Standard 80-column text mode
    Text80x43 = 2,       ///< EGA 43-line mode
    Text80x50 = 3,       ///< VGA 50-line mode
    Graphics320x200 = 4, ///< CGA/EGA/VGA low-res graphics
    Graphics640x480 = 5, ///< VGA high-res graphics
    Unknown = 255
};

/**
 * @brief Convert VideoMode to string.
 */
[[nodiscard]] constexpr const char* to_string(VideoMode mode) noexcept {
    switch (mode) {
        case VideoMode::Text40x25:       return "Text40x25";
        case VideoMode::Text80x25:       return "Text80x25";
        case VideoMode::Text80x43:       return "Text80x43";
        case VideoMode::Text80x50:       return "Text80x50";
        case VideoMode::Graphics320x200: return "Graphics320x200";
        case VideoMode::Graphics640x480: return "Graphics640x480";
        case VideoMode::Unknown:         return "Unknown";
        default:                         return "Unknown";
    }
}

/**
 * @brief Get columns for a video mode.
 */
[[nodiscard]] constexpr uint8_t get_columns(VideoMode mode) noexcept {
    switch (mode) {
        case VideoMode::Text40x25:       return 40;
        case VideoMode::Text80x25:       return 80;
        case VideoMode::Text80x43:       return 80;
        case VideoMode::Text80x50:       return 80;
        case VideoMode::Graphics320x200: return 40;  // Approximate text equivalent
        case VideoMode::Graphics640x480: return 80;
        default:                         return 80;
    }
}

/**
 * @brief Get rows for a video mode.
 */
[[nodiscard]] constexpr uint8_t get_rows(VideoMode mode) noexcept {
    switch (mode) {
        case VideoMode::Text40x25:       return 25;
        case VideoMode::Text80x25:       return 25;
        case VideoMode::Text80x43:       return 43;
        case VideoMode::Text80x50:       return 50;
        case VideoMode::Graphics320x200: return 25;
        case VideoMode::Graphics640x480: return 30;
        default:                         return 25;
    }
}

/**
 * @brief Check if mode is a text mode.
 */
[[nodiscard]] constexpr bool is_text_mode(VideoMode mode) noexcept {
    return mode == VideoMode::Text40x25 ||
           mode == VideoMode::Text80x25 ||
           mode == VideoMode::Text80x43 ||
           mode == VideoMode::Text80x50;
}

// ─────────────────────────────────────────────────────────────────────────────
// Cursor State
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Cursor state information.
 */
struct CursorState {
    uint8_t column{0};       ///< Column position (0-based)
    uint8_t row{0};          ///< Row position (0-based)
    bool visible{true};      ///< Whether cursor is visible
    bool blink_phase{true};  ///< True if cursor currently visible in blink cycle

    [[nodiscard]] bool operator==(const CursorState& other) const noexcept {
        return column == other.column &&
               row == other.row &&
               visible == other.visible &&
               blink_phase == other.blink_phase;
    }

    [[nodiscard]] bool operator!=(const CursorState& other) const noexcept {
        return !(*this == other);
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// Input Queue Status
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Input queue status for LLM awareness.
 */
struct InputQueueStatus {
    uint8_t pending_keystrokes{0};      ///< Number of pending keystrokes
    uint8_t pending_mouse_events{0};    ///< Number of pending mouse events
    std::optional<uint8_t> last_scancode;       ///< Last scancode (if any)
    std::optional<std::string> last_key_name;   ///< Human-readable key name

    [[nodiscard]] bool has_pending() const noexcept {
        return pending_keystrokes > 0 || pending_mouse_events > 0;
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// Hypercall Log Entry
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Hypercall log entry for LLM tracking.
 */
struct HypercallLogEntry {
    uint64_t timestamp_us{0};   ///< Timestamp in microseconds
    uint16_t command_id{0};     ///< Command ID
    uint32_t param_a{0};        ///< Parameter A
    uint32_t param_b{0};        ///< Parameter B
    uint32_t status{0};         ///< Status returned
    bool success{false};        ///< Whether hypercall succeeded

    [[nodiscard]] bool operator==(const HypercallLogEntry& other) const noexcept {
        return timestamp_us == other.timestamp_us &&
               command_id == other.command_id &&
               param_a == other.param_a &&
               param_b == other.param_b &&
               status == other.status &&
               success == other.success;
    }

    [[nodiscard]] bool operator!=(const HypercallLogEntry& other) const noexcept {
        return !(*this == other);
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// Frame Flags
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Frame state flags.
 */
enum class FrameFlags : uint8_t {
    None            = 0,
    TextMode        = 1 << 0,  ///< Currently in text mode
    GraphicsMode    = 1 << 1,  ///< Currently in graphics mode
    CursorVisible   = 1 << 2,  ///< Cursor is visible
    InputPending    = 1 << 3,  ///< Input events waiting
    ProgramRunning  = 1 << 4,  ///< DOS program actively executing
    Dirty           = 1 << 5,  ///< Frame has changed since last read
    RleCompressed   = 1 << 6,  ///< Text content uses RLE compression
};

[[nodiscard]] inline constexpr FrameFlags operator|(FrameFlags a, FrameFlags b) noexcept {
    return static_cast<FrameFlags>(
        static_cast<uint8_t>(a) | static_cast<uint8_t>(b)
    );
}

[[nodiscard]] inline constexpr FrameFlags operator&(FrameFlags a, FrameFlags b) noexcept {
    return static_cast<FrameFlags>(
        static_cast<uint8_t>(a) & static_cast<uint8_t>(b)
    );
}

inline constexpr FrameFlags& operator|=(FrameFlags& a, FrameFlags b) noexcept {
    return a = a | b;
}

inline constexpr FrameFlags& operator&=(FrameFlags& a, FrameFlags b) noexcept {
    return a = a & b;
}

[[nodiscard]] inline constexpr bool has_flag(FrameFlags flags, FrameFlags flag) noexcept {
    return (static_cast<uint8_t>(flags) & static_cast<uint8_t>(flag)) != 0;
}

// ─────────────────────────────────────────────────────────────────────────────
// Token Efficient Frame
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Token-efficient frame for LLM consumption.
 *
 * Contains all information needed for an LLM to understand the current
 * state of the DOS emulator and make decisions about actions to take.
 *
 * Example:
 * @code
 *   TokenEfficientFrame frame;
 *   frame.frame_id = 42;
 *   frame.timestamp_us = get_current_time_us();
 *   frame.mode = VideoMode::Text80x25;
 *   frame.text_columns = 80;
 *   frame.text_rows = 25;
 *   frame.text_content = "C:\\>_";
 *
 *   std::string json = frame.to_json();
 *   std::string text = frame.to_canonical_text();
 * @endcode
 */
struct TokenEfficientFrame {
    // Header (fixed size)
    uint64_t frame_id{0};           ///< Monotonically increasing frame ID
    uint64_t timestamp_us{0};       ///< Timestamp in microseconds
    VideoMode mode{VideoMode::Unknown};  ///< Current video mode
    FrameFlags flags{FrameFlags::None};  ///< State flags

    // Text mode content (only populated in text mode)
    uint8_t text_columns{0};        ///< Number of text columns
    uint8_t text_rows{0};           ///< Number of text rows
    std::string text_content;       ///< Canonical text serialization (UTF-8)

    // Cursor state
    CursorState cursor;

    // Input status
    InputQueueStatus input_status;

    // Recent hypercall log (last N entries)
    std::vector<HypercallLogEntry> hypercall_log;

    // Metadata for LLM
    std::string program_name;       ///< Current running program (if known)
    std::string working_dir;        ///< Current DOS directory

    /**
     * @brief Serialize to compact JSON for LLM.
     */
    [[nodiscard]] std::string to_json() const;

    /**
     * @brief Serialize to canonical text format (most token-efficient).
     *
     * Produces a human-readable representation with box drawing characters
     * that is easy for LLMs to parse and understand.
     */
    [[nodiscard]] std::string to_canonical_text() const;

    /**
     * @brief Estimate token count (approximate).
     *
     * Uses a rough heuristic of ~4 characters per token for English text,
     * with adjustments for box drawing characters and metadata.
     */
    [[nodiscard]] size_t estimate_tokens() const noexcept;

    /**
     * @brief Check if frame represents text mode.
     */
    [[nodiscard]] bool is_text() const noexcept {
        return is_text_mode(mode);
    }

    /**
     * @brief Get total cell count.
     */
    [[nodiscard]] size_t cell_count() const noexcept {
        return static_cast<size_t>(text_columns) * text_rows;
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// Frame Builder
// ─────────────────────────────────────────────────────────────────────────────

// Forward declaration
class MachineContext;

/**
 * @brief Frame builder with caching and diff support.
 *
 * Builds TokenEfficientFrame instances from the current machine state.
 * Supports differential frames for token efficiency.
 */
class FrameBuilder {
public:
    /**
     * @brief Construct a frame builder.
     */
    FrameBuilder() = default;

    /**
     * @brief Build a complete frame from current state.
     *
     * @param columns Text mode columns
     * @param rows Text mode rows
     * @param screen_data Raw screen data (CP437 encoded)
     * @param cursor_x Cursor X position
     * @param cursor_y Cursor Y position
     * @param cursor_visible Whether cursor is visible
     * @return Complete frame
     */
    [[nodiscard]] TokenEfficientFrame build_full_frame(
        uint8_t columns,
        uint8_t rows,
        const uint8_t* screen_data,
        uint8_t cursor_x,
        uint8_t cursor_y,
        bool cursor_visible
    );

    /**
     * @brief Build a differential frame (only changes since last frame).
     *
     * If no previous frame exists, returns a full frame.
     */
    [[nodiscard]] TokenEfficientFrame build_diff_frame(
        uint8_t columns,
        uint8_t rows,
        const uint8_t* screen_data,
        uint8_t cursor_x,
        uint8_t cursor_y,
        bool cursor_visible
    );

    /**
     * @brief Get estimated token count for current state.
     */
    [[nodiscard]] size_t estimate_current_tokens() const noexcept;

    /**
     * @brief Set maximum hypercall log entries to include.
     */
    void set_hypercall_log_limit(size_t limit) noexcept {
        hypercall_log_limit_ = limit;
    }

    /**
     * @brief Get maximum hypercall log entries.
     */
    [[nodiscard]] size_t hypercall_log_limit() const noexcept {
        return hypercall_log_limit_;
    }

    /**
     * @brief Enable/disable run-length encoding for repeated characters.
     */
    void set_rle_enabled(bool enabled) noexcept {
        rle_enabled_ = enabled;
    }

    /**
     * @brief Check if RLE is enabled.
     */
    [[nodiscard]] bool rle_enabled() const noexcept {
        return rle_enabled_;
    }

    /**
     * @brief Enable/disable trailing space trimming.
     */
    void set_trim_trailing_spaces(bool enabled) noexcept {
        trim_trailing_spaces_ = enabled;
    }

    /**
     * @brief Check if trailing space trimming is enabled.
     */
    [[nodiscard]] bool trim_trailing_spaces() const noexcept {
        return trim_trailing_spaces_;
    }

    /**
     * @brief Add a hypercall log entry.
     */
    void add_hypercall_log(const HypercallLogEntry& entry);

    /**
     * @brief Clear hypercall log.
     */
    void clear_hypercall_log() noexcept {
        hypercall_log_.clear();
    }

    /**
     * @brief Reset state (clears cached frame).
     */
    void reset() noexcept;

    /**
     * @brief Get current frame ID.
     */
    [[nodiscard]] uint64_t current_frame_id() const noexcept {
        return frame_id_;
    }

private:
    uint64_t frame_id_{0};
    std::optional<TokenEfficientFrame> last_frame_;
    std::vector<HypercallLogEntry> hypercall_log_;
    size_t hypercall_log_limit_{10};
    bool rle_enabled_{true};
    bool trim_trailing_spaces_{true};

    [[nodiscard]] std::string serialize_text_mode(
        uint8_t columns,
        uint8_t rows,
        const uint8_t* screen_data
    );

    [[nodiscard]] std::string apply_rle(const std::string& text);
    [[nodiscard]] std::string trim_lines(const std::string& text);
};

} // namespace aibox::llm
