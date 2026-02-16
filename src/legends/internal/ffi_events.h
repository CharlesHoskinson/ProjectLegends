/**
 * @file ffi_events.h
 * @brief FFI-safe event structures and subscription API.
 *
 * Defines C-compatible event structures for passing across the FFI boundary.
 * All structures use fixed-size types and explicit padding for ABI stability.
 */

#ifndef LEGENDS_FFI_EVENTS_H
#define LEGENDS_FFI_EVENTS_H

#include "ffi_core.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ═══════════════════════════════════════════════════════════════════════════
 * Event Types
 * ═══════════════════════════════════════════════════════════════════════════ */

/**
 * @brief Event type enumeration.
 */
typedef enum {
    LEGENDS_EVENT_TEXT_SCREEN = 1,       /**< Full text mode screen */
    LEGENDS_EVENT_TEXT_DIFF = 2,         /**< Differential text update */
    LEGENDS_EVENT_PROGRAM_STARTED = 3,   /**< Program started */
    LEGENDS_EVENT_PROGRAM_HALTED = 4,    /**< Program terminated */
    LEGENDS_EVENT_KEYBOARD = 5,          /**< Keyboard input */
    LEGENDS_EVENT_MOUSE = 6,             /**< Mouse input */
    LEGENDS_EVENT_LOG = 7                /**< Log message */
} legends_event_type_t;

/* ═══════════════════════════════════════════════════════════════════════════
 * Text Mode Events
 * ═══════════════════════════════════════════════════════════════════════════ */

/**
 * @brief Single text mode cell (FFI-safe).
 *
 * Fixed 4-byte structure for ABI stability.
 */
typedef struct {
    uint16_t character;    /**< Unicode codepoint (converted from CP437) */
    uint8_t  foreground;   /**< Foreground color (0-15) */
    uint8_t  background;   /**< Background color (0-7 or 0-15 w/o blink) */
} legends_text_cell_t;

/**
 * @brief Text mode screen event (FFI-safe).
 *
 * Contains full screen buffer and cursor information.
 * The cells pointer is valid only for the duration of the callback.
 */
typedef struct {
    uint8_t  columns;          /**< Number of columns (typically 80) */
    uint8_t  rows;             /**< Number of rows (typically 25) */
    uint8_t  cursor_x;         /**< Cursor column position */
    uint8_t  cursor_y;         /**< Cursor row position */
    int32_t  cursor_visible;   /**< 1 if cursor visible, 0 if hidden */
    uint64_t timestamp_us;     /**< Microseconds since emulator start */
    const legends_text_cell_t* cells;  /**< Cell array [rows * columns] */
} legends_text_screen_event_t;

/**
 * @brief Text mode diff entry (single cell change).
 */
typedef struct {
    uint16_t index;            /**< Cell index (row * columns + col) */
    legends_text_cell_t cell;    /**< New cell value */
} legends_text_change_t;

/**
 * @brief Text mode differential event (FFI-safe).
 *
 * Contains only cells that changed since the last event.
 * More efficient for incremental updates.
 */
typedef struct {
    uint8_t  cursor_x;         /**< Updated cursor column */
    uint8_t  cursor_y;         /**< Updated cursor row */
    int32_t  cursor_changed;   /**< 1 if cursor moved, 0 if unchanged */
    uint64_t timestamp_us;     /**< Microseconds since emulator start */
    uint16_t change_count;     /**< Number of changed cells */
    const legends_text_change_t* changes;  /**< Array of changes */
} legends_text_diff_event_t;

/* ═══════════════════════════════════════════════════════════════════════════
 * Program Lifecycle Events
 * ═══════════════════════════════════════════════════════════════════════════ */

/**
 * @brief Program termination reason.
 */
typedef enum {
    LEGENDS_TERM_NORMAL_EXIT = 0,    /**< INT 21h AH=4Ch */
    LEGENDS_TERM_CTRL_BREAK = 1,     /**< Ctrl+Break pressed */
    LEGENDS_TERM_CRITICAL_ERROR = 2, /**< DOS critical error */
    LEGENDS_TERM_EXCEPTION = 3,      /**< CPU exception */
    LEGENDS_TERM_PARENT_KILL = 4,    /**< Parent terminated child */
    LEGENDS_TERM_UNKNOWN = 5         /**< Unknown reason */
} legends_termination_reason_t;

/**
 * @brief Program started event (FFI-safe).
 */
typedef struct {
    uint64_t timestamp_us;         /**< Event timestamp */
    uint16_t psp_segment;          /**< Program Segment Prefix location */
    uint16_t environment_seg;      /**< Environment block segment */
    uint32_t load_address;         /**< Linear address where loaded */
    uint32_t program_size;         /**< Size in bytes */
    char     path[128];            /**< DOS path to executable */
    char     arguments[128];       /**< Command line arguments */
} legends_program_started_event_t;

/**
 * @brief Program halted event (FFI-safe).
 */
typedef struct {
    uint64_t timestamp_us;                    /**< Event timestamp */
    legends_termination_reason_t reason;        /**< Termination reason */
    uint8_t  exit_code;                       /**< Return code (0-255) */
    uint8_t  _padding[3];                     /**< Padding for alignment */
    uint32_t instructions_executed;           /**< Total instruction count */
    uint32_t runtime_ms;                      /**< Wall-clock runtime */
    char     path[128];                       /**< Path of terminated program */
} legends_program_halted_event_t;

/* ═══════════════════════════════════════════════════════════════════════════
 * Input Events
 * ═══════════════════════════════════════════════════════════════════════════ */

/**
 * @brief Keyboard modifier flags.
 */
typedef enum {
    LEGENDS_MOD_NONE  = 0,
    LEGENDS_MOD_SHIFT = 1 << 0,
    LEGENDS_MOD_CTRL  = 1 << 1,
    LEGENDS_MOD_ALT   = 1 << 2
} legends_key_modifiers_t;

/**
 * @brief Keyboard event (FFI-safe).
 */
typedef struct {
    uint64_t timestamp_us;     /**< Event timestamp */
    uint8_t  scan_code;        /**< AT scan code */
    int8_t   is_pressed;       /**< 1 = down, 0 = up */
    int8_t   is_extended;      /**< 1 = has E0 prefix */
    uint8_t  modifiers;        /**< Modifier bitmask */
} legends_keyboard_event_t;

/**
 * @brief Mouse button flags.
 */
typedef enum {
    LEGENDS_MOUSE_NONE   = 0,
    LEGENDS_MOUSE_LEFT   = 1 << 0,
    LEGENDS_MOUSE_RIGHT  = 1 << 1,
    LEGENDS_MOUSE_MIDDLE = 1 << 2
} legends_mouse_buttons_t;

/**
 * @brief Mouse event (FFI-safe).
 */
typedef struct {
    uint64_t timestamp_us;     /**< Event timestamp */
    int16_t  delta_x;          /**< Relative X movement */
    int16_t  delta_y;          /**< Relative Y movement */
    int8_t   wheel_delta;      /**< Scroll wheel movement */
    uint8_t  buttons;          /**< Current button state */
    uint8_t  changed;          /**< Buttons that changed */
    uint8_t  _padding;         /**< Padding for alignment */
} legends_mouse_event_t;

/* ═══════════════════════════════════════════════════════════════════════════
 * Event Callback Types
 * ═══════════════════════════════════════════════════════════════════════════ */

/**
 * @brief Generic event callback.
 *
 * @param event_type Type of event (legends_event_type_t)
 * @param event_data Pointer to event structure (type depends on event_type)
 * @param user_data User-provided context
 */
typedef void (*legends_event_callback_t)(
    legends_event_type_t event_type,
    const void* event_data,
    void* user_data
);

/**
 * @brief Text screen event callback.
 */
typedef void (*legends_text_screen_callback_t)(
    const legends_text_screen_event_t* event,
    void* user_data
);

/**
 * @brief Text diff event callback.
 */
typedef void (*legends_text_diff_callback_t)(
    const legends_text_diff_event_t* event,
    void* user_data
);

/**
 * @brief Program started callback.
 */
typedef void (*legends_program_started_callback_t)(
    const legends_program_started_event_t* event,
    void* user_data
);

/**
 * @brief Program halted callback.
 */
typedef void (*legends_program_halted_callback_t)(
    const legends_program_halted_event_t* event,
    void* user_data
);

/**
 * @brief Keyboard event callback.
 */
typedef void (*legends_keyboard_callback_t)(
    const legends_keyboard_event_t* event,
    void* user_data
);

/**
 * @brief Mouse event callback.
 */
typedef void (*legends_mouse_callback_t)(
    const legends_mouse_event_t* event,
    void* user_data
);

/* ═══════════════════════════════════════════════════════════════════════════
 * Event Subscription API
 * ═══════════════════════════════════════════════════════════════════════════ */

/**
 * @brief Subscribe to events.
 *
 * @param handle Emulator handle
 * @param event_type Type of event to subscribe to
 * @param callback Generic callback function
 * @param user_data User data passed to callback
 * @return Subscription handle, or NULL on failure
 */
legends_subscription_t legends_subscribe(
    legends_handle_t handle,
    legends_event_type_t event_type,
    legends_event_callback_t callback,
    void* user_data
);

/**
 * @brief Unsubscribe from events.
 *
 * @param subscription Subscription handle from legends_subscribe
 */
void legends_unsubscribe(legends_subscription_t subscription);

/**
 * @brief Enable differential text mode updates.
 *
 * When enabled, text screen events are converted to diff events
 * that contain only changed cells. More efficient for incremental
 * updates.
 *
 * @param handle Emulator handle
 * @param enable 1 to enable, 0 to disable
 * @return LEGENDS_OK on success
 */
legends_error_t legends_enable_text_diff(legends_handle_t handle, int enable);

/**
 * @brief Flush pending events to subscribers.
 *
 * Events are queued internally and delivered when this function
 * is called. This should be called from the main thread to ensure
 * thread-safe callback invocation.
 *
 * @param handle Emulator handle
 * @return Number of events delivered, or negative error code
 */
int32_t legends_flush_events(legends_handle_t handle);

/**
 * @brief Get number of pending events.
 *
 * @param handle Emulator handle
 * @return Number of pending events, or negative error code
 */
int32_t legends_pending_event_count(legends_handle_t handle);

/* ═══════════════════════════════════════════════════════════════════════════
 * Structure Size Verification
 * ═══════════════════════════════════════════════════════════════════════════ */

/**
 * @brief Get expected size of FFI structure.
 *
 * Used for ABI compatibility checking. If the caller's structure
 * size doesn't match, there may be an ABI mismatch.
 *
 * @param struct_name Name of structure (e.g., "legends_text_cell_t")
 * @return Size of structure in bytes, or 0 if unknown
 */
size_t legends_get_struct_size(const char* struct_name);

#ifdef __cplusplus
}
#endif

/* ═══════════════════════════════════════════════════════════════════════════
 * Static Size Assertions (C++ only)
 * ═══════════════════════════════════════════════════════════════════════════ */

#ifdef __cplusplus
static_assert(sizeof(legends_text_cell_t) == 4,
              "legends_text_cell_t must be 4 bytes");
static_assert(sizeof(legends_keyboard_event_t) == 12,
              "legends_keyboard_event_t must be 12 bytes");
static_assert(sizeof(legends_mouse_event_t) == 16,
              "legends_mouse_event_t must be 16 bytes");
#endif

#endif /* LEGENDS_FFI_EVENTS_H */
