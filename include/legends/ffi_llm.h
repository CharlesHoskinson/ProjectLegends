/**
 * @file ffi_llm.h
 * @brief C FFI API for LLM batch I/O operations.
 *
 * Provides a C-compatible interface for LLM agents to interact with
 * DOSBox-X through batch operations and token-efficient frame retrieval.
 */

#ifndef LEGENDS_FFI_LLM_H
#define LEGENDS_FFI_LLM_H

#include "ffi_core.h"

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

// ─────────────────────────────────────────────────────────────────────────────
// Constants
// ─────────────────────────────────────────────────────────────────────────────

/** Maximum actions in a single batch */
#define LEGENDS_LLM_MAX_BATCH_SIZE 100

/** Maximum text length for type action */
#define LEGENDS_LLM_MAX_TYPE_LENGTH 1024

/** Default timeout for batch execution (ms) */
#define LEGENDS_LLM_DEFAULT_TIMEOUT_MS 5000

/** Maximum timeout for batch execution (ms) */
#define LEGENDS_LLM_MAX_TIMEOUT_MS 60000

/** Maximum frame output buffer size */
#define LEGENDS_LLM_MAX_FRAME_SIZE 32768

/** Maximum JSON response buffer size */
#define LEGENDS_LLM_MAX_RESPONSE_SIZE 65536

// ─────────────────────────────────────────────────────────────────────────────
// Frame Format
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Frame serialization format.
 */
typedef enum {
    LEGENDS_LLM_FORMAT_JSON = 0,           /**< JSON format */
    LEGENDS_LLM_FORMAT_CANONICAL_TEXT = 1, /**< Canonical text with box borders */
    LEGENDS_LLM_FORMAT_RAW_TEXT = 2,       /**< Raw text without borders */
    LEGENDS_LLM_FORMAT_COMPACT_JSON = 3    /**< Compact JSON (no whitespace) */
} legends_llm_format_t;

// ─────────────────────────────────────────────────────────────────────────────
// Error Codes (use unified legends_error_t from ffi_core.h)
// ─────────────────────────────────────────────────────────────────────────────

/* LLM functions use the unified legends_error_t from ffi_core.h.
 * LLM-specific error codes are in the 200-299 range:
 *   LEGENDS_ERR_LLM_INVALID_JSON     = 200
 *   LEGENDS_ERR_LLM_BATCH_TOO_LARGE  = 201
 *   LEGENDS_ERR_LLM_ACTION_FAILED    = 202
 *   LEGENDS_ERR_LLM_NOT_TEXT_MODE    = 203
 *
 * Common error codes also apply:
 *   LEGENDS_ERR_INVALID_HANDLE       = 2
 *   LEGENDS_ERR_BUFFER_TOO_SMALL     = 6
 *   LEGENDS_ERR_TIMEOUT              = 11
 */

// ─────────────────────────────────────────────────────────────────────────────
// Configuration
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief LLM I/O layer configuration.
 */
typedef struct {
    int enable_rle;              /**< Enable run-length encoding (0/1) */
    int enable_diff_mode;        /**< Enable differential frames (0/1) */
    int hypercall_log_limit;     /**< Max hypercall log entries (0-100) */
    int trim_trailing_spaces;    /**< Remove trailing spaces (0/1) */
    int include_box_border;      /**< Include box border in canonical text (0/1) */
    int mark_cursor;             /**< Mark cursor position (0/1) */
} legends_llm_config_t;

/**
 * @brief Get default LLM configuration.
 */
LEGENDS_API legends_llm_config_t legends_llm_default_config(void);

/**
 * @brief Configure LLM I/O layer.
 *
 * @param handle Valid emulator handle
 * @param config Configuration settings
 * @return LEGENDS_OK on success, error code on failure
 */
LEGENDS_API legends_error_t legends_llm_configure(
    legends_handle_t handle,
    const legends_llm_config_t* config
);

// ─────────────────────────────────────────────────────────────────────────────
// Frame Retrieval
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Get current frame without executing actions.
 *
 * Retrieves the current screen state in the specified format.
 *
 * @param handle Valid emulator handle
 * @param format Output format (see legends_llm_format_t)
 * @param output_buffer Buffer for frame output
 * @param output_capacity Capacity of output buffer
 * @param output_len_out Actual length of output (can be NULL)
 * @return LEGENDS_OK on success, error code on failure
 *
 * @note If buffer is too small, returns LEGENDS_ERR_BUFFER_TOO_SMALL
 *       and sets output_len_out to required size.
 */
LEGENDS_API legends_error_t legends_llm_get_frame(
    legends_handle_t handle,
    legends_llm_format_t format,
    char* output_buffer,
    size_t output_capacity,
    size_t* output_len_out
);

/**
 * @brief Get differential frame (changes since last frame).
 *
 * Returns only the portions of the screen that have changed
 * since the last call to legends_llm_get_frame or legends_llm_get_diff_frame.
 *
 * @param handle Valid emulator handle
 * @param format Output format
 * @param output_buffer Buffer for frame output
 * @param output_capacity Capacity of output buffer
 * @param output_len_out Actual length of output
 * @return LEGENDS_OK on success, error code on failure
 */
LEGENDS_API legends_error_t legends_llm_get_diff_frame(
    legends_handle_t handle,
    legends_llm_format_t format,
    char* output_buffer,
    size_t output_capacity,
    size_t* output_len_out
);

/**
 * @brief Estimate token count for current frame.
 *
 * @param handle Valid emulator handle
 * @return Estimated token count, or negative error code
 */
LEGENDS_API int32_t legends_llm_estimate_tokens(legends_handle_t handle);

// ─────────────────────────────────────────────────────────────────────────────
// Batch Execution
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Execute a batch of actions and return frame.
 *
 * Executes the actions specified in the JSON request and returns
 * a JSON response with execution results and optional frame.
 *
 * JSON Request Format:
 * @code
 * {
 *   "actions": [
 *     {"type": "type", "text": "DIR\n"},
 *     {"type": "wait", "ms": 500},
 *     {"type": "special_key", "key": "Enter"}
 *   ],
 *   "timeout_ms": 5000,
 *   "return_frame": true,
 *   "stop_on_error": true
 * }
 * @endcode
 *
 * JSON Response Format:
 * @code
 * {
 *   "success": true,
 *   "actions_executed": 3,
 *   "results": [
 *     {"index": 0, "status": "ok", "duration_us": 1234},
 *     {"index": 1, "status": "ok", "duration_us": 500000},
 *     {"index": 2, "status": "ok", "duration_us": 567}
 *   ],
 *   "total_duration_us": 501801,
 *   "frame": { ... }
 * }
 * @endcode
 *
 * @param handle Valid emulator handle
 * @param json_request JSON-encoded action batch
 * @param json_request_len Length of JSON request
 * @param json_response_out Buffer for JSON response
 * @param json_response_capacity Capacity of response buffer
 * @param json_response_len_out Actual length of response
 * @return LEGENDS_OK on success, error code on failure
 */
LEGENDS_API legends_error_t legends_llm_execute_batch(
    legends_handle_t handle,
    const char* json_request,
    size_t json_request_len,
    char* json_response_out,
    size_t json_response_capacity,
    size_t* json_response_len_out
);

// ─────────────────────────────────────────────────────────────────────────────
// Simple Action Helpers
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Type text into the emulator.
 *
 * Convenience wrapper around legends_llm_execute_batch for simple typing.
 *
 * @param handle Valid emulator handle
 * @param text Text to type (supports \\n for Enter, \\t for Tab)
 * @param delay_between_ms Delay between keystrokes (0 for immediate)
 * @return LEGENDS_OK on success, error code on failure
 */
LEGENDS_API legends_error_t legends_llm_type(
    legends_handle_t handle,
    const char* text,
    uint32_t delay_between_ms
);

/**
 * @brief Send a special key.
 *
 * @param handle Valid emulator handle
 * @param key_name Key name (e.g., "Enter", "Escape", "F1", "CtrlC")
 * @return LEGENDS_OK on success, error code on failure
 */
LEGENDS_API legends_error_t legends_llm_special_key(
    legends_handle_t handle,
    const char* key_name
);

/**
 * @brief Wait for specified duration.
 *
 * @param handle Valid emulator handle
 * @param milliseconds Duration to wait
 * @return LEGENDS_OK on success, error code on failure
 */
LEGENDS_API legends_error_t legends_llm_wait(
    legends_handle_t handle,
    uint32_t milliseconds
);

/**
 * @brief Click at text coordinates.
 *
 * @param handle Valid emulator handle
 * @param column Column (0-based)
 * @param row Row (0-based)
 * @param button Button name: "left", "right", or "middle"
 * @return LEGENDS_OK on success, error code on failure
 */
LEGENDS_API legends_error_t legends_llm_click(
    legends_handle_t handle,
    uint8_t column,
    uint8_t row,
    const char* button
);

// ─────────────────────────────────────────────────────────────────────────────
// Screenshot Diff
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Compare current frame against baseline.
 *
 * @param handle Valid emulator handle
 * @param baseline_text Expected text content
 * @param baseline_len Length of baseline text
 * @param threshold_percent Ignore changes below this percentage (0-100)
 * @param diff_output Buffer for diff output (can be NULL)
 * @param diff_capacity Capacity of diff buffer
 * @param diff_len_out Actual length of diff (can be NULL)
 * @return Change percentage (0-100) on success, negative error code on failure
 */
LEGENDS_API float legends_llm_compare_baseline(
    legends_handle_t handle,
    const char* baseline_text,
    size_t baseline_len,
    float threshold_percent,
    char* diff_output,
    size_t diff_capacity,
    size_t* diff_len_out
);

/**
 * @brief Check if current frame matches baseline exactly.
 *
 * @param handle Valid emulator handle
 * @param baseline_text Expected text content
 * @param baseline_len Length of baseline text
 * @return 1 if identical, 0 if different, negative error code on failure
 */
LEGENDS_API int32_t legends_llm_matches_baseline(
    legends_handle_t handle,
    const char* baseline_text,
    size_t baseline_len
);

// ─────────────────────────────────────────────────────────────────────────────
// Frame State Queries
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Get current video mode.
 *
 * @param handle Valid emulator handle
 * @param[out] columns Number of columns (can be NULL)
 * @param[out] rows Number of rows (can be NULL)
 * @return Video mode enum value, or negative error code
 */
LEGENDS_API int32_t legends_llm_get_video_mode(
    legends_handle_t handle,
    uint8_t* columns,
    uint8_t* rows
);

/**
 * @brief Get cursor position.
 *
 * @param handle Valid emulator handle
 * @param[out] column Cursor column (can be NULL)
 * @param[out] row Cursor row (can be NULL)
 * @param[out] visible Cursor visibility (can be NULL)
 * @return LEGENDS_OK on success, error code on failure
 */
LEGENDS_API legends_error_t legends_llm_get_cursor(
    legends_handle_t handle,
    uint8_t* column,
    uint8_t* row,
    int* visible
);

/**
 * @brief Get input queue status.
 *
 * @param handle Valid emulator handle
 * @param[out] pending_keys Number of pending keystrokes
 * @param[out] pending_mouse Number of pending mouse events
 * @return LEGENDS_OK on success, error code on failure
 */
LEGENDS_API legends_error_t legends_llm_get_input_status(
    legends_handle_t handle,
    uint8_t* pending_keys,
    uint8_t* pending_mouse
);

/**
 * @brief Check if emulator is in text mode.
 *
 * @param handle Valid emulator handle
 * @return 1 if in text mode, 0 if in graphics mode, negative on error
 */
LEGENDS_API int32_t legends_llm_is_text_mode(legends_handle_t handle);

/**
 * @brief Get current frame ID.
 *
 * @param handle Valid emulator handle
 * @return Frame ID, or negative error code
 */
LEGENDS_API int64_t legends_llm_get_frame_id(legends_handle_t handle);

// ─────────────────────────────────────────────────────────────────────────────
// Hypercall Log
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Get recent hypercall log entries.
 *
 * Returns JSON array of recent hypercall entries.
 *
 * @param handle Valid emulator handle
 * @param max_entries Maximum entries to return
 * @param output_buffer Buffer for JSON output
 * @param output_capacity Capacity of output buffer
 * @param output_len_out Actual length of output
 * @return LEGENDS_OK on success, error code on failure
 */
LEGENDS_API legends_error_t legends_llm_get_hypercall_log(
    legends_handle_t handle,
    size_t max_entries,
    char* output_buffer,
    size_t output_capacity,
    size_t* output_len_out
);

/**
 * @brief Clear hypercall log.
 *
 * @param handle Valid emulator handle
 * @return LEGENDS_OK on success, error code on failure
 */
LEGENDS_API legends_error_t legends_llm_clear_hypercall_log(legends_handle_t handle);

#ifdef __cplusplus
}
#endif

#endif // LEGENDS_FFI_LLM_H
