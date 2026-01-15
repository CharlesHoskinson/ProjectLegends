/**
 * @file dosboxx_embed.h
 * @brief Embeddable DOSBox-X API - The Compile Firewall
 *
 * This is the stable C ABI boundary between AIBox (modern C++23) and
 * DOSBox-X core (legacy C++). All interaction with the emulator MUST
 * go through this API.
 *
 * DESIGN DECISIONS:
 * - Single instance per process (due to DOSBox-X global state)
 * - Pure C API (compiles as C11 and C++23)
 * - Two-call pattern for variable-size outputs
 * - All calls for a handle must be serialized by caller
 * - Deterministic mode disables host timing, audio pacing, randomness
 *
 * @version 1.0.0
 */

#ifndef DOSBOXX_EMBED_H
#define DOSBOXX_EMBED_H

#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* =========================================================================
 * VERSION & ABI
 * ========================================================================= */

#define DOSBOXX_API_VERSION_MAJOR 1
#define DOSBOXX_API_VERSION_MINOR 0
#define DOSBOXX_API_VERSION_PATCH 0

/* Packed version for single comparison: (major << 16) | (minor << 8) | patch */
#define DOSBOXX_API_VERSION \
    ((DOSBOXX_API_VERSION_MAJOR << 16) | \
     (DOSBOXX_API_VERSION_MINOR << 8) | \
     DOSBOXX_API_VERSION_PATCH)

/* =========================================================================
 * ERROR CODES
 * ========================================================================= */

typedef int32_t dosboxx_error_t;

#define DOSBOXX_OK                      0
#define DOSBOXX_ERR_NULL_HANDLE        -1
#define DOSBOXX_ERR_NULL_POINTER       -2
#define DOSBOXX_ERR_ALREADY_CREATED    -3   /* Single instance violation */
#define DOSBOXX_ERR_NOT_INITIALIZED    -4
#define DOSBOXX_ERR_ALREADY_RUNNING    -5
#define DOSBOXX_ERR_BUFFER_TOO_SMALL   -6
#define DOSBOXX_ERR_INVALID_CONFIG     -7
#define DOSBOXX_ERR_INVALID_STATE      -8
#define DOSBOXX_ERR_VERSION_MISMATCH   -9
#define DOSBOXX_ERR_IO_FAILED         -10
#define DOSBOXX_ERR_OUT_OF_MEMORY     -11
#define DOSBOXX_ERR_NOT_SUPPORTED     -12
#define DOSBOXX_ERR_INTERNAL          -99

/* =========================================================================
 * HANDLE TYPE (opaque)
 * ========================================================================= */

typedef struct dosboxx_instance* dosboxx_handle;

/* =========================================================================
 * CONFIGURATION
 * ========================================================================= */

/**
 * @brief Machine configuration. Must be set before dosboxx_create().
 *
 * ABI note: This struct layout is frozen for v1.x. New fields added at end only.
 */
typedef struct {
    uint32_t struct_size;           /**< sizeof(dosboxx_config_t) for versioning */
    uint32_t api_version;           /**< Expected DOSBOXX_API_VERSION */

    /* Memory */
    uint32_t memory_kb;             /**< Conventional memory in KB (640 typical) */
    uint32_t xms_kb;                /**< Extended memory in KB (0 = none) */
    uint32_t ems_kb;                /**< Expanded memory in KB (0 = none) */

    /* CPU */
    uint32_t cpu_cycles;            /**< Cycles per ms (0 = auto) */
    uint8_t  cpu_type;              /**< 0=auto, 1=8086, 2=286, 3=386, 4=486, 5=pentium */
    uint8_t  _pad1[3];

    /* Machine type */
    uint8_t  machine_type;          /**< 0=vga, 1=ega, 2=cga, 3=hercules, 4=tandy */
    uint8_t  _pad2[3];

    /* Determinism */
    uint8_t  deterministic;         /**< 1 = deterministic mode (no host timing) */
    uint8_t  _pad3[3];

    /* Paths (null-terminated, max 260 chars each) */
    const char* config_path;        /**< Path to .conf file (NULL = defaults) */
    const char* working_dir;        /**< Working directory (NULL = current) */

    /* Reserved for future use - must be zero */
    uint64_t _reserved[8];

} dosboxx_config_t;

/* Helper to initialize config with defaults - C99 designated initializers */
#define DOSBOXX_CONFIG_INIT { \
    sizeof(dosboxx_config_t), \
    DOSBOXX_API_VERSION, \
    640, \
    0, \
    0, \
    0, \
    0, \
    {0, 0, 0}, \
    0, \
    {0, 0, 0}, \
    1, \
    {0, 0, 0}, \
    NULL, \
    NULL, \
    {0, 0, 0, 0, 0, 0, 0, 0} \
}

/* =========================================================================
 * STEP RESULT
 * ========================================================================= */

/** Stop reasons for stepping */
#define DOSBOXX_STOP_COMPLETED      0   /**< Requested cycles/time completed */
#define DOSBOXX_STOP_HALT           1   /**< CPU halted (HLT instruction) */
#define DOSBOXX_STOP_BREAKPOINT     2   /**< Breakpoint hit */
#define DOSBOXX_STOP_ERROR          3   /**< Error during execution */

/**
 * @brief Result of a step operation.
 *
 * ABI note: This struct layout is frozen for v1.x.
 */
typedef struct {
    uint64_t cycles_executed;       /**< Actual CPU cycles executed */
    uint64_t emu_time_us;           /**< Emulated time advanced (microseconds) */
    uint32_t stop_reason;           /**< DOSBOXX_STOP_* code */
    uint32_t events_processed;      /**< PIC events fired during step */
} dosboxx_step_result_t;

/* =========================================================================
 * TEXT CAPTURE
 * ========================================================================= */

/**
 * @brief Single text cell (character + attribute).
 *
 * Layout matches VGA text memory: character at even address, attribute at odd.
 */
typedef struct {
    uint8_t character;              /**< CP437 character code */
    uint8_t attribute;              /**< VGA text attribute (fg/bg/blink) */
} dosboxx_text_cell_t;

/**
 * @brief Text capture result metadata.
 */
typedef struct {
    uint8_t  columns;               /**< Number of columns (40 or 80) */
    uint8_t  rows;                  /**< Number of rows (25, 43, or 50) */
    uint8_t  active_page;           /**< Currently displayed video page */
    uint8_t  cursor_x;              /**< Cursor column (0-based) */
    uint8_t  cursor_y;              /**< Cursor row (0-based) */
    uint8_t  cursor_visible;        /**< 1 if cursor visible */
    uint8_t  cursor_start;          /**< Cursor start scanline */
    uint8_t  cursor_end;            /**< Cursor end scanline */
} dosboxx_text_info_t;

/* =========================================================================
 * LIFECYCLE API
 * ========================================================================= */

/**
 * @brief Get API version.
 *
 * Call this before dosboxx_create() to verify ABI compatibility.
 *
 * @param[out] major Major version (breaking changes)
 * @param[out] minor Minor version (new features, backward compatible)
 * @param[out] patch Patch version (bug fixes)
 * @return DOSBOXX_OK on success
 */
dosboxx_error_t dosboxx_get_api_version(
    uint32_t* major,
    uint32_t* minor,
    uint32_t* patch
);

/**
 * @brief Create emulator instance.
 *
 * IMPORTANT: Only ONE instance per process is supported. Calling this
 * when an instance already exists returns DOSBOXX_ERR_ALREADY_CREATED.
 *
 * @param[in]  config Configuration (NULL for defaults)
 * @param[out] handle_out Receives the handle on success
 * @return DOSBOXX_OK on success, error code on failure
 */
dosboxx_error_t dosboxx_create(
    const dosboxx_config_t* config,
    dosboxx_handle* handle_out
);

/**
 * @brief Destroy emulator instance.
 *
 * Safe to call multiple times. After this call, the handle is invalid.
 *
 * @param handle Handle from dosboxx_create()
 * @return DOSBOXX_OK on success
 */
dosboxx_error_t dosboxx_destroy(dosboxx_handle handle);

/**
 * @brief Soft reset the emulator.
 *
 * Resets CPU, memory, and devices to initial state. Configuration preserved.
 *
 * @param handle Valid handle
 * @return DOSBOXX_OK on success
 */
dosboxx_error_t dosboxx_reset(dosboxx_handle handle);

/**
 * @brief Get current configuration.
 *
 * @param handle Valid handle
 * @param[out] config_out Receives current configuration
 * @return DOSBOXX_OK on success
 */
dosboxx_error_t dosboxx_get_config(
    dosboxx_handle handle,
    dosboxx_config_t* config_out
);

/* =========================================================================
 * STEPPING API
 * ========================================================================= */

/**
 * @brief Step emulation by milliseconds of emulated time.
 *
 * Advances exactly `ms` milliseconds of emulated time. In deterministic mode,
 * this is independent of host wall-clock time.
 *
 * @param handle Valid handle
 * @param ms Milliseconds of emulated time to execute
 * @param[out] result_out Receives step result (may be NULL)
 * @return DOSBOXX_OK on success
 */
dosboxx_error_t dosboxx_step_ms(
    dosboxx_handle handle,
    uint32_t ms,
    dosboxx_step_result_t* result_out
);

/**
 * @brief Step emulation by exact CPU cycles.
 *
 * Executes exactly `cycles` CPU cycles. Events fire when their scheduled
 * time passes.
 *
 * @param handle Valid handle
 * @param cycles Exact number of CPU cycles to execute
 * @param[out] result_out Receives step result (may be NULL)
 * @return DOSBOXX_OK on success
 */
dosboxx_error_t dosboxx_step_cycles(
    dosboxx_handle handle,
    uint64_t cycles,
    dosboxx_step_result_t* result_out
);

/**
 * @brief Get current emulated time.
 *
 * @param handle Valid handle
 * @param[out] time_us_out Receives emulated time in microseconds
 * @return DOSBOXX_OK on success
 */
dosboxx_error_t dosboxx_get_emu_time(
    dosboxx_handle handle,
    uint64_t* time_us_out
);

/**
 * @brief Get total CPU cycles executed since creation/reset.
 *
 * @param handle Valid handle
 * @param[out] cycles_out Receives total cycles
 * @return DOSBOXX_OK on success
 */
dosboxx_error_t dosboxx_get_total_cycles(
    dosboxx_handle handle,
    uint64_t* cycles_out
);

/* =========================================================================
 * FRAME CAPTURE API
 * ========================================================================= */

/**
 * @brief Capture text-mode screen.
 *
 * Two-call pattern:
 *   1. Call with cells=NULL to get required count in cells_count_out
 *   2. Call with buffer to fill cells array
 *
 * @param handle Valid handle
 * @param[out] cells Output buffer (NULL to query size)
 * @param cells_count Buffer capacity in cells
 * @param[out] cells_count_out Actual/required cell count
 * @param[out] info_out Text mode info (may be NULL)
 * @return DOSBOXX_OK on success, DOSBOXX_ERR_BUFFER_TOO_SMALL if buffer too small
 */
dosboxx_error_t dosboxx_capture_text(
    dosboxx_handle handle,
    dosboxx_text_cell_t* cells,
    size_t cells_count,
    size_t* cells_count_out,
    dosboxx_text_info_t* info_out
);

/**
 * @brief Capture graphics framebuffer as RGB24.
 *
 * Two-call pattern:
 *   1. Call with buffer=NULL to get required size
 *   2. Call with buffer to fill with RGB24 data (3 bytes per pixel)
 *
 * Returns pre-scaler output. Pixel format: RGB24 (R at offset 0, G at 1, B at 2).
 *
 * @param handle Valid handle
 * @param[out] buffer Output buffer (NULL to query size)
 * @param buffer_size Buffer size in bytes
 * @param[out] size_out Actual/required byte count
 * @param[out] width_out Frame width in pixels
 * @param[out] height_out Frame height in pixels
 * @return DOSBOXX_OK on success
 */
dosboxx_error_t dosboxx_capture_rgb(
    dosboxx_handle handle,
    uint8_t* buffer,
    size_t buffer_size,
    size_t* size_out,
    uint16_t* width_out,
    uint16_t* height_out
);

/**
 * @brief Check if framebuffer changed since last capture.
 *
 * @param handle Valid handle
 * @param[out] dirty_out Receives 1 if dirty, 0 if unchanged
 * @return DOSBOXX_OK on success
 */
dosboxx_error_t dosboxx_is_frame_dirty(
    dosboxx_handle handle,
    int* dirty_out
);

/**
 * @brief Get cursor position.
 *
 * @param handle Valid handle
 * @param[out] x_out Cursor column (0-based)
 * @param[out] y_out Cursor row (0-based)
 * @param[out] visible_out 1 if visible, 0 if hidden
 * @return DOSBOXX_OK on success
 */
dosboxx_error_t dosboxx_get_cursor(
    dosboxx_handle handle,
    uint8_t* x_out,
    uint8_t* y_out,
    int* visible_out
);

/* =========================================================================
 * INPUT INJECTION API
 * ========================================================================= */

/**
 * @brief Inject keyboard scancode (Set 1 / AT scancodes).
 *
 * Scancodes are buffered and processed on next step() call.
 *
 * @param handle Valid handle
 * @param scancode AT scancode (set 1)
 * @param is_down 1 for key press, 0 for key release
 * @return DOSBOXX_OK on success
 */
dosboxx_error_t dosboxx_key_event(
    dosboxx_handle handle,
    uint8_t scancode,
    int is_down
);

/**
 * @brief Inject extended scancode (E0-prefixed keys).
 *
 * For arrow keys, Insert, Delete, Home, End, Page Up/Down, etc.
 *
 * @param handle Valid handle
 * @param scancode Scancode after E0 prefix
 * @param is_down 1 for key press, 0 for key release
 * @return DOSBOXX_OK on success
 */
dosboxx_error_t dosboxx_key_event_ext(
    dosboxx_handle handle,
    uint8_t scancode,
    int is_down
);

/**
 * @brief Type UTF-8 text string (convenience wrapper).
 *
 * Translates UTF-8 characters to appropriate scancodes. Handles common
 * special characters and shift states. Newlines become Enter key.
 *
 * @param handle Valid handle
 * @param utf8_text Null-terminated UTF-8 string
 * @return DOSBOXX_OK on success
 */
dosboxx_error_t dosboxx_text_input(
    dosboxx_handle handle,
    const char* utf8_text
);

/**
 * @brief Inject mouse movement and button event.
 *
 * @param handle Valid handle
 * @param delta_x Relative X movement
 * @param delta_y Relative Y movement
 * @param buttons Button bitmask (bit 0=left, 1=right, 2=middle)
 * @return DOSBOXX_OK on success
 */
dosboxx_error_t dosboxx_mouse_event(
    dosboxx_handle handle,
    int16_t delta_x,
    int16_t delta_y,
    uint8_t buttons
);

/* =========================================================================
 * SAVE/LOAD API
 * ========================================================================= */

/**
 * @brief Save complete machine state.
 *
 * Two-call pattern:
 *   1. Call with buffer=NULL to get required size
 *   2. Call with buffer to save state
 *
 * State includes everything needed for deterministic resume:
 * - CPU registers, memory
 * - PIC/PIT state and event queue
 * - Timing indices and cycle counters
 * - Input buffers
 *
 * Format is versioned. Load rejects incompatible versions.
 *
 * @param handle Valid handle
 * @param[out] buffer Output buffer (NULL to query size)
 * @param buffer_size Buffer size in bytes
 * @param[out] size_out Actual/required byte count
 * @return DOSBOXX_OK on success
 */
dosboxx_error_t dosboxx_save_state(
    dosboxx_handle handle,
    void* buffer,
    size_t buffer_size,
    size_t* size_out
);

/**
 * @brief Load machine state from buffer.
 *
 * Restores complete state. After load, stepping produces identical
 * results as if the save point were reached normally.
 *
 * @param handle Valid handle
 * @param buffer State data from dosboxx_save_state()
 * @param buffer_size Size of state data
 * @return DOSBOXX_OK on success, DOSBOXX_ERR_VERSION_MISMATCH if incompatible
 */
dosboxx_error_t dosboxx_load_state(
    dosboxx_handle handle,
    const void* buffer,
    size_t buffer_size
);

/**
 * @brief Get SHA-256 hash of current machine state.
 *
 * Use for determinism verification: same inputs should produce same hash.
 *
 * @param handle Valid handle
 * @param[out] hash_out 32-byte buffer for SHA-256 hash
 * @return DOSBOXX_OK on success
 */
dosboxx_error_t dosboxx_get_state_hash(
    dosboxx_handle handle,
    uint8_t hash_out[32]
);

/**
 * @brief Verify determinism via round-trip test.
 *
 * Performs: save -> step N cycles -> hash1; restore -> step N cycles -> hash2
 * Returns success if hash1 == hash2.
 *
 * @param handle Valid handle
 * @param test_cycles Number of cycles to step for test
 * @param[out] is_deterministic_out 1 if hashes match, 0 if not
 * @return DOSBOXX_OK on success (check is_deterministic_out for result)
 */
dosboxx_error_t dosboxx_verify_determinism(
    dosboxx_handle handle,
    uint64_t test_cycles,
    int* is_deterministic_out
);

/* =========================================================================
 * INTROSPECTION & ERROR HANDLING
 * ========================================================================= */

/**
 * @brief Get human-readable error message for last error.
 *
 * Two-call pattern:
 *   1. Call with buffer=NULL to get required length
 *   2. Call with buffer to get message
 *
 * @param handle Handle (may be NULL for global errors)
 * @param[out] buffer Output buffer (NULL to query size)
 * @param buffer_size Buffer size in bytes
 * @param[out] length_out Actual/required length including null terminator
 * @return DOSBOXX_OK on success
 */
dosboxx_error_t dosboxx_get_last_error(
    dosboxx_handle handle,
    char* buffer,
    size_t buffer_size,
    size_t* length_out
);

/**
 * @brief Log callback function type.
 *
 * @param level Log level (0=error, 1=warn, 2=info, 3=debug)
 * @param message Null-terminated message
 * @param userdata User-provided context
 */
typedef void (*dosboxx_log_callback_t)(
    int level,
    const char* message,
    void* userdata
);

/**
 * @brief Set log callback for debug output.
 *
 * @param handle Valid handle
 * @param callback Callback function (NULL to disable)
 * @param userdata Context passed to callback
 * @return DOSBOXX_OK on success
 */
dosboxx_error_t dosboxx_set_log_callback(
    dosboxx_handle handle,
    dosboxx_log_callback_t callback,
    void* userdata
);

#ifdef __cplusplus
}
#endif

#endif /* DOSBOXX_EMBED_H */
