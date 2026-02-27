/**
 * @file dosbox_library.h
 * @brief DOSBox-X Embeddable Library C API (PR #22)
 *
 * This is the stable C ABI boundary for embedding DOSBox-X into host applications.
 * Designed to match ProjectLegends' legends_embed.h interface.
 *
 * DESIGN DECISIONS:
 * - Pure C API (C11 and C++23 compatible)
 * - Single instance per process (for determinism)
 * - Error codes return negative values on failure
 * - Two-call pattern for variable-size outputs
 * - All calls for a handle must be serialized by caller
 *
 * USAGE:
 *   dosbox_handle_t handle;
 *   dosbox_lib_create(NULL, &handle);
 *   dosbox_lib_init(handle);
 *   dosbox_lib_step_ms(handle, 100, &result);
 *   dosbox_lib_destroy(handle);
 *
 * @copyright GPL-2.0-or-later
 */

#ifndef DOSBOX_DOSBOX_LIBRARY_H
#define DOSBOX_DOSBOX_LIBRARY_H

#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* =========================================================================
 * VERSION & ABI
 * ========================================================================= */

#define DOSBOX_LIB_VERSION_MAJOR 1
#define DOSBOX_LIB_VERSION_MINOR 0
#define DOSBOX_LIB_VERSION_PATCH 0

#define DOSBOX_LIB_VERSION \
    ((DOSBOX_LIB_VERSION_MAJOR << 16) | \
     (DOSBOX_LIB_VERSION_MINOR << 8) | \
     DOSBOX_LIB_VERSION_PATCH)

/* =========================================================================
 * ERROR CODES (compatible with legends_embed.h)
 * ========================================================================= */

typedef int32_t dosbox_lib_error_t;

#define DOSBOX_LIB_OK                      0
#define DOSBOX_LIB_ERR_NULL_HANDLE        -1
#define DOSBOX_LIB_ERR_NULL_POINTER       -2
#define DOSBOX_LIB_ERR_ALREADY_CREATED    -3
#define DOSBOX_LIB_ERR_NOT_INITIALIZED    -4
#define DOSBOX_LIB_ERR_REENTRANT_CALL     -5
#define DOSBOX_LIB_ERR_BUFFER_TOO_SMALL   -6
#define DOSBOX_LIB_ERR_INVALID_CONFIG     -7
#define DOSBOX_LIB_ERR_INVALID_STATE      -8
#define DOSBOX_LIB_ERR_VERSION_MISMATCH   -9
#define DOSBOX_LIB_ERR_IO_FAILED         -10
#define DOSBOX_LIB_ERR_OUT_OF_MEMORY     -11
#define DOSBOX_LIB_ERR_NOT_SUPPORTED     -12
#define DOSBOX_LIB_ERR_INTERNAL          -13
#define DOSBOX_LIB_ERR_WRONG_THREAD      -14
#define DOSBOX_LIB_ERR_INVALID_HANDLE    -15

/* =========================================================================
 * HANDLE TYPE
 * ========================================================================= */

typedef struct dosbox_lib_instance* dosbox_lib_handle_t;

/* =========================================================================
 * CONFIGURATION
 * ========================================================================= */

/**
 * @brief Library mode configuration.
 */
typedef struct {
    uint32_t struct_size;           /**< sizeof(dosbox_lib_config_t) */
    uint32_t api_version;           /**< DOSBOX_LIB_VERSION */

    /* Memory */
    uint32_t memory_kb;             /**< Conventional memory in KB */
    uint32_t xms_kb;                /**< Extended memory in KB */
    uint32_t ems_kb;                /**< Expanded memory in KB */

    /* CPU */
    uint32_t cpu_cycles;            /**< Cycles per ms (0 = auto) */
    uint8_t  cpu_type;              /**< CPU type enum */
    uint8_t  _pad1[3];

    /* Machine */
    uint8_t  machine_type;          /**< Machine type enum */
    uint8_t  _pad2[3];

    /* Determinism */
    uint8_t  deterministic;         /**< 1 = deterministic mode */
    uint8_t  _pad3[3];

    /* Paths */
    const char* config_path;        /**< Path to .conf file (NULL = defaults) */
    const char* working_dir;        /**< Working directory (NULL = current) */

    /* Reserved */
    uint64_t _reserved[8];

} dosbox_lib_config_t;

/* Helper to initialize config with defaults */
#define DOSBOX_LIB_CONFIG_INIT { \
    sizeof(dosbox_lib_config_t), \
    DOSBOX_LIB_VERSION, \
    640, 0, 0, \
    3000, 0, {0, 0, 0}, \
    0, {0, 0, 0}, \
    1, {0, 0, 0}, \
    NULL, NULL, \
    {0, 0, 0, 0, 0, 0, 0, 0} \
}

/* =========================================================================
 * STEP RESULT
 * ========================================================================= */

#define DOSBOX_LIB_STOP_COMPLETED      0
#define DOSBOX_LIB_STOP_HALT           1
#define DOSBOX_LIB_STOP_BREAKPOINT     2
#define DOSBOX_LIB_STOP_ERROR          3
#define DOSBOX_LIB_STOP_USER_REQUEST   4
#define DOSBOX_LIB_STOP_CALLBACK       5

typedef struct {
    uint64_t cycles_executed;       /**< Actual CPU cycles executed */
    uint64_t emu_time_us;           /**< Emulated time in microseconds */
    uint32_t stop_reason;           /**< Stop reason code */
    uint32_t events_processed;      /**< Events fired during step */
} dosbox_lib_step_result_t;

/* =========================================================================
 * LIFECYCLE API
 * ========================================================================= */

/**
 * @brief Get API version.
 */
dosbox_lib_error_t dosbox_lib_get_version(
    uint32_t* major,
    uint32_t* minor,
    uint32_t* patch
);

/**
 * @brief Create emulator instance.
 *
 * @param config Configuration (NULL for defaults)
 * @param handle_out Receives handle on success
 * @return DOSBOX_LIB_OK on success
 */
dosbox_lib_error_t dosbox_lib_create(
    const dosbox_lib_config_t* config,
    dosbox_lib_handle_t* handle_out
);

/**
 * @brief Initialize created instance.
 *
 * Must be called before stepping.
 *
 * @param handle Instance handle
 * @return DOSBOX_LIB_OK on success
 */
dosbox_lib_error_t dosbox_lib_init(dosbox_lib_handle_t handle);

/**
 * @brief Destroy emulator instance.
 *
 * @param handle Handle from dosbox_lib_create()
 * @return DOSBOX_LIB_OK on success
 */
dosbox_lib_error_t dosbox_lib_destroy(dosbox_lib_handle_t handle);

/**
 * @brief Reset emulator to initial state.
 *
 * @param handle Valid handle
 * @return DOSBOX_LIB_OK on success
 */
dosbox_lib_error_t dosbox_lib_reset(dosbox_lib_handle_t handle);

/* =========================================================================
 * STEPPING API
 * ========================================================================= */

/**
 * @brief Step emulation by milliseconds.
 *
 * @param handle Valid handle
 * @param ms Milliseconds of emulated time
 * @param result_out Step result (may be NULL)
 * @return DOSBOX_LIB_OK on success
 */
dosbox_lib_error_t dosbox_lib_step_ms(
    dosbox_lib_handle_t handle,
    uint32_t ms,
    dosbox_lib_step_result_t* result_out
);

/**
 * @brief Step emulation by exact CPU cycles.
 *
 * @param handle Valid handle
 * @param cycles CPU cycles to execute
 * @param result_out Step result (may be NULL)
 * @return DOSBOX_LIB_OK on success
 */
dosbox_lib_error_t dosbox_lib_step_cycles(
    dosbox_lib_handle_t handle,
    uint64_t cycles,
    dosbox_lib_step_result_t* result_out
);

/**
 * @brief Get current emulated time.
 *
 * @param handle Valid handle
 * @param time_us_out Receives emulated time in microseconds
 * @return DOSBOX_LIB_OK on success
 */
dosbox_lib_error_t dosbox_lib_get_emu_time(
    dosbox_lib_handle_t handle,
    uint64_t* time_us_out
);

/**
 * @brief Get total CPU cycles executed.
 *
 * @param handle Valid handle
 * @param cycles_out Receives total cycles
 * @return DOSBOX_LIB_OK on success
 */
dosbox_lib_error_t dosbox_lib_get_total_cycles(
    dosbox_lib_handle_t handle,
    uint64_t* cycles_out
);

/* =========================================================================
 * CONTEXT ACCESS API
 * ========================================================================= */

/**
 * @brief Get raw pointer to the internal DOSBoxContext.
 *
 * Used by the legends layer to set dosbox::ContextGuard before stepping.
 * The returned pointer is valid for the lifetime of the handle.
 *
 * @param handle Valid handle
 * @param ctx_out Receives opaque context pointer
 * @return DOSBOX_LIB_OK on success
 */
dosbox_lib_error_t dosbox_lib_get_context_ptr(
    dosbox_lib_handle_t handle,
    void** ctx_out
);

/* =========================================================================
 * STATE API
 * ========================================================================= */

/**
 * @brief Get SHA-256 hash of current state.
 *
 * @param handle Valid handle
 * @param hash_out 32-byte buffer for hash
 * @return DOSBOX_LIB_OK on success
 */
dosbox_lib_error_t dosbox_lib_get_state_hash(
    dosbox_lib_handle_t handle,
    uint8_t hash_out[32]
);

/**
 * @brief Save complete machine state.
 *
 * Two-call pattern: call with buffer=NULL to get required size.
 *
 * @param handle Valid handle
 * @param buffer Output buffer (NULL to query size)
 * @param buffer_size Buffer size in bytes
 * @param size_out Actual/required byte count
 * @return DOSBOX_LIB_OK on success
 */
dosbox_lib_error_t dosbox_lib_save_state(
    dosbox_lib_handle_t handle,
    void* buffer,
    size_t buffer_size,
    size_t* size_out
);

/**
 * @brief Load machine state from buffer.
 *
 * @param handle Valid handle
 * @param buffer State data
 * @param buffer_size Size of state data
 * @return DOSBOX_LIB_OK on success
 */
dosbox_lib_error_t dosbox_lib_load_state(
    dosbox_lib_handle_t handle,
    const void* buffer,
    size_t buffer_size
);

/* =========================================================================
 * ERROR HANDLING
 * ========================================================================= */

/**
 * @brief Get human-readable error message.
 *
 * @param handle Handle (may be NULL for global errors)
 * @param buffer Output buffer (NULL to query size)
 * @param buffer_size Buffer size
 * @param length_out Actual/required length
 * @return DOSBOX_LIB_OK on success
 */
dosbox_lib_error_t dosbox_lib_get_last_error(
    dosbox_lib_handle_t handle,
    char* buffer,
    size_t buffer_size,
    size_t* length_out
);

/**
 * @brief Log callback function type.
 */
typedef void (*dosbox_lib_log_callback_t)(
    int level,
    const char* message,
    void* userdata
);

/**
 * @brief Set log callback.
 *
 * @param handle Valid handle
 * @param callback Callback function (NULL to disable)
 * @param userdata Context passed to callback
 * @return DOSBOX_LIB_OK on success
 */
dosbox_lib_error_t dosbox_lib_set_log_callback(
    dosbox_lib_handle_t handle,
    dosbox_lib_log_callback_t callback,
    void* userdata
);

/* =========================================================================
 * INPUT INJECTION API
 * ========================================================================= */

/**
 * @brief Inject keyboard scancode into the emulator.
 *
 * Forwards keyboard input directly to the engine's keyboard controller.
 * Called by legends layer to drain input queue before stepping.
 *
 * @param handle Valid handle
 * @param scancode AT scancode (set 1)
 * @param pressed 1 for key press, 0 for key release
 * @param extended 1 for E0-prefixed keys (arrows, etc.)
 * @return DOSBOX_LIB_OK on success
 */
dosbox_lib_error_t dosbox_lib_inject_key(
    dosbox_lib_handle_t handle,
    uint8_t scancode,
    int pressed,
    int extended
);

/**
 * @brief Inject mouse movement and button state into the emulator.
 *
 * Forwards mouse input directly to the engine's PS/2 aux port.
 * Called by legends layer to drain input queue before stepping.
 *
 * @param handle Valid handle
 * @param delta_x Relative X movement
 * @param delta_y Relative Y movement
 * @param buttons Button bitmask (bit 0=left, 1=right, 2=middle)
 * @return DOSBOX_LIB_OK on success
 */
dosbox_lib_error_t dosbox_lib_inject_mouse(
    dosbox_lib_handle_t handle,
    int16_t delta_x,
    int16_t delta_y,
    uint8_t buttons
);

/* =========================================================================
 * MEMORY ACCESS API
 * ========================================================================= */

/**
 * @brief Read from guest physical memory.
 *
 * @param handle Valid handle
 * @param address Guest physical address
 * @param buffer Output buffer
 * @param size Bytes to read
 * @return DOSBOX_LIB_OK on success
 */
dosbox_lib_error_t dosbox_lib_read_memory(
    dosbox_lib_handle_t handle,
    uint32_t address,
    void* buffer,
    size_t size
);

/**
 * @brief Write to guest physical memory.
 *
 * @param handle Valid handle
 * @param address Guest physical address
 * @param buffer Data to write
 * @param size Bytes to write
 * @return DOSBOX_LIB_OK on success
 */
dosbox_lib_error_t dosbox_lib_write_memory(
    dosbox_lib_handle_t handle,
    const void* buffer,
    uint32_t address,
    size_t size
);

/* =========================================================================
 * PIC STATE API
 * ========================================================================= */

/**
 * @brief PIC (Programmable Interrupt Controller) state structure.
 *
 * Used to sync PIC state from engine to legends layer for hash consistency.
 */
typedef struct {
    uint8_t master_irr;  /**< Master PIC Interrupt Request Register */
    uint8_t master_imr;  /**< Master PIC Interrupt Mask Register */
    uint8_t master_isr;  /**< Master PIC In-Service Register */
    uint8_t slave_irr;   /**< Slave PIC Interrupt Request Register */
    uint8_t slave_imr;   /**< Slave PIC Interrupt Mask Register */
    uint8_t slave_isr;   /**< Slave PIC In-Service Register */
} dosbox_lib_pic_state_t;

/**
 * @brief Get current PIC state from the engine.
 *
 * Used by legends layer to sync PIC state for deterministic hashing.
 *
 * @param handle Valid handle
 * @param state_out Receives PIC state
 * @return DOSBOX_LIB_OK on success
 */
dosbox_lib_error_t dosbox_lib_get_pic_state(
    dosbox_lib_handle_t handle,
    dosbox_lib_pic_state_t* state_out
);

/* =========================================================================
 * PHASE 3: ENHANCED FEATURES BRIDGE API
 * ========================================================================= */

/* --- PC-98 Machine Type --- */

dosbox_lib_error_t dosbox_lib_set_machine_pc98(dosbox_lib_handle_t handle, int enable);
dosbox_lib_error_t dosbox_lib_is_pc98_mode(dosbox_lib_handle_t handle, int* out);

/* --- 3dfx Glide --- */

dosbox_lib_error_t dosbox_lib_glide_enable(dosbox_lib_handle_t handle, int enable);
dosbox_lib_error_t dosbox_lib_glide_set_resolution(dosbox_lib_handle_t handle, uint16_t w, uint16_t h);

/* --- Printer --- */

dosbox_lib_error_t dosbox_lib_printer_set_output(dosbox_lib_handle_t handle, const char* path);
dosbox_lib_error_t dosbox_lib_printer_is_active(dosbox_lib_handle_t handle, int* out);
dosbox_lib_error_t dosbox_lib_printer_flush(dosbox_lib_handle_t handle);

/* --- IPX Networking --- */

dosbox_lib_error_t dosbox_lib_ipx_enable(dosbox_lib_handle_t handle, int enable);
dosbox_lib_error_t dosbox_lib_ipx_connect(dosbox_lib_handle_t handle, const char* server, uint16_t port);
dosbox_lib_error_t dosbox_lib_ipx_disconnect(dosbox_lib_handle_t handle);
dosbox_lib_error_t dosbox_lib_ipx_is_connected(dosbox_lib_handle_t handle, int* out);

/* --- MIDI & Synthesis --- */

dosbox_lib_error_t dosbox_lib_midi_set_device(dosbox_lib_handle_t handle, const char* device_type);
dosbox_lib_error_t dosbox_lib_midi_set_soundfont(dosbox_lib_handle_t handle, const char* sf2_path);
dosbox_lib_error_t dosbox_lib_midi_set_romdir(dosbox_lib_handle_t handle, const char* rom_dir);
dosbox_lib_error_t dosbox_lib_midi_capture_audio(dosbox_lib_handle_t handle, int16_t* buf, size_t count, size_t* out);

/* =========================================================================
 * VGA/DISPLAY STATE API (H8)
 * ========================================================================= */

/**
 * @brief Display mode information from the engine.
 */
typedef struct {
    uint16_t width;          /**< Display width in pixels */
    uint16_t height;         /**< Display height in pixels */
    uint8_t  bpp;            /**< Bits per pixel */
    uint8_t  is_text_mode;   /**< 1 if text mode, 0 if graphics */
    uint8_t  text_columns;   /**< Text mode columns (typically 80) */
    uint8_t  text_rows;      /**< Text mode rows (typically 25) */
} dosbox_lib_display_info_t;

/**
 * @brief Get current display mode info from the engine.
 *
 * @param handle Valid handle
 * @param info_out Receives display info
 * @return DOSBOX_LIB_OK on success
 */
dosbox_lib_error_t dosbox_lib_get_display_info(
    dosbox_lib_handle_t handle,
    dosbox_lib_display_info_t* info_out
);

/* =========================================================================
 * VGA DATA ACCESS API (Phase -1: Engine I/O Plumbing)
 * ========================================================================= */

/**
 * @brief Get VGA text buffer contents.
 *
 * Two-call pattern: call with buffer=NULL to get cell count.
 * Each cell is uint16_t: low byte = character, high byte = attribute.
 * Count = text_columns × text_rows.
 *
 * @param handle Valid handle
 * @param buffer Output buffer (NULL to query count)
 * @param buffer_count Buffer capacity in uint16_t elements
 * @param count_out Actual/required cell count
 * @return DOSBOX_LIB_OK on success
 */
dosbox_lib_error_t dosbox_lib_get_text_buffer(
    dosbox_lib_handle_t handle,
    uint16_t* buffer,
    size_t buffer_count,
    size_t* count_out
);

/**
 * @brief Get VGA indexed pixel data (graphics modes).
 *
 * Two-call pattern: call with buffer=NULL to get required size.
 * Returns 8bpp indexed pixels for Mode 13h (320×200).
 * Returns DOSBOX_LIB_ERR_NOT_SUPPORTED for planar modes.
 *
 * @param handle Valid handle
 * @param buffer Output buffer (NULL to query size)
 * @param buffer_size Buffer size in bytes
 * @param size_out Actual/required byte count
 * @return DOSBOX_LIB_OK on success
 */
dosbox_lib_error_t dosbox_lib_get_indexed_pixels(
    dosbox_lib_handle_t handle,
    uint8_t* buffer,
    size_t buffer_size,
    size_t* size_out
);

/**
 * @brief Get VGA DAC palette (256 RGB triplets).
 *
 * Reads the VGA DAC and scales 6-bit values to 8-bit.
 * Output is 768 bytes: 256 entries × 3 bytes (R, G, B).
 *
 * @param handle Valid handle
 * @param rgb_out 768-byte output buffer
 * @return DOSBOX_LIB_OK on success
 */
dosbox_lib_error_t dosbox_lib_get_palette(
    dosbox_lib_handle_t handle,
    uint8_t rgb_out[768]
);

/**
 * @brief Get VGA font data (1bpp glyph bitmaps).
 *
 * Two-call pattern: call with buffer=NULL to get required size.
 * Returns 256 characters × char_height bytes of 1bpp bitmap data.
 *
 * @param handle Valid handle
 * @param buffer Output buffer (NULL to query size)
 * @param buffer_size Buffer size in bytes
 * @param size_out Actual/required byte count
 * @param char_height_out Receives scanlines per character (typically 16)
 * @return DOSBOX_LIB_OK on success
 */
dosbox_lib_error_t dosbox_lib_get_font_data(
    dosbox_lib_handle_t handle,
    uint8_t* buffer,
    size_t buffer_size,
    size_t* size_out,
    uint8_t* char_height_out
);

/* =========================================================================
 * AUDIO API (Phase -1: Engine I/O Plumbing)
 * ========================================================================= */

/**
 * @brief Enable or disable audio before instance creation.
 *
 * Must be called before dosbox_lib_create() to take effect.
 * handle may be NULL (pre-create global setting).
 *
 * @param handle Handle (may be NULL for pre-create setting)
 * @param enabled 1 to enable audio, 0 to disable
 * @return DOSBOX_LIB_OK on success
 */
dosbox_lib_error_t dosbox_lib_set_audio_enabled(
    dosbox_lib_handle_t handle,
    int enabled
);

/**
 * @brief Get audio samples from the engine (destructive read).
 *
 * Two-call pattern: call with buffer=NULL to query available count.
 * Pops samples from the engine's audio ring buffer.
 * Samples are interleaved S16LE stereo at 44100 Hz.
 *
 * @param handle Valid handle
 * @param buffer Output buffer (NULL to query available count)
 * @param buffer_count Buffer capacity in int16_t elements
 * @param count_out Available/actual sample count
 * @return DOSBOX_LIB_OK on success
 */
dosbox_lib_error_t dosbox_lib_get_audio_samples(
    dosbox_lib_handle_t handle,
    int16_t* buffer,
    size_t buffer_count,
    size_t* count_out
);

// ═══════════════════════════════════════════════════════════════════════════════
// Display API — Cursor
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Cursor information read from the BIOS Data Area.
 */
typedef struct {
    uint8_t col;            /**< Cursor column */
    uint8_t row;            /**< Cursor row */
    uint8_t active_page;    /**< Active display page */
    uint8_t visible;        /**< 1 = visible, 0 = hidden */
    uint8_t start_line;     /**< Cursor start scanline */
    uint8_t end_line;       /**< Cursor end scanline */
} dosbox_lib_cursor_info_t;

/**
 * @brief Get cursor position and shape from the BIOS Data Area.
 *
 * @param handle Valid handle
 * @param info_out Receives cursor information
 * @return DOSBOX_LIB_OK on success
 */
dosbox_lib_error_t dosbox_lib_get_cursor_info(
    dosbox_lib_handle_t handle,
    dosbox_lib_cursor_info_t* info_out
);

#ifdef __cplusplus
}
#endif

#endif /* DOSBOX_DOSBOX_LIBRARY_H */
