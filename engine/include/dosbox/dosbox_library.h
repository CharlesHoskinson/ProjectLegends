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

#ifdef __cplusplus
}
#endif

#endif /* DOSBOX_DOSBOX_LIBRARY_H */
