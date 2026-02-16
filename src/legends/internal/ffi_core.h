/**
 * @file ffi_core.h
 * @brief C FFI API header with ABI versioning.
 *
 * This is the primary public header for the DOSBox core library.
 * All functions use C linkage for maximum compatibility with
 * foreign language bindings (Rust, Python, etc.).
 */

#ifndef LEGENDS_FFI_CORE_H
#define LEGENDS_FFI_CORE_H

#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ═══════════════════════════════════════════════════════════════════════════
 * ABI Version
 * ═══════════════════════════════════════════════════════════════════════════ */

/**
 * @brief ABI version components.
 *
 * - Major: Incompatible changes (structure layout, removed functions)
 * - Minor: Backward-compatible additions (new functions, new struct fields at end)
 * - Patch: Bug fixes only (no API changes)
 */
#define LEGENDS_ABI_VERSION_MAJOR 1
#define LEGENDS_ABI_VERSION_MINOR 0
#define LEGENDS_ABI_VERSION_PATCH 0

/**
 * @brief Packed ABI version number.
 *
 * Format: (major << 16) | (minor << 8) | patch
 */
#define LEGENDS_ABI_VERSION \
    ((LEGENDS_ABI_VERSION_MAJOR << 16) | \
     (LEGENDS_ABI_VERSION_MINOR << 8)  | \
     LEGENDS_ABI_VERSION_PATCH)

/* ═══════════════════════════════════════════════════════════════════════════
 * Handle Types
 * ═══════════════════════════════════════════════════════════════════════════ */

/**
 * @brief Opaque handle to emulator instance.
 *
 * Created by legends_create(), destroyed by legends_destroy().
 * Must be validated before each use.
 */
typedef struct legends_handle_s* legends_handle_t;

/**
 * @brief Opaque handle to event subscription.
 *
 * Created by legends_subscribe(), destroyed by legends_unsubscribe().
 */
typedef struct legends_subscription_s* legends_subscription_t;

/**
 * @brief Handle validation status codes.
 */
typedef enum {
    LEGENDS_HANDLE_VALID = 0,               /**< Handle is valid */
    LEGENDS_HANDLE_NULL = -1,               /**< Handle is null */
    LEGENDS_HANDLE_INVALID_GENERATION = -2, /**< Use-after-free detected */
    LEGENDS_HANDLE_WRONG_TYPE = -3,         /**< Type mismatch */
    LEGENDS_HANDLE_DESTROYED = -4           /**< Handle was freed */
} legends_handle_status_t;

/* ═══════════════════════════════════════════════════════════════════════════
 * Error Codes
 * ═══════════════════════════════════════════════════════════════════════════ */

/**
 * @brief Unified error codes returned by all API functions.
 *
 * Error code ranges:
 * - 0:         Success
 * - 1-99:      Common/general errors
 * - 100-199:   Hardware/emulation errors
 * - 200-299:   LLM subsystem errors
 * - 300-399:   Vision subsystem errors
 * - 900-999:   Fatal/internal errors
 */
typedef enum {
    /* ─────────────────────────────────────────────────────────────────────────
     * Success (0)
     * ───────────────────────────────────────────────────────────────────────── */
    LEGENDS_OK = 0,                         /**< Success */

    /* ─────────────────────────────────────────────────────────────────────────
     * Common Errors (1-99)
     * ───────────────────────────────────────────────────────────────────────── */
    LEGENDS_ERR_INVALID_PARAM = 1,          /**< Invalid parameter value */
    LEGENDS_ERR_INVALID_HANDLE = 2,         /**< Invalid or null handle */
    LEGENDS_ERR_NOT_INITIALIZED = 3,        /**< Instance not initialized */
    LEGENDS_ERR_ALREADY_INITIALIZED = 4,    /**< Instance already initialized */
    LEGENDS_ERR_INVALID_STATE = 5,          /**< Invalid state for operation */
    LEGENDS_ERR_BUFFER_TOO_SMALL = 6,       /**< Output buffer too small */
    LEGENDS_ERR_OUT_OF_MEMORY = 7,          /**< Memory allocation failed */
    LEGENDS_ERR_ABI_MISMATCH = 8,           /**< ABI version incompatible */
    LEGENDS_ERR_REGISTRY_FULL = 9,          /**< Handle registry full */
    LEGENDS_ERR_IO = 10,                    /**< I/O operation failed */
    LEGENDS_ERR_TIMEOUT = 11,               /**< Operation timed out */
    LEGENDS_ERR_NOT_SUPPORTED = 12,         /**< Operation not supported */

    /* ─────────────────────────────────────────────────────────────────────────
     * Hardware/Emulation Errors (100-199)
     * ───────────────────────────────────────────────────────────────────────── */
    LEGENDS_ERR_CPU = 100,                  /**< CPU emulation error */
    LEGENDS_ERR_DMA = 101,                  /**< DMA transfer error */
    LEGENDS_ERR_MEMORY = 102,               /**< Memory access error */
    LEGENDS_ERR_CONFIG = 103,               /**< Configuration error */
    LEGENDS_ERR_IO_PORT = 104,              /**< I/O port error */

    /* ─────────────────────────────────────────────────────────────────────────
     * LLM Subsystem Errors (200-299)
     * ───────────────────────────────────────────────────────────────────────── */
    LEGENDS_ERR_LLM_INVALID_JSON = 200,     /**< Invalid JSON input */
    LEGENDS_ERR_LLM_BATCH_TOO_LARGE = 201,  /**< Too many actions in batch */
    LEGENDS_ERR_LLM_ACTION_FAILED = 202,    /**< Action execution failed */
    LEGENDS_ERR_LLM_NOT_TEXT_MODE = 203,    /**< Not in text mode */

    /* ─────────────────────────────────────────────────────────────────────────
     * Vision Subsystem Errors (300-399)
     * ───────────────────────────────────────────────────────────────────────── */
    LEGENDS_ERR_VISION_NO_FRAMEBUFFER = 300,/**< No framebuffer available */
    LEGENDS_ERR_VISION_NOT_DIRTY = 301,     /**< Framebuffer unchanged */
    LEGENDS_ERR_VISION_INVALID_FORMAT = 302,/**< Invalid pixel format */
    LEGENDS_ERR_VISION_OVERLAY_NOT_FOUND = 303, /**< Overlay ID not found */

    /* ─────────────────────────────────────────────────────────────────────────
     * Fatal/Internal Errors (900-999)
     * ───────────────────────────────────────────────────────────────────────── */
    LEGENDS_ERR_EXCEPTION = 900,            /**< Internal exception occurred */
    LEGENDS_ERR_FATAL = 998,                /**< Fatal unrecoverable error */
    LEGENDS_ERR_INTERNAL = 999              /**< Internal/unknown error */
} legends_error_t;

/**
 * @brief Get human-readable error message for error code.
 *
 * @param error Error code
 * @return Static string describing the error
 */
const char* legends_error_message(legends_error_t error);

/* ═══════════════════════════════════════════════════════════════════════════
 * Version and Compatibility
 * ═══════════════════════════════════════════════════════════════════════════ */

/**
 * @brief Get library ABI version.
 *
 * @return Packed version number (major << 16 | minor << 8 | patch)
 */
uint32_t legends_get_abi_version(void);

/**
 * @brief Check if host ABI version is compatible with library.
 *
 * The library is compatible if:
 * - Major versions match exactly
 * - Library minor >= host minor (backward compatible)
 *
 * @param host_version Host's expected ABI version
 * @return 1 if compatible, 0 if not
 */
int legends_check_abi_compatible(uint32_t host_version);

/**
 * @brief Get version string.
 *
 * @return Static string like "1.0.0"
 */
const char* legends_get_version_string(void);

/* ═══════════════════════════════════════════════════════════════════════════
 * Handle Management
 * ═══════════════════════════════════════════════════════════════════════════ */

/**
 * @brief Create a new emulator instance.
 *
 * @param config_path Path to configuration file (or NULL for defaults)
 * @return Handle to instance, or NULL on failure
 */
legends_handle_t legends_create(const char* config_path);

/**
 * @brief Initialize the emulator instance.
 *
 * Must be called after legends_create() and before legends_step().
 *
 * @param handle Emulator handle
 * @return LEGENDS_OK on success, error code on failure
 */
legends_error_t legends_init(legends_handle_t handle);

/**
 * @brief Run emulator for specified number of milliseconds.
 *
 * Deterministic: always runs exactly the specified amount of
 * virtual time regardless of wall-clock time.
 *
 * @param handle Emulator handle
 * @param milliseconds Virtual milliseconds to run
 * @return Number of instructions executed, or negative error code
 */
int32_t legends_step(legends_handle_t handle, uint32_t milliseconds);

/**
 * @brief Gracefully stop the emulator.
 *
 * Signals the emulator to stop after the current instruction.
 * Does not destroy the instance.
 *
 * @param handle Emulator handle
 * @return LEGENDS_OK on success
 */
legends_error_t legends_stop(legends_handle_t handle);

/**
 * @brief Destroy an emulator instance.
 *
 * Frees all resources and invalidates the handle.
 * After this call, the handle must not be used.
 *
 * @param handle Emulator handle
 */
void legends_destroy(legends_handle_t handle);

/**
 * @brief Validate a handle without using it.
 *
 * @param handle Handle to validate
 * @return Validation status code
 */
legends_handle_status_t legends_validate_handle(legends_handle_t handle);

/**
 * @brief Get last error message.
 *
 * Returns a human-readable description of the last error
 * that occurred on this handle.
 *
 * @param handle Emulator handle (may be invalid)
 * @return Static error string, or empty string if no error
 */
const char* legends_last_error(legends_handle_t handle);

/* ═══════════════════════════════════════════════════════════════════════════
 * Memory Access
 * ═══════════════════════════════════════════════════════════════════════════ */

/**
 * @brief Read from guest memory.
 *
 * @param handle Emulator handle
 * @param address Linear address in guest memory
 * @param buffer Output buffer
 * @param size Number of bytes to read
 * @return Number of bytes read, or negative error code
 */
int32_t legends_memory_read(
    legends_handle_t handle,
    uint32_t address,
    void* buffer,
    size_t size
);

/**
 * @brief Write to guest memory.
 *
 * @param handle Emulator handle
 * @param address Linear address in guest memory
 * @param data Data to write
 * @param size Number of bytes to write
 * @return Number of bytes written, or negative error code
 */
int32_t legends_memory_write(
    legends_handle_t handle,
    uint32_t address,
    const void* data,
    size_t size
);

/**
 * @brief Get guest memory size.
 *
 * @param handle Emulator handle
 * @return Memory size in bytes, or 0 on error
 */
size_t legends_memory_size(legends_handle_t handle);

/* ═══════════════════════════════════════════════════════════════════════════
 * Input Injection
 * ═══════════════════════════════════════════════════════════════════════════ */

/**
 * @brief Inject keyboard event.
 *
 * @param handle Emulator handle
 * @param scancode AT scan code
 * @param is_pressed 1 for key down, 0 for key up
 * @return LEGENDS_OK on success
 */
legends_error_t legends_key_event(
    legends_handle_t handle,
    uint8_t scancode,
    int is_pressed
);

/**
 * @brief Inject mouse movement and button event.
 *
 * @param handle Emulator handle
 * @param delta_x Relative X movement
 * @param delta_y Relative Y movement
 * @param buttons Button state bitmask (bit 0=left, 1=right, 2=middle)
 * @return LEGENDS_OK on success
 */
legends_error_t legends_mouse_event(
    legends_handle_t handle,
    int16_t delta_x,
    int16_t delta_y,
    uint8_t buttons
);

/* ═══════════════════════════════════════════════════════════════════════════
 * Hypercall Bridge
 * ═══════════════════════════════════════════════════════════════════════════ */

/**
 * @brief Hypercall callback function type.
 *
 * @param command Hypercall command code
 * @param param_a First parameter
 * @param param_b Second parameter
 * @param user_data User-provided context
 * @return Response value to return to guest
 */
typedef uint32_t (*legends_hypercall_callback_t)(
    uint32_t command,
    uint32_t param_a,
    uint32_t param_b,
    void* user_data
);

/**
 * @brief Register hypercall handler.
 *
 * Only one handler can be registered at a time.
 * Pass NULL to unregister.
 *
 * @param handle Emulator handle
 * @param callback Callback function
 * @param user_data User data passed to callback
 * @return LEGENDS_OK on success
 */
legends_error_t legends_set_hypercall_handler(
    legends_handle_t handle,
    legends_hypercall_callback_t callback,
    void* user_data
);

/* ═══════════════════════════════════════════════════════════════════════════
 * Logging
 * ═══════════════════════════════════════════════════════════════════════════ */

/**
 * @brief Log level enumeration.
 */
typedef enum {
    LEGENDS_LOG_TRACE = 0,
    LEGENDS_LOG_DEBUG = 1,
    LEGENDS_LOG_INFO = 2,
    LEGENDS_LOG_WARN = 3,
    LEGENDS_LOG_ERROR = 4,
    LEGENDS_LOG_FATAL = 5
} legends_log_level_t;

/**
 * @brief Log callback function type.
 *
 * @param level Log level
 * @param component Component name (e.g., "CPU", "VGA")
 * @param message Log message
 * @param user_data User-provided context
 */
typedef void (*legends_log_callback_t)(
    legends_log_level_t level,
    const char* component,
    const char* message,
    void* user_data
);

/**
 * @brief Set log callback.
 *
 * @param handle Emulator handle
 * @param callback Callback function (NULL to disable)
 * @param user_data User data passed to callback
 * @param min_level Minimum level to log
 * @return LEGENDS_OK on success
 */
legends_error_t legends_set_log_callback(
    legends_handle_t handle,
    legends_log_callback_t callback,
    void* user_data,
    legends_log_level_t min_level
);

#ifdef __cplusplus
}
#endif

#endif /* LEGENDS_FFI_CORE_H */
