/**
 * @file ffi.h
 * @brief FFI (Foreign Function Interface) utilities for C API.
 *
 * Provides:
 * - Thread-local error storage
 * - Exception-safe FFI wrapper
 * - Error code definitions (via ffi_core.h)
 *
 * Requirements implemented:
 * - REQ-FND-006: Catch all exceptions at FFI boundaries
 * - REQ-FND-007: Thread-local error message storage
 * - REQ-FND-011: Store message and return error code on exception
 */

#pragma once

#include "exceptions.h"
#include "ffi_core.h"
#include <cstring>
#include <format>

// ─────────────────────────────────────────────────────────────────────────────
// FFI Error Codes (from ffi_core.h)
// ─────────────────────────────────────────────────────────────────────────────

/* All error codes are now defined in ffi_core.h as the unified legends_error_t enum.
 * This file uses those codes for exception-to-error-code mapping.
 *
 * Hardware/emulation error codes (100-199):
 *   LEGENDS_ERR_CPU      = 100
 *   LEGENDS_ERR_DMA      = 101
 *   LEGENDS_ERR_MEMORY   = 102
 *   LEGENDS_ERR_CONFIG   = 103
 *   LEGENDS_ERR_IO_PORT  = 104
 */

#ifdef __cplusplus

namespace legends {
namespace ffi {

// ─────────────────────────────────────────────────────────────────────────────
// Thread-Local Error Storage
// ─────────────────────────────────────────────────────────────────────────────

namespace detail {

/** @brief Maximum size of error message buffer */
inline constexpr size_t ERROR_BUFFER_SIZE = 2048;

/** @brief Thread-local error message storage */
inline thread_local char g_last_error[ERROR_BUFFER_SIZE] = {0};

/** @brief Flag indicating if error was truncated */
inline thread_local bool g_error_truncated = false;

} // namespace detail

/**
 * @brief Store error message in thread-local storage.
 * @param msg Error message (will be truncated if too long)
 */
inline void set_error(const char* msg) {
    size_t len = std::strlen(msg);
    if (len >= detail::ERROR_BUFFER_SIZE) {
        std::memcpy(detail::g_last_error, msg, detail::ERROR_BUFFER_SIZE - 4);
        std::memcpy(detail::g_last_error + detail::ERROR_BUFFER_SIZE - 4, "...", 4);
        detail::g_error_truncated = true;
    } else {
        std::memcpy(detail::g_last_error, msg, len + 1);
        detail::g_error_truncated = false;
    }
}

/**
 * @brief Store formatted error message using std::format.
 *
 * Uses std::format_to_n for bounded output to stack buffer.
 */
template<typename... Args>
void set_error_fmt(std::format_string<Args...> fmt, Args&&... args) {
    auto result = std::format_to_n(
        detail::g_last_error,
        detail::ERROR_BUFFER_SIZE - 1,
        fmt,
        std::forward<Args>(args)...
    );
    *result.out = '\0';  // Null-terminate
    detail::g_error_truncated = (static_cast<size_t>(result.size) >= detail::ERROR_BUFFER_SIZE);
}

/**
 * @brief Get last error message.
 * @return Error message or empty string if no error
 */
inline const char* get_error() noexcept {
    return detail::g_last_error;
}

/**
 * @brief Check if last error was truncated.
 * @return true if message was truncated
 */
inline bool error_truncated() noexcept {
    return detail::g_error_truncated;
}

/**
 * @brief Clear error state.
 */
inline void clear_error() noexcept {
    detail::g_last_error[0] = '\0';
    detail::g_error_truncated = false;
}

// ─────────────────────────────────────────────────────────────────────────────
// Exception-Safe FFI Wrapper
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Wrap FFI function with exception handling.
 *
 * Catches all exceptions and converts to error codes.
 * Stores error message in thread-local storage.
 *
 * @tparam F Function type (must return int)
 * @param func Function to call
 * @return LEGENDS_OK on success, error code on failure
 *
 * Example:
 * @code
 * extern "C" int legends_init(legends_handle_t* handle) {
 *     return legends::ffi::safe_call([&]() {
 *         if (!handle) {
 *             legends::ffi::set_error("Null handle pointer");
 *             return LEGENDS_ERR_INVALID_PARAM;
 *         }
 *         *handle = new AiboxContext();
 *         return LEGENDS_OK;
 *     });
 * }
 * @endcode
 */
template<typename F>
int safe_call(F&& func) noexcept {
    clear_error();

    try {
        return func();
    }
    catch (const IllegalCpuStateException& e) {
        set_error_fmt("CPU error: {}", e.what());
        return LEGENDS_ERR_CPU;
    }
    catch (const DmaException& e) {
        set_error_fmt("DMA error: {}", e.what());
        return LEGENDS_ERR_DMA;
    }
    catch (const MemoryAccessException& e) {
        set_error_fmt("Memory error at 0x{:08X}: {}", e.address(), e.what());
        return LEGENDS_ERR_MEMORY;
    }
    catch (const ConfigException& e) {
        set_error_fmt("Config error: {}", e.what());
        return LEGENDS_ERR_CONFIG;
    }
    catch (const IoPortException& e) {
        set_error_fmt("I/O error at 0x{:04X}: {}", e.port(), e.what());
        return LEGENDS_ERR_IO_PORT;
    }
    catch (const FatalException& e) {
        set_error_fmt("Fatal: {}", e.what());
        return LEGENDS_ERR_FATAL;
    }
    catch (const CallbackException& e) {
        set_error_fmt("Callback error: {}", e.what());
        return LEGENDS_ERR_INTERNAL;
    }
    catch (const EmulatorException& e) {
        set_error_fmt("Emulator error: {}", e.what());
        return LEGENDS_ERR_INTERNAL;
    }
    catch (const std::bad_alloc&) {
        set_error("Out of memory");
        return LEGENDS_ERR_MEMORY;
    }
    catch (const std::exception& e) {
        set_error_fmt("Unexpected error: {}", e.what());
        return LEGENDS_ERR_INTERNAL;
    }
    catch (...) {
        set_error("Unknown exception");
        return LEGENDS_ERR_INTERNAL;
    }
}

/**
 * @brief Convert error code to human-readable string.
 * @note Uses unified legends_error_t codes from ffi_core.h.
 */
inline const char* error_code_string(int code) noexcept {
    switch (code) {
        // Success
        case LEGENDS_OK: return "OK";

        // Common errors (1-99)
        case LEGENDS_ERR_INVALID_PARAM: return "Invalid parameter";
        case LEGENDS_ERR_INVALID_HANDLE: return "Invalid handle";
        case LEGENDS_ERR_NOT_INITIALIZED: return "Not initialized";
        case LEGENDS_ERR_ALREADY_INITIALIZED: return "Already initialized";
        case LEGENDS_ERR_INVALID_STATE: return "Invalid state";
        case LEGENDS_ERR_BUFFER_TOO_SMALL: return "Buffer too small";
        case LEGENDS_ERR_OUT_OF_MEMORY: return "Out of memory";
        case LEGENDS_ERR_ABI_MISMATCH: return "ABI mismatch";
        case LEGENDS_ERR_REGISTRY_FULL: return "Registry full";
        case LEGENDS_ERR_IO: return "I/O error";
        case LEGENDS_ERR_TIMEOUT: return "Timeout";
        case LEGENDS_ERR_NOT_SUPPORTED: return "Not supported";

        // Hardware/emulation errors (100-199)
        case LEGENDS_ERR_CPU: return "CPU error";
        case LEGENDS_ERR_DMA: return "DMA error";
        case LEGENDS_ERR_MEMORY: return "Memory error";
        case LEGENDS_ERR_CONFIG: return "Configuration error";
        case LEGENDS_ERR_IO_PORT: return "I/O port error";

        // LLM errors (200-299)
        case LEGENDS_ERR_LLM_INVALID_JSON: return "Invalid JSON";
        case LEGENDS_ERR_LLM_BATCH_TOO_LARGE: return "Batch too large";
        case LEGENDS_ERR_LLM_ACTION_FAILED: return "Action failed";
        case LEGENDS_ERR_LLM_NOT_TEXT_MODE: return "Not in text mode";

        // Vision errors (300-399)
        case LEGENDS_ERR_VISION_NO_FRAMEBUFFER: return "No framebuffer";
        case LEGENDS_ERR_VISION_NOT_DIRTY: return "Framebuffer unchanged";
        case LEGENDS_ERR_VISION_INVALID_FORMAT: return "Invalid format";
        case LEGENDS_ERR_VISION_OVERLAY_NOT_FOUND: return "Overlay not found";

        // Fatal/internal errors (900-999)
        case LEGENDS_ERR_EXCEPTION: return "Exception occurred";
        case LEGENDS_ERR_FATAL: return "Fatal error";
        case LEGENDS_ERR_INTERNAL: return "Internal error";

        default: return "Unknown error";
    }
}

} // namespace ffi
} // namespace legends

#endif // __cplusplus

// ─────────────────────────────────────────────────────────────────────────────
// Thread-Local C API for Error Handling
// ─────────────────────────────────────────────────────────────────────────────
// These functions use thread-local storage, separate from ffi_core.h's
// handle-based error storage. Use legends_ffi_* for thread-local errors
// and legends_last_error(handle) for handle-specific errors.

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Get last error message for current thread (thread-local).
 * @return Error message or empty string if no error
 * @note This is separate from legends_last_error(handle) in ffi_core.h
 */
inline const char* legends_ffi_last_error(void) {
#ifdef __cplusplus
    return legends::ffi::get_error();
#else
    return "";
#endif
}

/**
 * @brief Check if last thread-local error was truncated.
 * @return 1 if truncated, 0 otherwise
 */
inline int legends_ffi_error_truncated(void) {
#ifdef __cplusplus
    return legends::ffi::error_truncated() ? 1 : 0;
#else
    return 0;
#endif
}

/**
 * @brief Clear thread-local error.
 */
inline void legends_ffi_clear_error(void) {
#ifdef __cplusplus
    legends::ffi::clear_error();
#endif
}

/**
 * @brief Get human-readable string for error code.
 * @param code Error code
 * @return String description of error code
 */
inline const char* legends_ffi_error_string(int code) {
#ifdef __cplusplus
    return legends::ffi::error_code_string(code);
#else
    return "Unknown";
#endif
}

#ifdef __cplusplus
}
#endif
