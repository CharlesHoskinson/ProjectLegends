/**
 * @file error_model.cpp
 * @brief Implementation of FAIL/PANIC/TRAP error model for DOSBox-X library mode.
 *
 * This implements the error handling infrastructure defined in error_model.h.
 * Thread-local storage is used for last error to support future multi-threading.
 *
 * @copyright GPL-2.0-or-later
 */

#include "dosbox/error_model.h"

#include <cstring>
#include <cstdio>
#include <atomic>
#include <mutex>

// ═══════════════════════════════════════════════════════════════════════════════
// Thread-Local Error Storage
// ═══════════════════════════════════════════════════════════════════════════════

namespace {

// Thread-local last error (safe for multi-threaded hosts)
thread_local dosbox_error g_last_error = {};
thread_local bool g_has_error = false;

// Handler storage (process-wide, protected by mutex)
std::mutex g_handler_mutex;
dosbox_error_handler g_panic_handler = nullptr;
void* g_panic_userdata = nullptr;
dosbox_error_handler g_trap_handler = nullptr;
void* g_trap_userdata = nullptr;

// Placeholder context state (full implementation in context module)
// For now, we track a simple failed flag
std::atomic<bool> g_context_failed{false};

/**
 * @brief Safely copy string to fixed buffer with truncation.
 */
void safe_strcpy(char* dest, size_t dest_size, const char* src) {
    if (!dest || dest_size == 0) return;
    if (!src) {
        dest[0] = '\0';
        return;
    }

    size_t src_len = std::strlen(src);
    size_t copy_len = (src_len < dest_size - 1) ? src_len : dest_size - 1;
    std::memcpy(dest, src, copy_len);
    dest[copy_len] = '\0';
}

} // anonymous namespace

// ═══════════════════════════════════════════════════════════════════════════════
// C API Implementation
// ═══════════════════════════════════════════════════════════════════════════════

extern "C" {

void dosbox_set_panic_handler(dosbox_error_handler handler, void* userdata) {
    std::lock_guard<std::mutex> lock(g_handler_mutex);
    g_panic_handler = handler;
    g_panic_userdata = userdata;
}

void dosbox_set_trap_handler(dosbox_error_handler handler, void* userdata) {
    std::lock_guard<std::mutex> lock(g_handler_mutex);
    g_trap_handler = handler;
    g_trap_userdata = userdata;
}

const dosbox_error* dosbox_get_last_error(void) {
    if (!g_has_error) {
        return nullptr;
    }
    return &g_last_error;
}

int dosbox_get_last_error_string(char* buffer, size_t buffer_size, size_t* out_length) {
    if (!buffer || buffer_size == 0) {
        return DOSBOX_ERR_INVALID_ARGUMENT;
    }

    if (!g_has_error) {
        buffer[0] = '\0';
        if (out_length) *out_length = 0;
        return DOSBOX_OK;
    }

    size_t msg_len = std::strlen(g_last_error.message);
    size_t copy_len = (msg_len < buffer_size - 1) ? msg_len : buffer_size - 1;
    std::memcpy(buffer, g_last_error.message, copy_len);
    buffer[copy_len] = '\0';

    if (out_length) *out_length = msg_len;

    return (copy_len < msg_len) ? DOSBOX_ERR_BUFFER_TOO_SMALL : DOSBOX_OK;
}

void dosbox_clear_last_error(void) {
    g_has_error = false;
    std::memset(&g_last_error, 0, sizeof(g_last_error));
}

const char* dosbox_error_code_name(dosbox_error_code code) {
    switch (code) {
        case DOSBOX_OK: return "OK";

        // General errors
        case DOSBOX_ERR_UNKNOWN: return "ERR_UNKNOWN";
        case DOSBOX_ERR_NOT_IMPLEMENTED: return "ERR_NOT_IMPLEMENTED";
        case DOSBOX_ERR_INVALID_ARGUMENT: return "ERR_INVALID_ARGUMENT";
        case DOSBOX_ERR_INVALID_STATE: return "ERR_INVALID_STATE";
        case DOSBOX_ERR_NOT_INITIALIZED: return "ERR_NOT_INITIALIZED";
        case DOSBOX_ERR_ALREADY_INITIALIZED: return "ERR_ALREADY_INITIALIZED";

        // Resource errors
        case DOSBOX_ERR_OUT_OF_MEMORY: return "ERR_OUT_OF_MEMORY";
        case DOSBOX_ERR_RESOURCE_EXHAUSTED: return "ERR_RESOURCE_EXHAUSTED";
        case DOSBOX_ERR_RESOURCE_BUSY: return "ERR_RESOURCE_BUSY";
        case DOSBOX_ERR_RESOURCE_NOT_FOUND: return "ERR_RESOURCE_NOT_FOUND";

        // I/O errors
        case DOSBOX_ERR_FILE_NOT_FOUND: return "ERR_FILE_NOT_FOUND";
        case DOSBOX_ERR_FILE_ACCESS_DENIED: return "ERR_FILE_ACCESS_DENIED";
        case DOSBOX_ERR_FILE_READ_ERROR: return "ERR_FILE_READ_ERROR";
        case DOSBOX_ERR_FILE_WRITE_ERROR: return "ERR_FILE_WRITE_ERROR";
        case DOSBOX_ERR_PATH_TOO_LONG: return "ERR_PATH_TOO_LONG";

        // Configuration errors
        case DOSBOX_ERR_CONFIG_PARSE: return "ERR_CONFIG_PARSE";
        case DOSBOX_ERR_CONFIG_VALUE: return "ERR_CONFIG_VALUE";
        case DOSBOX_ERR_CONFIG_SECTION: return "ERR_CONFIG_SECTION";

        // Emulation errors
        case DOSBOX_ERR_CPU: return "ERR_CPU";
        case DOSBOX_ERR_MEMORY: return "ERR_MEMORY";
        case DOSBOX_ERR_DMA: return "ERR_DMA";
        case DOSBOX_ERR_INTERRUPT: return "ERR_INTERRUPT";
        case DOSBOX_ERR_DEVICE: return "ERR_DEVICE";

        // FFI/API errors
        case DOSBOX_ERR_NULL_HANDLE: return "ERR_NULL_HANDLE";
        case DOSBOX_ERR_INVALID_HANDLE: return "ERR_INVALID_HANDLE";
        case DOSBOX_ERR_BUFFER_TOO_SMALL: return "ERR_BUFFER_TOO_SMALL";
        case DOSBOX_ERR_EXCEPTION: return "ERR_EXCEPTION";

        // Fatal errors
        case DOSBOX_ERR_PANIC: return "ERR_PANIC";
        case DOSBOX_ERR_TRAP: return "ERR_TRAP";
        case DOSBOX_ERR_FATAL: return "ERR_FATAL";

        default: return "ERR_UNKNOWN";
    }
}

} // extern "C"

// ═══════════════════════════════════════════════════════════════════════════════
// C++ Implementation
// ═══════════════════════════════════════════════════════════════════════════════

namespace dosbox {

// ─────────────────────────────────────────────────────────────────────────────
// Error Class Methods
// ─────────────────────────────────────────────────────────────────────────────

dosbox_error Error::to_ffi() const noexcept {
    dosbox_error err = {};
    err.code = static_cast<dosbox_error_code>(code_);
    err.subsystem_id = 0; // TODO: implement subsystem interning
    err.line = static_cast<uint32_t>(location_.line());

    safe_strcpy(err.file, sizeof(err.file), location_.file_name());
    safe_strcpy(err.function, sizeof(err.function), location_.function_name());
    safe_strcpy(err.message, sizeof(err.message), message_.c_str());

    return err;
}

Error Error::from_ffi(const dosbox_error& err) {
    return Error{
        static_cast<ErrorCode>(err.code),
        std::string(err.message)
    };
}

// ─────────────────────────────────────────────────────────────────────────────
// Internal Functions
// ─────────────────────────────────────────────────────────────────────────────

void set_last_error(const Error& error) noexcept {
    g_last_error = error.to_ffi();
    g_has_error = true;
}

Error panic_internal(const char* message, std::source_location loc) noexcept {
    Error error{ErrorCode::Panic, message ? message : "Unknown panic", loc};

    // Set last error for FFI retrieval
    set_last_error(error);

    // Mark context as failed
    g_context_failed.store(true, std::memory_order_release);

    // Invoke panic handler if set
    {
        std::lock_guard<std::mutex> lock(g_handler_mutex);
        if (g_panic_handler) {
            dosbox_error ffi_err = error.to_ffi();
            g_panic_handler(&ffi_err, g_panic_userdata);
        }
    }

    return error;
}

Error trap_internal(const char* message, std::source_location loc) noexcept {
    Error error{ErrorCode::Trap, message ? message : "Unknown trap", loc};

    // Set last error for FFI retrieval
    set_last_error(error);

    // Mark context as failed
    g_context_failed.store(true, std::memory_order_release);

    // Invoke trap handler if set
    bool has_handler = false;
    {
        std::lock_guard<std::mutex> lock(g_handler_mutex);
        if (g_trap_handler) {
            has_handler = true;
            dosbox_error ffi_err = error.to_ffi();
            g_trap_handler(&ffi_err, g_trap_userdata);
        }
    }

    // In standalone mode without handler, abort would be called here.
    // In library mode, we return the error and let the host decide.
#ifndef DOSBOX_LIBRARY_MODE
    if (!has_handler) {
        // Standalone mode: abort on unhandled TRAP
        std::abort();
    }
#endif
    (void)has_handler; // Suppress warning in library mode

    return error;
}

// ─────────────────────────────────────────────────────────────────────────────
// Context State (Placeholder - Full implementation in context module)
// ─────────────────────────────────────────────────────────────────────────────

DOSBoxContext* current_context() noexcept {
    // Placeholder: returns nullptr until context module is implemented
    // PR #9 will implement the full context structure
    return nullptr;
}

void set_context_state(DOSBoxContext* ctx, ContextState state) noexcept {
    (void)ctx;
    if (state == ContextState::Failed) {
        g_context_failed.store(true, std::memory_order_release);
    }
}

ContextState get_context_state(DOSBoxContext* ctx) noexcept {
    (void)ctx;
    if (g_context_failed.load(std::memory_order_acquire)) {
        return ContextState::Failed;
    }
    return ContextState::Created; // Placeholder
}

} // namespace dosbox
