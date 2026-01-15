/**
 * @file error_model.h
 * @brief FAIL/PANIC/TRAP error taxonomy for DOSBox-X library mode.
 *
 * This file implements the three-level error model defined in LIBRARY_CONTRACT.md:
 *
 * | Level | Macro          | Behavior                              |
 * |-------|----------------|---------------------------------------|
 * | FAIL  | DOSBOX_FAIL    | Returns Result::error (recoverable)   |
 * | PANIC | DOSBOX_PANIC   | Context → Failed state, returns fatal |
 * | TRAP  | DOSBOX_TRAP    | Calls host handler (memory corruption)|
 *
 * Usage:
 * - DOSBOX_FAIL: For recoverable errors (invalid input, missing files)
 * - DOSBOX_PANIC: For internal invariant violations (bugs, should never happen)
 * - DOSBOX_TRAP: For unrecoverable memory corruption (extremely rare)
 *
 * @copyright GPL-2.0-or-later
 */

#ifndef DOSBOX_ERROR_MODEL_H
#define DOSBOX_ERROR_MODEL_H

#include <cstdint>
#include <cstddef>

#ifdef __cplusplus
#include <string>
#include <functional>
#include <source_location>
#include <expected>
#include <format>
#endif

// ═══════════════════════════════════════════════════════════════════════════════
// C ABI Types (FFI-safe)
// ═══════════════════════════════════════════════════════════════════════════════

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Error codes for DOSBox-X library mode.
 *
 * These codes are stable across versions and safe for FFI.
 */
typedef enum dosbox_error_code {
    DOSBOX_OK = 0,

    /* General errors (1-99) */
    DOSBOX_ERR_UNKNOWN = 1,
    DOSBOX_ERR_NOT_IMPLEMENTED = 2,
    DOSBOX_ERR_INVALID_ARGUMENT = 3,
    DOSBOX_ERR_INVALID_STATE = 4,
    DOSBOX_ERR_NOT_INITIALIZED = 5,
    DOSBOX_ERR_ALREADY_INITIALIZED = 6,

    /* Resource errors (100-199) */
    DOSBOX_ERR_OUT_OF_MEMORY = 100,
    DOSBOX_ERR_RESOURCE_EXHAUSTED = 101,
    DOSBOX_ERR_RESOURCE_BUSY = 102,
    DOSBOX_ERR_RESOURCE_NOT_FOUND = 103,

    /* I/O errors (200-299) */
    DOSBOX_ERR_FILE_NOT_FOUND = 200,
    DOSBOX_ERR_FILE_ACCESS_DENIED = 201,
    DOSBOX_ERR_FILE_READ_ERROR = 202,
    DOSBOX_ERR_FILE_WRITE_ERROR = 203,
    DOSBOX_ERR_PATH_TOO_LONG = 204,

    /* Configuration errors (300-399) */
    DOSBOX_ERR_CONFIG_PARSE = 300,
    DOSBOX_ERR_CONFIG_VALUE = 301,
    DOSBOX_ERR_CONFIG_SECTION = 302,

    /* Emulation errors (400-499) */
    DOSBOX_ERR_CPU = 400,
    DOSBOX_ERR_MEMORY = 401,
    DOSBOX_ERR_DMA = 402,
    DOSBOX_ERR_INTERRUPT = 403,
    DOSBOX_ERR_DEVICE = 404,

    /* FFI/API errors (500-599) */
    DOSBOX_ERR_NULL_HANDLE = 500,
    DOSBOX_ERR_INVALID_HANDLE = 501,
    DOSBOX_ERR_BUFFER_TOO_SMALL = 502,
    DOSBOX_ERR_EXCEPTION = 503,

    /* Fatal errors (900-999) */
    DOSBOX_ERR_PANIC = 900,
    DOSBOX_ERR_TRAP = 901,
    DOSBOX_ERR_FATAL = 999
} dosbox_error_code;

/**
 * @brief FFI-safe error structure.
 *
 * Contains no pointers that could dangle across FFI boundary.
 * All string data is either interned or in fixed buffers.
 */
typedef struct dosbox_error {
    dosbox_error_code code;
    uint32_t subsystem_id;          /* Interned subsystem identifier */
    uint32_t line;                  /* Source line number */
    char file[64];                  /* Source file name (truncated) */
    char function[64];              /* Function name (truncated) */
    char message[256];              /* Formatted error message */
} dosbox_error;

/**
 * @brief Error handler callback type.
 *
 * Called when DOSBOX_PANIC or DOSBOX_TRAP is invoked.
 * @param error The error details
 * @param userdata User-provided context
 */
typedef void (*dosbox_error_handler)(const dosbox_error* error, void* userdata);

/* Handler management */
void dosbox_set_panic_handler(dosbox_error_handler handler, void* userdata);
void dosbox_set_trap_handler(dosbox_error_handler handler, void* userdata);

/* Error retrieval */
const dosbox_error* dosbox_get_last_error(void);
int dosbox_get_last_error_string(char* buffer, size_t buffer_size, size_t* out_length);
void dosbox_clear_last_error(void);

/* Error code to string */
const char* dosbox_error_code_name(dosbox_error_code code);

#ifdef __cplusplus
} /* extern "C" */
#endif

// ═══════════════════════════════════════════════════════════════════════════════
// C++ API
// ═══════════════════════════════════════════════════════════════════════════════

#ifdef __cplusplus

namespace dosbox {

// ─────────────────────────────────────────────────────────────────────────────
// Error Code (C++ enum class wrapper)
// ─────────────────────────────────────────────────────────────────────────────

enum class ErrorCode : int {
    Ok = DOSBOX_OK,

    Unknown = DOSBOX_ERR_UNKNOWN,
    NotImplemented = DOSBOX_ERR_NOT_IMPLEMENTED,
    InvalidArgument = DOSBOX_ERR_INVALID_ARGUMENT,
    InvalidState = DOSBOX_ERR_INVALID_STATE,
    NotInitialized = DOSBOX_ERR_NOT_INITIALIZED,
    AlreadyInitialized = DOSBOX_ERR_ALREADY_INITIALIZED,

    OutOfMemory = DOSBOX_ERR_OUT_OF_MEMORY,
    ResourceExhausted = DOSBOX_ERR_RESOURCE_EXHAUSTED,
    ResourceBusy = DOSBOX_ERR_RESOURCE_BUSY,
    ResourceNotFound = DOSBOX_ERR_RESOURCE_NOT_FOUND,

    FileNotFound = DOSBOX_ERR_FILE_NOT_FOUND,
    FileAccessDenied = DOSBOX_ERR_FILE_ACCESS_DENIED,
    FileReadError = DOSBOX_ERR_FILE_READ_ERROR,
    FileWriteError = DOSBOX_ERR_FILE_WRITE_ERROR,
    PathTooLong = DOSBOX_ERR_PATH_TOO_LONG,

    ConfigParseError = DOSBOX_ERR_CONFIG_PARSE,
    ConfigValueInvalid = DOSBOX_ERR_CONFIG_VALUE,
    ConfigSectionMissing = DOSBOX_ERR_CONFIG_SECTION,

    CpuError = DOSBOX_ERR_CPU,
    MemoryError = DOSBOX_ERR_MEMORY,
    DmaError = DOSBOX_ERR_DMA,
    InterruptError = DOSBOX_ERR_INTERRUPT,
    DeviceError = DOSBOX_ERR_DEVICE,

    NullHandle = DOSBOX_ERR_NULL_HANDLE,
    InvalidHandle = DOSBOX_ERR_INVALID_HANDLE,
    BufferTooSmall = DOSBOX_ERR_BUFFER_TOO_SMALL,
    Exception = DOSBOX_ERR_EXCEPTION,

    Panic = DOSBOX_ERR_PANIC,
    Trap = DOSBOX_ERR_TRAP,
    Fatal = DOSBOX_ERR_FATAL
};

/**
 * @brief Convert ErrorCode to string.
 */
[[nodiscard]] inline const char* error_code_name(ErrorCode code) noexcept {
    return dosbox_error_code_name(static_cast<dosbox_error_code>(code));
}

// ─────────────────────────────────────────────────────────────────────────────
// Error Class (C++ rich error)
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Rich error type for C++ code.
 *
 * Contains source location and full message. Can be converted
 * to/from the FFI-safe dosbox_error struct.
 */
class Error {
public:
    Error(ErrorCode code,
          std::string message,
          std::source_location loc = std::source_location::current())
        : code_(code)
        , message_(std::move(message))
        , location_(loc)
    {}

    [[nodiscard]] ErrorCode code() const noexcept { return code_; }
    [[nodiscard]] const std::string& message() const noexcept { return message_; }
    [[nodiscard]] const std::source_location& location() const noexcept { return location_; }

    [[nodiscard]] const char* file() const noexcept { return location_.file_name(); }
    [[nodiscard]] uint_least32_t line() const noexcept { return location_.line(); }
    [[nodiscard]] const char* function() const noexcept { return location_.function_name(); }

    [[nodiscard]] std::string format() const {
        return std::format("{} at {}:{} ({}): {}",
            error_code_name(code_),
            location_.file_name(),
            location_.line(),
            location_.function_name(),
            message_);
    }

    /**
     * @brief Convert to FFI-safe error struct.
     */
    [[nodiscard]] dosbox_error to_ffi() const noexcept;

    /**
     * @brief Create from FFI error struct.
     */
    [[nodiscard]] static Error from_ffi(const dosbox_error& err);

private:
    ErrorCode code_;
    std::string message_;
    std::source_location location_;
};

// ─────────────────────────────────────────────────────────────────────────────
// Result Type
// ─────────────────────────────────────────────────────────────────────────────

template<typename T>
using Result = std::expected<T, Error>;

template<typename T>
[[nodiscard]] constexpr Result<T> Ok(T value) {
    return Result<T>{std::in_place, std::move(value)};
}

[[nodiscard]] inline constexpr Result<void> Ok() {
    return Result<void>{};
}

[[nodiscard]] inline std::unexpected<Error> Err(Error error) {
    return std::unexpected(std::move(error));
}

[[nodiscard]] inline std::unexpected<Error> make_error(
    ErrorCode code,
    std::string msg,
    std::source_location loc = std::source_location::current()
) {
    return std::unexpected(Error{code, std::move(msg), loc});
}

template<typename... Args>
[[nodiscard]] std::unexpected<Error> make_error_fmt(
    ErrorCode code,
    std::format_string<Args...> fmt,
    Args&&... args
) {
    return std::unexpected(Error{
        code,
        std::format(fmt, std::forward<Args>(args)...),
        std::source_location::current()
    });
}

// ─────────────────────────────────────────────────────────────────────────────
// Context State (for PANIC behavior)
// ─────────────────────────────────────────────────────────────────────────────

enum class ContextState {
    Created,
    Initialized,
    Running,
    Failed,     // After PANIC - only destroy is valid
    Destroyed
};

// Forward declaration - implemented in context module
class DOSBoxContext;
DOSBoxContext* current_context() noexcept;
void set_context_state(DOSBoxContext* ctx, ContextState state) noexcept;
ContextState get_context_state(DOSBoxContext* ctx) noexcept;

// ─────────────────────────────────────────────────────────────────────────────
// Internal Functions (called by macros)
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Record error for FFI retrieval.
 */
void set_last_error(const Error& error) noexcept;

/**
 * @brief Handle PANIC - set context to Failed state, invoke handler.
 * @return Error to return from calling function
 */
[[nodiscard]] Error panic_internal(
    const char* message,
    std::source_location loc = std::source_location::current()
) noexcept;

/**
 * @brief Handle TRAP - invoke handler, potentially abort.
 * @return Error to return (if handler allows continuation)
 */
[[nodiscard]] Error trap_internal(
    const char* message,
    std::source_location loc = std::source_location::current()
) noexcept;

} // namespace dosbox

// ═══════════════════════════════════════════════════════════════════════════════
// FAIL/PANIC/TRAP Macros
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief FAIL - Recoverable error, returns Result::error.
 *
 * Use for: Invalid input, missing files, parse errors.
 * Does NOT terminate. Caller can handle the error.
 *
 * @param code ErrorCode value
 * @param msg Error message string
 */
#define DOSBOX_FAIL(code, msg) \
    return ::dosbox::make_error(::dosbox::ErrorCode::code, msg)

/**
 * @brief FAIL with formatted message.
 */
#define DOSBOX_FAIL_FMT(code, fmt, ...) \
    return ::dosbox::make_error_fmt(::dosbox::ErrorCode::code, fmt, __VA_ARGS__)

/**
 * @brief CHECK - Return error if condition is false.
 */
#define DOSBOX_CHECK(cond, code, msg) \
    do { \
        if (!(cond)) { \
            return ::dosbox::make_error(::dosbox::ErrorCode::code, msg); \
        } \
    } while (0)

/**
 * @brief PANIC - Internal invariant violation.
 *
 * Use for: Bugs, impossible states, programming errors.
 * Sets context to Failed state. All subsequent API calls
 * return ERR_INVALID_STATE until destroy.
 *
 * Does NOT terminate the host process.
 *
 * @param msg Error message string
 */
#define DOSBOX_PANIC(msg) \
    return ::dosbox::Err(::dosbox::panic_internal(msg))

/**
 * @brief PANIC with formatted message.
 */
#define DOSBOX_PANIC_FMT(fmt, ...) \
    return ::dosbox::Err(::dosbox::panic_internal( \
        std::format(fmt, __VA_ARGS__).c_str()))

/**
 * @brief TRAP - Unrecoverable memory corruption.
 *
 * Use for: Memory corruption, impossible states that indicate
 * the process is compromised. Extremely rare (< 5 call sites).
 *
 * Invokes host-settable handler. Default behavior:
 * - Library mode: Returns fatal error
 * - Standalone mode: Calls abort()
 *
 * @param msg Error message string
 */
#define DOSBOX_TRAP(msg) \
    return ::dosbox::Err(::dosbox::trap_internal(msg))

/**
 * @brief TRY - Propagate errors from Result.
 *
 * Usage:
 *   Result<int> foo() {
 *       int val = DOSBOX_TRY(bar());
 *       return Ok(val + 1);
 *   }
 */
#define DOSBOX_TRY(expr) \
    ({ \
        auto&& _dosbox_result = (expr); \
        if (!_dosbox_result.has_value()) { \
            return ::dosbox::Err(_dosbox_result.error()); \
        } \
        std::move(_dosbox_result).value(); \
    })

// ═══════════════════════════════════════════════════════════════════════════════
// Legacy E_Exit Replacement (for gradual migration)
// ═══════════════════════════════════════════════════════════════════════════════

#ifdef DOSBOX_LIBRARY_MODE

/**
 * @brief Replacement for E_Exit in library mode.
 *
 * Instead of terminating the process, this throws an exception
 * that will be caught at the API boundary by safe_call.
 *
 * Migration: Replace E_Exit("message") with DOSBOX_E_EXIT("message")
 * Then gradually convert to DOSBOX_FAIL or DOSBOX_PANIC as appropriate.
 */
#define DOSBOX_E_EXIT(msg) \
    throw ::dosbox::FatalException(msg, __FILE__, __LINE__)

#else

/* In standalone mode, E_Exit behavior is unchanged */
#define DOSBOX_E_EXIT(msg) E_Exit(msg)

#endif /* DOSBOX_LIBRARY_MODE */

#endif /* __cplusplus */

#endif /* DOSBOX_ERROR_MODEL_H */
