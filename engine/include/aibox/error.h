/**
 * @file error.h
 * @brief Error handling infrastructure using C++23 std::expected.
 *
 * Provides:
 * - Error struct with code, message, and source location
 * - Result<T> type alias for std::expected<T, Error>
 * - Ok(), Err(), make_error() helper functions
 * - Monadic operations via std::expected (and_then, transform, or_else)
 *
 * Requirements implemented:
 * - REQ-FND-002: Result<T> for expected failures
 * - REQ-FND-004: Source location in errors
 * - REQ-P3-001: Result as std::expected alias
 *
 * @copyright GPL-2.0-or-later
 */

#pragma once

#include <expected>
#include <format>
#include <source_location>
#include <string>
#include <utility>
#include <cstdint>

namespace aibox {

// ─────────────────────────────────────────────────────────────────────────────
// Error Codes
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Categorized error codes for Result<T> failures.
 *
 * Positive codes indicate specific error categories.
 * Zero indicates success (not used in Error objects).
 */
enum class ErrorCode : int {
    // Success (not stored in Error)
    Ok = 0,

    // General errors (1-99)
    Unknown = 1,
    NotImplemented = 2,
    InvalidArgument = 3,
    InvalidState = 4,
    NotInitialized = 5,
    AlreadyInitialized = 6,

    // Resource errors (100-199)
    OutOfMemory = 100,
    ResourceExhausted = 101,
    ResourceBusy = 102,
    ResourceNotFound = 103,

    // I/O errors (200-299)
    FileNotFound = 200,
    FileAccessDenied = 201,
    FileReadError = 202,
    FileWriteError = 203,
    PathTooLong = 204,

    // Configuration errors (300-399)
    ConfigParseError = 300,
    ConfigValueInvalid = 301,
    ConfigSectionMissing = 302,

    // Emulation errors (400-499)
    CpuError = 400,
    MemoryError = 401,
    DmaError = 402,
    InterruptError = 403,
    DeviceError = 404,

    // FFI errors (500-599)
    NullPointer = 500,
    InvalidHandle = 501,
    BufferTooSmall = 502,
};

/**
 * @brief Convert ErrorCode to string representation.
 */
[[nodiscard]] inline constexpr const char* error_code_name(ErrorCode code) noexcept {
    switch (code) {
        case ErrorCode::Ok: return "Ok";
        case ErrorCode::Unknown: return "Unknown";
        case ErrorCode::NotImplemented: return "NotImplemented";
        case ErrorCode::InvalidArgument: return "InvalidArgument";
        case ErrorCode::InvalidState: return "InvalidState";
        case ErrorCode::NotInitialized: return "NotInitialized";
        case ErrorCode::AlreadyInitialized: return "AlreadyInitialized";
        case ErrorCode::OutOfMemory: return "OutOfMemory";
        case ErrorCode::ResourceExhausted: return "ResourceExhausted";
        case ErrorCode::ResourceBusy: return "ResourceBusy";
        case ErrorCode::ResourceNotFound: return "ResourceNotFound";
        case ErrorCode::FileNotFound: return "FileNotFound";
        case ErrorCode::FileAccessDenied: return "FileAccessDenied";
        case ErrorCode::FileReadError: return "FileReadError";
        case ErrorCode::FileWriteError: return "FileWriteError";
        case ErrorCode::PathTooLong: return "PathTooLong";
        case ErrorCode::ConfigParseError: return "ConfigParseError";
        case ErrorCode::ConfigValueInvalid: return "ConfigValueInvalid";
        case ErrorCode::ConfigSectionMissing: return "ConfigSectionMissing";
        case ErrorCode::CpuError: return "CpuError";
        case ErrorCode::MemoryError: return "MemoryError";
        case ErrorCode::DmaError: return "DmaError";
        case ErrorCode::InterruptError: return "InterruptError";
        case ErrorCode::DeviceError: return "DeviceError";
        case ErrorCode::NullPointer: return "NullPointer";
        case ErrorCode::InvalidHandle: return "InvalidHandle";
        case ErrorCode::BufferTooSmall: return "BufferTooSmall";
        default: return "Unknown";
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Error Class
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Structured error with code, message, and source location.
 *
 * Used as the error type in Result<T> (std::expected<T, Error>).
 * Captures where the error occurred for debugging purposes.
 *
 * Example:
 * @code
 *   Error err(ErrorCode::FileNotFound, "Config file missing");
 *   std::cerr << err.format() << std::endl;
 *   // Output: FileNotFound at config.cpp:42 (load_config): Config file missing
 * @endcode
 */
class Error {
public:
    /**
     * @brief Construct an error with code and message.
     * @param code Error category
     * @param message Human-readable description
     * @param location Source location (auto-captured by default)
     */
    Error(ErrorCode code,
          std::string message,
          std::source_location location = std::source_location::current())
        : code_(code)
        , message_(std::move(message))
        , location_(location)
    {}

    /**
     * @brief Create error from code and message.
     */
    [[nodiscard]] static Error from_code(
        ErrorCode code,
        std::string msg,
        std::source_location loc = std::source_location::current()
    ) {
        return Error{code, std::move(msg), loc};
    }

    /**
     * @brief Create error with formatted message.
     *
     * @tparam Args Format argument types
     * @param code Error code
     * @param fmt Format string
     * @param args Format arguments
     */
    template<typename... Args>
    [[nodiscard]] static Error formatted(
        ErrorCode code,
        std::format_string<Args...> fmt,
        Args&&... args
    ) {
        return Error{
            code,
            std::format(fmt, std::forward<Args>(args)...),
            std::source_location::current()
        };
    }

    // Accessors
    [[nodiscard]] ErrorCode code() const noexcept { return code_; }
    [[nodiscard]] const std::string& message() const noexcept { return message_; }
    [[nodiscard]] const std::source_location& location() const noexcept { return location_; }

    /**
     * @brief Get file name from location.
     */
    [[nodiscard]] const char* file() const noexcept {
        return location_.file_name();
    }

    /**
     * @brief Get line number from location.
     */
    [[nodiscard]] uint_least32_t line() const noexcept {
        return location_.line();
    }

    /**
     * @brief Get function name from location.
     */
    [[nodiscard]] const char* function() const noexcept {
        return location_.function_name();
    }

    /**
     * @brief Format error for display/logging.
     * @return Formatted string: "CODE at file:line (func): message"
     */
    [[nodiscard]] std::string format() const {
        return std::format(
            "{} at {}:{} ({}): {}",
            error_code_name(code_),
            location_.file_name(),
            location_.line(),
            location_.function_name(),
            message_
        );
    }

    /**
     * @brief Check if this is a specific error code.
     */
    [[nodiscard]] bool is(ErrorCode code) const noexcept {
        return code_ == code;
    }

private:
    ErrorCode code_;
    std::string message_;
    std::source_location location_;
};

// ─────────────────────────────────────────────────────────────────────────────
// Result Type (std::expected alias)
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Result type for fallible operations.
 *
 * Represents either a success value of type T, or an Error.
 * This is a type alias for std::expected<T, Error>.
 *
 * @tparam T The success value type
 *
 * Available methods from std::expected:
 * - has_value() / operator bool() - check for success
 * - value() - get success value (throws if error)
 * - error() - get error (undefined if success)
 * - value_or(default) - get value or default
 * - and_then(f) - chain operations on success
 * - transform(f) - map success value
 * - or_else(f) - handle/recover from error
 *
 * Example:
 * @code
 *   Result<int> parse(const char* s) {
 *       if (!s) return Err(Error(ErrorCode::NullPointer, "null input"));
 *       return Ok(std::atoi(s));
 *   }
 *
 *   auto r = parse("42");
 *   if (r) {
 *       std::cout << r.value();
 *   } else {
 *       std::cerr << r.error().message();
 *   }
 * @endcode
 */
template<typename T>
using Result = std::expected<T, Error>;

// ─────────────────────────────────────────────────────────────────────────────
// Helper Functions
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Create a successful Result.
 *
 * @tparam T Value type
 * @param value The success value
 * @return Result containing the value
 */
template<typename T>
[[nodiscard]] constexpr Result<T> Ok(T value) {
    return Result<T>{std::in_place, std::move(value)};
}

/**
 * @brief Create a void successful Result.
 *
 * @return Result<void> indicating success
 */
[[nodiscard]] inline constexpr Result<void> Ok() {
    return Result<void>{};
}

/**
 * @brief Create a failed Result.
 *
 * @param error The error
 * @return std::unexpected convertible to any Result<T>
 */
[[nodiscard]] inline std::unexpected<Error> Err(Error error) {
    return std::unexpected(std::move(error));
}

/**
 * @brief Create error with code and message.
 *
 * @param code Error code
 * @param msg Error message
 * @param loc Source location (auto-captured)
 * @return std::unexpected<Error>
 */
[[nodiscard]] inline std::unexpected<Error> make_error(
    ErrorCode code,
    std::string msg,
    std::source_location loc = std::source_location::current()
) {
    return std::unexpected(Error{code, std::move(msg), loc});
}

/**
 * @brief Create formatted error.
 *
 * @tparam Args Format argument types
 * @param code Error code
 * @param fmt Format string
 * @param args Format arguments
 * @return std::unexpected<Error>
 */
template<typename... Args>
[[nodiscard]] std::unexpected<Error> make_error_fmt(
    ErrorCode code,
    std::format_string<Args...> fmt,
    Args&&... args
) {
    return std::unexpected(Error::formatted(code, fmt, std::forward<Args>(args)...));
}

// ─────────────────────────────────────────────────────────────────────────────
// Convenience Macros
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Return error if condition is false.
 *
 * Usage:
 *   AIBOX_CHECK(ptr != nullptr, ErrorCode::NullPointer, "pointer is null");
 */
#define AIBOX_CHECK(cond, code, msg) \
    do { \
        if (!(cond)) { \
            return ::aibox::make_error(code, msg); \
        } \
    } while (0)

/**
 * @brief Return early if result is an error.
 *
 * Usage:
 * @code
 *   Result<int> foo() {
 *       auto val = AIBOX_TRY(bar());  // Returns if bar() fails
 *       return Ok(val + 1);
 *   }
 * @endcode
 *
 * Note: Uses GCC statement expression extension. For portable code,
 * use explicit if-checks instead.
 */
#define AIBOX_TRY(expr) \
    ({ \
        auto&& _aibox_result = (expr); \
        if (!_aibox_result.has_value()) { \
            return ::aibox::Err(_aibox_result.error()); \
        } \
        std::move(_aibox_result).value(); \
    })

/**
 * @brief Return early with error if condition is false.
 */
#define AIBOX_ENSURE(cond, code, msg) \
    do { \
        if (!(cond)) { \
            return ::aibox::make_error(code, msg); \
        } \
    } while (0)

/**
 * @brief Create an error with current location.
 */
#define AIBOX_ERROR(code, msg) \
    ::aibox::Error(code, msg, std::source_location::current())

// ─────────────────────────────────────────────────────────────────────────────
// Legacy Compatibility (for gradual migration)
// ─────────────────────────────────────────────────────────────────────────────

// Type alias for source location (legacy code compatibility)
using SourceLocation = std::source_location;

// Macro for getting current location (legacy code compatibility)
#define AIBOX_CURRENT_LOCATION std::source_location::current()

} // namespace aibox
