/**
 * @file safe_call.h
 * @brief API boundary containment for DOSBox-X library mode.
 *
 * This implements the safe_call wrapper that contains exceptions and abort
 * paths at the public API boundary, as defined in LIBRARY_CONTRACT.md:
 *
 * - No exception escapes to host application
 * - No abort/exit terminates host process
 * - All errors converted to error codes for FFI
 *
 * Usage:
 *   // In public API implementation
 *   extern "C" int dosbox_do_thing(dosbox_handle h, int arg) {
 *       return dosbox::safe_call([&]() -> dosbox::Result<int> {
 *           // Implementation that may throw or use DOSBOX_FAIL/PANIC
 *           return dosbox::Ok(do_the_thing(h, arg));
 *       });
 *   }
 *
 * @copyright GPL-2.0-or-later
 */

#ifndef DOSBOX_SAFE_CALL_H
#define DOSBOX_SAFE_CALL_H

#include "dosbox/error_model.h"
#include "dosbox/logging.h"

#include <exception>
#include <type_traits>
#include <functional>

namespace dosbox {

// ═══════════════════════════════════════════════════════════════════════════════
// Exception Types (for legacy code migration)
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * @brief Exception thrown by DOSBOX_E_EXIT macro during migration.
 *
 * This allows legacy E_Exit() calls to be caught at the API boundary
 * instead of terminating the host process.
 */
class FatalException : public std::exception {
public:
    FatalException(const char* message, const char* file, int line)
        : message_(message ? message : "Unknown fatal error")
        , file_(file ? file : "unknown")
        , line_(line)
    {}

    [[nodiscard]] const char* what() const noexcept override {
        return message_.c_str();
    }

    [[nodiscard]] const std::string& message() const noexcept { return message_; }
    [[nodiscard]] const std::string& file() const noexcept { return file_; }
    [[nodiscard]] int line() const noexcept { return line_; }

private:
    std::string message_;
    std::string file_;
    int line_;
};

// ═══════════════════════════════════════════════════════════════════════════════
// Safe Call Implementation
// ═══════════════════════════════════════════════════════════════════════════════

namespace detail {

/**
 * @brief Convert exception to error and set last error.
 */
inline Error exception_to_error(const std::exception& e,
                                 std::source_location loc = std::source_location::current()) {
    Error err{ErrorCode::Exception, e.what(), loc};
    set_last_error(err);
    return err;
}

/**
 * @brief Convert FatalException to error.
 */
inline Error fatal_to_error(const FatalException& e) {
    // Create source location from exception's stored location
    Error err{ErrorCode::Fatal, e.message()};
    set_last_error(err);
    return err;
}

/**
 * @brief Handle unknown exception.
 */
inline Error unknown_exception_error(
    std::source_location loc = std::source_location::current()) {
    Error err{ErrorCode::Exception, "Unknown exception caught at API boundary", loc};
    set_last_error(err);
    return err;
}

} // namespace detail

// ─────────────────────────────────────────────────────────────────────────────
// safe_call for Result<T> returning functions
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Execute a function and catch all exceptions at the API boundary.
 *
 * For functions returning Result<T>, extracts the value or returns error code.
 *
 * @tparam F    Callable type returning Result<T>
 * @param func  Function to execute
 * @return      Value on success, or error code on failure
 */
template<typename F>
    requires std::invocable<F> &&
             requires { typename std::invoke_result_t<F>::value_type; }
auto safe_call(F&& func) noexcept ->
    typename std::invoke_result_t<F>::value_type {

    using ResultType = std::invoke_result_t<F>;
    using ValueType = typename ResultType::value_type;

    try {
        ResultType result = std::forward<F>(func)();
        if (result.has_value()) {
            if constexpr (std::is_void_v<ValueType>) {
                return;
            } else {
                return std::move(result).value();
            }
        } else {
            set_last_error(result.error());
            if constexpr (std::is_void_v<ValueType>) {
                return;
            } else if constexpr (std::is_default_constructible_v<ValueType>) {
                return ValueType{};
            } else {
                // Can't return default, this is a compile error
                static_assert(std::is_default_constructible_v<ValueType>,
                    "safe_call requires default-constructible return type for error case");
            }
        }
    } catch (const FatalException& e) {
        detail::fatal_to_error(e);
        LOG_ERROR("API", "Fatal exception at boundary: %s", e.what());
    } catch (const Error& e) {
        set_last_error(e);
        LOG_ERROR("API", "Error at boundary: %s", e.message().c_str());
    } catch (const std::exception& e) {
        detail::exception_to_error(e);
        LOG_ERROR("API", "Exception at boundary: %s", e.what());
    } catch (...) {
        detail::unknown_exception_error();
        LOG_ERROR("API", "Unknown exception at boundary");
    }

    if constexpr (std::is_void_v<ValueType>) {
        return;
    } else {
        return ValueType{};
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// safe_call for Result<void>
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Execute a function returning Result<void> and return error code.
 *
 * @tparam F    Callable type returning Result<void>
 * @param func  Function to execute
 * @return      DOSBOX_OK on success, error code on failure
 */
template<typename F>
    requires std::invocable<F> &&
             std::same_as<std::invoke_result_t<F>, Result<void>>
dosbox_error_code safe_call_void(F&& func) noexcept {
    try {
        Result<void> result = std::forward<F>(func)();
        if (result.has_value()) {
            return DOSBOX_OK;
        } else {
            set_last_error(result.error());
            return static_cast<dosbox_error_code>(result.error().code());
        }
    } catch (const FatalException& e) {
        detail::fatal_to_error(e);
        LOG_ERROR("API", "Fatal exception at boundary: %s", e.what());
        return DOSBOX_ERR_FATAL;
    } catch (const Error& e) {
        set_last_error(e);
        LOG_ERROR("API", "Error at boundary: %s", e.message().c_str());
        return static_cast<dosbox_error_code>(e.code());
    } catch (const std::exception& e) {
        detail::exception_to_error(e);
        LOG_ERROR("API", "Exception at boundary: %s", e.what());
        return DOSBOX_ERR_EXCEPTION;
    } catch (...) {
        detail::unknown_exception_error();
        LOG_ERROR("API", "Unknown exception at boundary");
        return DOSBOX_ERR_EXCEPTION;
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// safe_call_code for functions returning error codes directly
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Execute a function and return error code, catching exceptions.
 *
 * For functions that return dosbox_error_code directly.
 *
 * @tparam F    Callable type returning dosbox_error_code
 * @param func  Function to execute
 * @return      Error code from function or DOSBOX_ERR_EXCEPTION
 */
template<typename F>
    requires std::invocable<F> &&
             std::same_as<std::invoke_result_t<F>, dosbox_error_code>
dosbox_error_code safe_call_code(F&& func) noexcept {
    try {
        return std::forward<F>(func)();
    } catch (const FatalException& e) {
        detail::fatal_to_error(e);
        LOG_ERROR("API", "Fatal exception at boundary: %s", e.what());
        return DOSBOX_ERR_FATAL;
    } catch (const Error& e) {
        set_last_error(e);
        LOG_ERROR("API", "Error at boundary: %s", e.message().c_str());
        return static_cast<dosbox_error_code>(e.code());
    } catch (const std::exception& e) {
        detail::exception_to_error(e);
        LOG_ERROR("API", "Exception at boundary: %s", e.what());
        return DOSBOX_ERR_EXCEPTION;
    } catch (...) {
        detail::unknown_exception_error();
        LOG_ERROR("API", "Unknown exception at boundary");
        return DOSBOX_ERR_EXCEPTION;
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Convenience Macros for API Implementation
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Wrap API function body with exception containment.
 *
 * Usage:
 *   extern "C" int dosbox_foo(dosbox_handle h) {
 *       DOSBOX_API_BOUNDARY {
 *           // code that may throw
 *           return DOSBOX_OK;
 *       }
 *   }
 */
#define DOSBOX_API_BOUNDARY \
    return ::dosbox::safe_call_code([&]() -> dosbox_error_code

#define DOSBOX_API_BOUNDARY_END )

/**
 * @brief Wrap API function returning Result<void>.
 */
#define DOSBOX_API_VOID \
    return ::dosbox::safe_call_void([&]() -> ::dosbox::Result<void>

#define DOSBOX_API_VOID_END )

} // namespace dosbox

#endif /* DOSBOX_SAFE_CALL_H */
