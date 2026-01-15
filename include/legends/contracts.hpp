/**
 * @file contracts.hpp
 * @brief Unified contract checking infrastructure.
 *
 * This header provides contract macros aligned with the FAIL/PANIC/TRAP
 * error taxonomy defined in the library contract:
 *
 * ┌─────────────────────────────────────────────────────────────────────────┐
 * │ Level       │ Macro              │ Action on Violation                 │
 * ├─────────────┼────────────────────┼─────────────────────────────────────┤
 * │ FAIL        │ LEGENDS_REQUIRE    │ Returns Result<T> error             │
 * │ PANIC       │ LEGENDS_ASSERT     │ Throws FatalException (lib mode)    │
 * │ TRAP        │ LEGENDS_ABORT      │ Calls trap handler / abort          │
 * └─────────────────────────────────────────────────────────────────────────┘
 *
 * Usage Guidelines:
 *
 * 1. LEGENDS_REQUIRE - For recoverable precondition failures (FAIL level)
 *    Use when: Caller provided invalid input that can be reported as error
 *    @code
 *    Result<void> load_file(const char* path) {
 *        LEGENDS_REQUIRE(path != nullptr, ErrorCode::NullPointer, "path is null");
 *        LEGENDS_REQUIRE(strlen(path) > 0, ErrorCode::InvalidArgument, "path is empty");
 *        // ...
 *    }
 *    @endcode
 *
 * 2. LEGENDS_ASSERT - For internal invariant violations (PANIC level)
 *    Use when: Bug detected, state is inconsistent, should NEVER happen
 *    @code
 *    void process_queue() {
 *        LEGENDS_ASSERT(!queue_.empty(), "process_queue called on empty queue");
 *        LEGENDS_ASSERT(state_ == State::Running, "invalid state for processing");
 *        // ...
 *    }
 *    @endcode
 *
 * 3. LEGENDS_ABORT - For unrecoverable corruption (TRAP level)
 *    Use when: Memory corruption, impossible states, safety-critical failures
 *    Rarely used - prefer LEGENDS_ASSERT for most invariants.
 *
 * Integration with gsl-lite:
 *
 * gsl-lite provides Expects() and Ensures() for narrow contracts. These
 * call the contract violation handler on failure (configurable via
 * gsl_CONFIG_CONTRACT_VIOLATION_THROWS / TERMINATES / CALLS_HANDLER).
 *
 * In library mode, we configure gsl-lite to throw on contract violation,
 * making it equivalent to LEGENDS_ASSERT behavior.
 *
 * @code
 *   #include <legends/gsl.hpp>
 *
 *   void foo(legends::gsl::span<int> data) {
 *       legends::gsl::Expects(data.size() > 0);  // Narrow contract (throws)
 *       // ...
 *       legends::gsl::Ensures(result >= 0);      // Postcondition
 *   }
 * @endcode
 *
 * Requirements implemented:
 * - REQ-FND-002: Result<T> for expected failures (via LEGENDS_REQUIRE)
 * - REQ-FND-003: Exceptions for programming errors (via LEGENDS_ASSERT)
 * - REQ-P0-002: FAIL/PANIC/TRAP taxonomy alignment
 *
 * @copyright GPL-2.0-or-later
 */

#pragma once

#include <legends/error.h>
#include <legends/exceptions.h>

namespace legends {

// ─────────────────────────────────────────────────────────────────────────────
// FAIL Level: Recoverable Precondition Checks
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Check precondition and return error if violated (FAIL level).
 *
 * Use for input validation where the caller can handle the error.
 * Returns an error Result<T> on violation - does NOT terminate.
 *
 * @param cond Condition that must be true
 * @param code ErrorCode to return on violation
 * @param msg Error message describing the violation
 *
 * @code
 *   Result<int> divide(int a, int b) {
 *       LEGENDS_REQUIRE(b != 0, ErrorCode::InvalidArgument, "division by zero");
 *       return Ok(a / b);
 *   }
 * @endcode
 */
#define LEGENDS_REQUIRE(cond, code, msg) \
    LEGENDS_CHECK(cond, code, msg)

/**
 * @brief Check precondition with formatted message (FAIL level).
 *
 * @param cond Condition that must be true
 * @param code ErrorCode to return on violation
 * @param fmt Format string
 * @param ... Format arguments
 *
 * @code
 *   Result<void> set_port(uint16_t port) {
 *       LEGENDS_REQUIRE_FMT(port <= 0xFFFF, ErrorCode::InvalidArgument,
 *                           "port {} exceeds maximum", port);
 *       return Ok();
 *   }
 * @endcode
 */
#define LEGENDS_REQUIRE_FMT(cond, code, fmt, ...) \
    do { \
        if (!(cond)) { \
            return ::legends::make_error_fmt(code, fmt, __VA_ARGS__); \
        } \
    } while (0)

// ─────────────────────────────────────────────────────────────────────────────
// FAIL Level: Postcondition Checks
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Check postcondition and return error if violated (FAIL level).
 *
 * Use to validate function outputs before returning.
 *
 * @param cond Condition that must be true
 * @param code ErrorCode to return on violation
 * @param msg Error message describing the violation
 *
 * @code
 *   Result<int> compute() {
 *       int result = do_computation();
 *       LEGENDS_POSTCOND(result >= 0, ErrorCode::InvalidState, "negative result");
 *       return Ok(result);
 *   }
 * @endcode
 */
#define LEGENDS_POSTCOND(cond, code, msg) \
    LEGENDS_CHECK(cond, code, msg)

// ─────────────────────────────────────────────────────────────────────────────
// PANIC Level: Invariant Assertions
// ─────────────────────────────────────────────────────────────────────────────

// LEGENDS_ASSERT is defined in <legends/exceptions.h>
// In library mode: throws FatalException
// In standalone mode: calls assert()

/**
 * @brief Assert with formatted message (PANIC level).
 *
 * @param cond Condition that must be true
 * @param fmt Format string
 * @param ... Format arguments
 *
 * @code
 *   void update_state(State new_state) {
 *       LEGENDS_ASSERT_FMT(is_valid_transition(state_, new_state),
 *                          "invalid transition: {} -> {}", state_, new_state);
 *       state_ = new_state;
 *   }
 * @endcode
 */
#ifdef LEGENDS_LIBRARY_MODE
    #define LEGENDS_ASSERT_FMT(cond, fmt, ...) \
        do { \
            if (!(cond)) { \
                throw ::legends::FatalException( \
                    std::format("Assertion failed: " fmt, __VA_ARGS__), \
                    __FILE__, __LINE__); \
            } \
        } while (0)
#else
    #define LEGENDS_ASSERT_FMT(cond, fmt, ...) \
        do { \
            if (!(cond)) { \
                std::cerr << "Assertion failed at " << __FILE__ << ":" << __LINE__ \
                          << ": " << std::format(fmt, __VA_ARGS__) << "\n"; \
                std::abort(); \
            } \
        } while (0)
#endif

// ─────────────────────────────────────────────────────────────────────────────
// TRAP Level: Unrecoverable Failures
// ─────────────────────────────────────────────────────────────────────────────

// LEGENDS_ABORT is defined in <legends/exceptions.h>
// Use sparingly - for truly unrecoverable corruption only.

// ─────────────────────────────────────────────────────────────────────────────
// gsl-lite Contract Configuration
// ─────────────────────────────────────────────────────────────────────────────

// Configure gsl-lite to throw on contract violation in library mode.
// This makes gsl::Expects/Ensures behave like LEGENDS_ASSERT.
//
// NOTE: These must be defined BEFORE including <gsl-lite/gsl-lite.hpp>.
// The CMakeLists.txt should define these via target_compile_definitions
// for the legends_core target.
//
// Recommended configuration (set in CMake, not here):
//   LEGENDS_LIBRARY_MODE=1  =>  gsl_CONFIG_CONTRACT_VIOLATION_THROWS=1
//   LEGENDS_LIBRARY_MODE=0  =>  gsl_CONFIG_CONTRACT_VIOLATION_TERMINATES=1

} // namespace legends
