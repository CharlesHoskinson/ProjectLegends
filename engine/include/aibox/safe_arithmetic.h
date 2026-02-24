/**
 * @file safe_arithmetic.h
 * @brief Overflow-safe arithmetic utilities for aibox.
 *
 * Provides safe_multiply() and safe_multiply_3() returning std::expected,
 * and a SAFE_MULTIPLY_OR_ERROR macro for use in FFI functions that
 * return dosboxx_error_t via DOSBOXX_ERROR.
 *
 * @copyright GPL-2.0-or-later
 */

#pragma once

#include <cstddef>
#include <cstdint>
#include <expected>
#include <aibox/error.h>

namespace aibox {

/**
 * @brief Multiply two size_t values with overflow detection.
 * @return The product, or unexpected(ErrorCode::InvalidState) on overflow.
 */
[[nodiscard]] inline std::expected<std::size_t, ErrorCode>
safe_multiply(std::size_t a, std::size_t b) noexcept {
    if (b != 0 && a > SIZE_MAX / b)
        return std::unexpected(ErrorCode::InvalidState);
    return a * b;
}

/**
 * @brief Multiply three size_t values with overflow detection.
 * @return The product, or unexpected(ErrorCode::InvalidState) on overflow.
 */
[[nodiscard]] inline std::expected<std::size_t, ErrorCode>
safe_multiply_3(std::size_t a, std::size_t b, std::size_t c) noexcept {
    auto ab = safe_multiply(a, b);
    if (!ab) return ab;
    return safe_multiply(*ab, c);
}

} // namespace aibox

/**
 * @brief Compute a * b into result_var, returning DOSBOXX_ERR_INVALID_STATE
 *        on overflow via the file-local DOSBOXX_ERROR macro.
 *
 * Requires DOSBOXX_ERROR(code, msg) to be in scope
 * (as in legends_embed_api.cpp FFI functions).
 */
#define SAFE_MULTIPLY_OR_ERROR(a, b, result_var) \
    do { \
        if ((b) != 0 && (a) > SIZE_MAX / (b)) { \
            DOSBOXX_ERROR(DOSBOXX_ERR_INVALID_STATE, \
                "Integer overflow: " #a " * " #b); \
        } \
        (result_var) = static_cast<std::size_t>(a) * (b); \
    } while (0)
