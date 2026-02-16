/**
 * @file safe_arithmetic.h
 * @brief Overflow-safe arithmetic utilities.
 *
 * Provides safe_multiply() returning std::expected and a
 * SAFE_MULTIPLY_OR_ERROR macro for use in FFI functions that
 * return legends_error_t via LEGENDS_ERROR.
 *
 * @copyright GPL-2.0-or-later
 */

#pragma once

#include <cstddef>
#include <cstdint>
#include <expected>
#include <legends/error.h>

namespace legends {

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

} // namespace legends

/**
 * @brief Compute a * b into result_var, returning LEGENDS_ERR_INVALID_STATE
 *        on overflow via the file-local LEGENDS_ERROR macro.
 *
 * Requires LEGENDS_ERROR(code, msg) and `inst` to be in scope
 * (as in legends_embed_api.cpp FFI functions).
 */
#define SAFE_MULTIPLY_OR_ERROR(a, b, result_var) \
    do { \
        if ((b) != 0 && (a) > SIZE_MAX / (b)) { \
            LEGENDS_ERROR(LEGENDS_ERR_INVALID_STATE, \
                "Integer overflow: " #a " * " #b); \
        } \
        (result_var) = static_cast<std::size_t>(a) * (b); \
    } while (0)
