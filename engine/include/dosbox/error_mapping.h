/**
 * @file error_mapping.h
 * @brief Error code mapping between ProjectLegends and DOSBox-X (PR #22)
 *
 * Provides utilities to translate error codes between the legends_embed.h
 * and dosbox_library.h APIs.
 *
 * @copyright GPL-2.0-or-later
 */

#ifndef DOSBOX_ERROR_MAPPING_H
#define DOSBOX_ERROR_MAPPING_H

#include "dosbox/dosbox_library.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Map DOSBox-X library error to legends_error_t.
 *
 * Error codes are designed to be compatible, but this function
 * provides explicit mapping for safety.
 *
 * @param dosbox_err DOSBox-X library error code
 * @return Equivalent legends_error_t value
 */
static inline int32_t dosbox_to_legends_error(dosbox_lib_error_t dosbox_err) {
    /* Error codes are already compatible by design */
    /* DOSBOX_LIB_OK (0) -> LEGENDS_OK (0) */
    /* DOSBOX_LIB_ERR_NULL_HANDLE (-1) -> LEGENDS_ERR_NULL_HANDLE (-1) */
    /* etc. */
    return (int32_t)dosbox_err;
}

/**
 * @brief Map legends_error_t to DOSBox-X library error.
 *
 * @param legends_err ProjectLegends error code
 * @return Equivalent dosbox_lib_error_t value
 */
static inline dosbox_lib_error_t legends_to_dosbox_error(int32_t legends_err) {
    return (dosbox_lib_error_t)legends_err;
}

/**
 * @brief Get human-readable name for DOSBox-X library error.
 *
 * @param err Error code
 * @return Error name string (static, never NULL)
 */
static inline const char* dosbox_lib_error_name(dosbox_lib_error_t err) {
    switch (err) {
        case DOSBOX_LIB_OK:                   return "DOSBOX_LIB_OK";
        case DOSBOX_LIB_ERR_NULL_HANDLE:      return "DOSBOX_LIB_ERR_NULL_HANDLE";
        case DOSBOX_LIB_ERR_NULL_POINTER:     return "DOSBOX_LIB_ERR_NULL_POINTER";
        case DOSBOX_LIB_ERR_ALREADY_CREATED:  return "DOSBOX_LIB_ERR_ALREADY_CREATED";
        case DOSBOX_LIB_ERR_NOT_INITIALIZED:  return "DOSBOX_LIB_ERR_NOT_INITIALIZED";
        case DOSBOX_LIB_ERR_REENTRANT_CALL:   return "DOSBOX_LIB_ERR_REENTRANT_CALL";
        case DOSBOX_LIB_ERR_BUFFER_TOO_SMALL: return "DOSBOX_LIB_ERR_BUFFER_TOO_SMALL";
        case DOSBOX_LIB_ERR_INVALID_CONFIG:   return "DOSBOX_LIB_ERR_INVALID_CONFIG";
        case DOSBOX_LIB_ERR_INVALID_STATE:    return "DOSBOX_LIB_ERR_INVALID_STATE";
        case DOSBOX_LIB_ERR_VERSION_MISMATCH: return "DOSBOX_LIB_ERR_VERSION_MISMATCH";
        case DOSBOX_LIB_ERR_IO_FAILED:        return "DOSBOX_LIB_ERR_IO_FAILED";
        case DOSBOX_LIB_ERR_OUT_OF_MEMORY:    return "DOSBOX_LIB_ERR_OUT_OF_MEMORY";
        case DOSBOX_LIB_ERR_NOT_SUPPORTED:    return "DOSBOX_LIB_ERR_NOT_SUPPORTED";
        case DOSBOX_LIB_ERR_INTERNAL:         return "DOSBOX_LIB_ERR_INTERNAL";
        case DOSBOX_LIB_ERR_WRONG_THREAD:     return "DOSBOX_LIB_ERR_WRONG_THREAD";
        default:                              return "DOSBOX_LIB_ERR_UNKNOWN";
    }
}

#ifdef __cplusplus
} /* extern "C" */

namespace dosbox {

/**
 * @brief C++ wrapper for error mapping.
 */
struct ErrorMapping {
    /**
     * @brief Convert DOSBox-X error to legends error.
     */
    static int32_t to_legends(dosbox_lib_error_t err) noexcept {
        return dosbox_to_legends_error(err);
    }

    /**
     * @brief Convert legends error to DOSBox-X error.
     */
    static dosbox_lib_error_t from_legends(int32_t err) noexcept {
        return legends_to_dosbox_error(err);
    }

    /**
     * @brief Get error name string.
     */
    static const char* name(dosbox_lib_error_t err) noexcept {
        return dosbox_lib_error_name(err);
    }
};

} // namespace dosbox

#endif /* __cplusplus */

#endif /* DOSBOX_ERROR_MAPPING_H */
