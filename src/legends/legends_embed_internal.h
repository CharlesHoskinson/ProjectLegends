/**
 * @file legends_embed_internal.h
 * @brief Internal types exposed for testing only - NOT part of public API
 *
 * This header exposes internal implementation details from legends_embed_api.cpp
 * for unit testing purposes. It should NEVER be included in production code
 * outside of the legends layer or test code.
 *
 * @warning DO NOT use these types in application code. They may change
 *          without notice between versions.
 */

#ifndef LEGENDS_EMBED_INTERNAL_H
#define LEGENDS_EMBED_INTERNAL_H

// All types are now defined in instance_state.h (Sprint 2 extraction)
#include "internal/instance_state.h"

namespace legends::internal {

// ============================================================================
// Capacity Constants (convenience aliases)
// ============================================================================

constexpr size_t EFFECTIVE_INPUT_CAPACITY = InputState::EFFECTIVE_CAPACITY;  // 319

} // namespace legends::internal

#endif // LEGENDS_EMBED_INTERNAL_H
