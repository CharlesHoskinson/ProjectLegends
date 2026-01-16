/**
 * @file state_hash_compat.cpp
 * @brief Compatibility shims for state hashing API
 *
 * This file provides legacy API wrappers that use current_context() internally.
 * These exist to support code that hasn't been migrated to explicit context passing.
 *
 * Per Sprint 2 policy, current_context() is allowed in *_compat.cpp files.
 *
 * @copyright GPL-2.0-or-later
 */

#include "dosbox/state_hash.h"
#include "dosbox/dosbox_context.h"

#include <cstring>

namespace dosbox {

// ─────────────────────────────────────────────────────────────────────────────
// Transitional API: Uses thread-local current_context() (deprecated)
// Retained for test compatibility during migration
// Implementation moved from state_hash.cpp to isolate current_context() usage
// ─────────────────────────────────────────────────────────────────────────────

Result<StateHash> get_state_hash(HashMode mode) {
    // Use current context if available
    if (has_current_context()) {
        return get_state_hash(&current_context(), mode);
    }

    // No context - return placeholder hash for backward compatibility
    HashBuilder builder;

    const uint32_t hash_version = 7;  // V7: Added Memory state (Sprint 2 Phase 2)
    builder.update(hash_version);

    const uint32_t mode_marker = static_cast<uint32_t>(mode);
    builder.update(mode_marker);

    // No context available - use placeholder
    const char* no_ctx = "NO_CONTEXT";
    builder.update(no_ctx, std::strlen(no_ctx));

    const char* placeholder = "STATE_HASH_V6";
    builder.update(placeholder, std::strlen(placeholder));

    if (mode == HashMode::Full) {
        const char* full_marker = "FULL_MODE";
        builder.update(full_marker, std::strlen(full_marker));
    }

    return Ok(builder.finalize());
}

} // namespace dosbox
