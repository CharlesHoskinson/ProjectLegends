/*
 * memory_compat.cpp - Compatibility shims for Memory APIs
 *
 * This file provides legacy API wrappers that use current_context() internally.
 * These exist to support code that hasn't been migrated to explicit context passing.
 *
 * Per Sprint 2 policy, current_context() is allowed in *_compat.cpp files.
 *
 * Copyright (C) 2002-2021  The DOSBox Team
 * SPDX-License-Identifier: GPL-2.0-or-later
 */

#include "dosbox/dosbox_context.h"

using namespace dosbox;

// ═══════════════════════════════════════════════════════════════════════════════
// MemBase / MemSize Compatibility Shims
// ═══════════════════════════════════════════════════════════════════════════════
// Provides access to memory base/size via current_context().
// New code should use DOSBoxContext.memory.base/size directly.
// These were previously inline in mem.h but moved here to eliminate
// current_context() calls from header files (PR #9 cleanup).

#ifdef DOSBOX_LIBRARY_MODE

static uint8_t* fallback_base = nullptr;
static size_t fallback_size = 0;

uint8_t*& MEM_GetBaseRef() {
    if (has_current_context()) {
        return current_context().memory.base;
    }
    return fallback_base;
}

size_t& MEM_GetSizeRef() {
    if (has_current_context()) {
        return current_context().memory.size;
    }
    return fallback_size;
}

#endif // DOSBOX_LIBRARY_MODE
