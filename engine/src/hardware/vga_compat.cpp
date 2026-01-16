/*
 * vga_compat.cpp - Compatibility shims for VGA APIs
 *
 * This file provides legacy API wrappers that use current_context() internally.
 * These exist to support code that hasn't been migrated to explicit context passing.
 *
 * Per Sprint 2 policy, current_context() is allowed in *_compat.cpp files.
 *
 * Copyright (C) 2002-2021  The DOSBox Team
 * SPDX-License-Identifier: GPL-2.0-or-later
 */

#include "dosbox.h"
#include "dosbox/dosbox_context.h"

using namespace dosbox;

// ═══════════════════════════════════════════════════════════════════════════════
// VGA LFB Compatibility Shim
// ═══════════════════════════════════════════════════════════════════════════════
// Provides access to assigned_lfb via current_context().
// New code should use DOSBoxContext.vga.assigned_lfb directly.

static uint32_t fallback_assigned_lfb = 0;

uint32_t& vga_get_assigned_lfb() {
    if (has_current_context()) {
        return current_context().vga.assigned_lfb;
    }
    return fallback_assigned_lfb;
}
