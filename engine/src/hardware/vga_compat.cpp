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

#include "dosbox/dosbox_context.h"
#include "vga.h"

#include <cstddef>

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

// ═══════════════════════════════════════════════════════════════════════════════
// VSync State Compatibility Shim
// ═══════════════════════════════════════════════════════════════════════════════
// Provides access to vsync state via current_context().
// Previously an inline macro in vga.h, moved here to eliminate
// current_context() calls from header files (PR #9 cleanup).
//
// The context's VgaState::VsyncState and vga.h's vsync_state have
// identical data layout (double + 3 bools). The reinterpret_cast
// is safe because both are standard-layout types with matching members.

// Verify layout compatibility at compile time
static_assert(sizeof(VgaState::VsyncState) >= sizeof(vsync_state),
    "VsyncState must be at least as large as vsync_state");
static_assert(offsetof(vsync_state, period) == 0,
    "vsync_state::period must be at offset 0");

static vsync_state fallback_vsync = {};

vsync_state& vga_get_vsync() {
    if (has_current_context()) {
        return reinterpret_cast<vsync_state&>(current_context().vga.vsync);
    }
    return fallback_vsync;
}

// ═══════════════════════════════════════════════════════════════════════════════
// VGA Hardware State Compatibility Shim (Sprint 2 Completion)
// ═══════════════════════════════════════════════════════════════════════════════
// Provides access to the full VGA_Type hardware state via current_context().
// The `extern VGA_Type vga;` in vga.h is replaced by a macro calling this function.
// New code should use DOSBoxContext.vga.hw-> directly when possible.

static VGA_Type fallback_vga_hw = {};

VGA_Type& vga_get_hw() {
    if (has_current_context()) {
        auto* hw = current_context().vga.hw;
        if (hw) {
            return *hw;
        }
    }
    return fallback_vga_hw;
}
