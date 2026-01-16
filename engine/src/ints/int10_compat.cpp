/*
 * int10_compat.cpp - Compatibility shims for INT 10h APIs
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
#include "vga.h"

using namespace dosbox;

// ═══════════════════════════════════════════════════════════════════════════════
// CurMode Compatibility Shims
// ═══════════════════════════════════════════════════════════════════════════════
// Provides access to vga.cur_mode via current_context().
// New code should use DOSBoxContext.vga.cur_mode directly.

VideoModeBlock* INT10_GetCurMode() {
    if (!has_current_context()) return nullptr;
    return current_context().vga.cur_mode;
}

void INT10_SetCurModePtr(VideoModeBlock* mode) {
    if (has_current_context()) {
        current_context().vga.cur_mode = mode;
    }
}
