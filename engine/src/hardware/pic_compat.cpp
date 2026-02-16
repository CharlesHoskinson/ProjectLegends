/*
 * pic_compat.cpp - Compatibility shims for PIC/Timer APIs
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
#include "timer.h"

using namespace dosbox;

// ═══════════════════════════════════════════════════════════════════════════════
// Timer Compatibility Shims
// ═══════════════════════════════════════════════════════════════════════════════
// These functions provide the legacy TIMER_* API using current_context().
// New code should use DOSBoxContext.pic methods directly.

void TIMER_ShutdownTickHandlers() {
    if (!has_current_context()) return;
    current_context().pic.shutdown_tickers();
}

void TIMER_DelTickHandler(TIMER_TickHandler handler) {
    if (!has_current_context()) return;
    current_context().pic.remove_ticker(handler);
}

void TIMER_AddTickHandler(TIMER_TickHandler handler) {
    if (!has_current_context()) return;
    current_context().pic.add_ticker(handler);
}

// Called from TIMER_AddTick to execute registered tick handlers
void TIMER_ExecuteTickHandlers() {
    if (!has_current_context()) return;
    current_context().pic.execute_tickers();
}

// ═══════════════════════════════════════════════════════════════════════════════
// PIC Controller Compatibility Shims (Sprint 2 Completion)
// ═══════════════════════════════════════════════════════════════════════════════
// These provide access to PIC controller state through current_context().
// New code should use DOSBoxContext.pic.controllers[] directly.

namespace {
    // Static fallbacks for when no context is active
    static dosbox::PicController fallback_controllers[2];
    static bool fallback_enable_slave_pic = true;
    static bool fallback_enable_pc_xt_nmi_mask = false;
}

dosbox::PicController& pic_get_controller(int index) {
    if (has_current_context()) {
        return current_context().pic.controllers[index & 1];
    }
    return fallback_controllers[index & 1];
}

dosbox::PicController& pic_get_master() {
    return pic_get_controller(0);
}

dosbox::PicController& pic_get_slave() {
    return pic_get_controller(1);
}

bool& pic_get_enable_slave_pic() {
    if (has_current_context()) {
        return current_context().pic.enable_slave_pic;
    }
    return fallback_enable_slave_pic;
}

bool& pic_get_enable_pc_xt_nmi_mask() {
    if (has_current_context()) {
        return current_context().pic.enable_pc_xt_nmi_mask;
    }
    return fallback_enable_pc_xt_nmi_mask;
}
