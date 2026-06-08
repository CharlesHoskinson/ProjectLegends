/**
 * @file cpu_bridge.cpp
 * @brief CPU execution bridge for library mode.
 *
 * Bridges the library mode context-based API to the DOSBox-X CPU core.
 * Calls CPU_Core_Normal_Run (or whichever decoder cpudecoder points to)
 * using CPU_Cycles as the execution budget.
 *
 * @copyright GPL-2.0-or-later
 */

#include "dosbox/cpu_bridge.h"
#include "dosbox/dosbox_context.h"
#include "dosbox/engine_state.h"
#include "cpu.h"
#include "pic.h"
#include "callback.h"

#include <gsl-lite/gsl-lite.hpp>
#include <algorithm>
#include <cassert>
#include <limits>
#include <cstring>

extern void CPU_Init();
extern void CPU_LibraryInit();
extern bool CPU_IsHLTed();
extern Bitu CPU_extflags_toggle;

namespace dosbox {

namespace {
bool g_bridge_initialized = false;

void sync_context_cpu_state(DOSBoxContext& ctx)
{
    ctx.cpu_state.cycles = CPU_Cycles;
    ctx.cpu_state.cycle_left = CPU_CycleLeft;
    ctx.cpu_state.cycle_max = CPU_CycleMax;
    ctx.cpu_state.cycle_old_max = CPU_OldCycleMax;
    ctx.cpu_state.cycle_percent_used = CPU_CyclePercUsed;
    ctx.cpu_state.cycle_limit = CPU_CycleLimit;
    ctx.cpu_state.cycles_set = CPU_CyclesSet;
    ctx.cpu_state.io_delay_removed = CPU_IODelayRemoved;
    ctx.cpu_state.extflags_toggle = static_cast<uint32_t>(CPU_extflags_toggle);
    ctx.cpu_state.cycle_auto_adjust = CPU_CycleAutoAdjust;
    ctx.cpu_state.skip_cycle_auto_adjust = CPU_SkipCycleAutoAdjust;
    ctx.cpu_state.nmi_gate = CPU_NMI_gate;
    ctx.cpu_state.nmi_active = CPU_NMI_active;
    ctx.cpu_state.nmi_pending = CPU_NMI_pending;
    ctx.cpu_state.halted = CPU_IsHLTed();
}
} // anonymous namespace

void init_cpu_bridge() {
    if (!g_bridge_initialized) {
        // Initialize CPU state if not already done
        ::CPU_Init();

        // Ensure decoder is set
        if (cpudecoder == nullptr)
            cpudecoder = &CPU_Core_Simple_Run;

        g_bridge_initialized = true;
    }
}

bool is_cpu_bridge_ready() {
    return g_bridge_initialized;
}

void reset_cpu_bridge() {
    // Re-initialize all CPU registers, segments, flags to power-on defaults.
    // This ensures deterministic execution after a context reset.
    ::CPU_LibraryInit();
    cpudecoder = &CPU_Core_Simple_Run;
}

CpuExecuteResult execute_cycles(DOSBoxContext* ctx, uint64_t cycles) {
    CpuExecuteResult result{};
    result.cycles_executed = 0;
    result.events_processed = 0;
    result.stop_reason = CpuStopReason::Completed;
    result.callback_id = -1;

    if (!is_cpu_bridge_ready()) {
        init_cpu_bridge();
    }

    if (ctx == nullptr) {
        result.stop_reason = CpuStopReason::Error;
        return result;
    }

    if (ctx->stop_requested()) {
        result.stop_reason = CpuStopReason::UserRequest;
        return result;
    }

    // Zero cycles: no-op
    if (cycles == 0) {
        return result;
    }

    // Clamp to signed range for CPU_Cycles (intptr_t)
    constexpr uint64_t max_budget = static_cast<uint64_t>(std::numeric_limits<cpu_cycles_count_t>::max());
    auto budget = static_cast<cpu_cycles_count_t>(std::min(cycles, max_budget));

    cpu_cycles_count_t saved = CPU_Cycles;
    CPU_Cycles = budget;

    // Process pending PIC events before CPU execution (C2 fix)
    if (PIC_RunQueue())
        result.events_processed++;

    Bits ret = (*cpudecoder)();

    // Check for NMI after execution (C2 fix)
    CPU_Check_NMI();

    // Compute consumed cycles (decoder may overshoot by 1 instruction)
    cpu_cycles_count_t consumed = budget - CPU_Cycles;
    if (consumed < 0) consumed = 0;
    // Clamp to requested budget - overshoot is a decoder implementation detail
    if (static_cast<uint64_t>(consumed) > cycles)
        consumed = static_cast<cpu_cycles_count_t>(cycles);
    result.cycles_executed = static_cast<uint64_t>(consumed);

    // Restore any remaining cycles
    CPU_Cycles = saved;
#ifndef NDEBUG
    assert(CPU_Cycles == saved && "CPU_Cycles not restored after bridge call");
#endif

    if (ret == CBRET_STOP) {
        result.stop_reason = CpuStopReason::Halt;
    } else if (ret > CBRET_STOP) {
        result.stop_reason = CpuStopReason::Callback;
        result.callback_id = static_cast<int32_t>(ret);
    } else if (CPU_IsHLTed()) {
        result.stop_reason = CpuStopReason::Halt;
    }
    // ret == CBRET_NONE (0) means normal completion
    sync_context_cpu_state(*ctx);

    // Update context timing state
    ctx->timing.total_cycles += result.cycles_executed;

    return result;
}

CpuExecuteResult execute_ms(DOSBoxContext* ctx, uint32_t ms, uint32_t cycles_per_ms) {
    gsl_Expects(cycles_per_ms > 0);

    uint64_t total_cycles = static_cast<uint64_t>(ms) * cycles_per_ms;
    auto result = execute_cycles(ctx, total_cycles);

    if (ctx) {
        uint32_t ms_executed = static_cast<uint32_t>(result.cycles_executed / cycles_per_ms);
        ctx->timing.virtual_ticks_ms += ms_executed;
    }

    return result;
}

void snapshot_cpu_gprs(
    uint32_t gpr[8], uint32_t& eip, uint32_t& eflags,
    uint16_t seg_val[6], uint32_t seg_phys[6], uint32_t seg_limit[6])
{
    for (int i = 0; i < 8; ++i)
        gpr[i] = cpu_regs.regs[i].dword[DW_INDEX];
    eip = cpu_regs.ip.dword[DW_INDEX];
    eflags = static_cast<uint32_t>(cpu_regs.flags);
    for (int i = 0; i < 6; ++i) {
        seg_val[i] = static_cast<uint16_t>(Segs.val[i]);
        seg_phys[i] = static_cast<uint32_t>(Segs.phys[i]);
        seg_limit[i] = static_cast<uint32_t>(Segs.limit[i]);
    }
}

void restore_cpu_gprs(
    const uint32_t gpr[8], uint32_t eip, uint32_t eflags,
    const uint16_t seg_val[6], const uint32_t seg_phys[6], const uint32_t seg_limit[6])
{
    for (int i = 0; i < 8; ++i)
        cpu_regs.regs[i].dword[DW_INDEX] = gpr[i];
    cpu_regs.ip.dword[DW_INDEX] = eip;
    cpu_regs.flags = static_cast<Bitu>(eflags);
    for (int i = 0; i < 6; ++i) {
        Segs.val[i] = static_cast<Bitu>(seg_val[i]);
        Segs.phys[i] = static_cast<PhysPt>(seg_phys[i]);
        Segs.limit[i] = static_cast<PhysPt>(seg_limit[i]);
    }
}

void snapshot_cpu_control(EngineStateCpu& out)
{
    out.cycles = CPU_Cycles;
    out.cycle_left = CPU_CycleLeft;
    out.cycle_max = CPU_CycleMax;
    out.cycle_old_max = CPU_OldCycleMax;
    out.cycle_percent_used = CPU_CyclePercUsed;
    out.cycle_limit = CPU_CycleLimit;
    out.cycle_up = 0;
    out.cycle_down = 0;
    out.cycles_set = CPU_CyclesSet;
    out.io_delay_removed = CPU_IODelayRemoved;
    out.extflags_toggle = static_cast<uint32_t>(CPU_extflags_toggle);
    out.cycle_auto_adjust = CPU_CycleAutoAdjust ? 1 : 0;
    out.skip_cycle_auto_adjust = CPU_SkipCycleAutoAdjust ? 1 : 0;
    out.nmi_gate = CPU_NMI_gate ? 1 : 0;
    out.nmi_active = CPU_NMI_active ? 1 : 0;
    out.nmi_pending = CPU_NMI_pending ? 1 : 0;
    out.halted = CPU_IsHLTed() ? 1 : 0;
}

void restore_cpu_control(const EngineStateCpu& in)
{
    CPU_Cycles = static_cast<cpu_cycles_count_t>(in.cycles);
    CPU_CycleLeft = static_cast<cpu_cycles_count_t>(in.cycle_left);
    CPU_CycleMax = static_cast<cpu_cycles_count_t>(in.cycle_max);
    CPU_OldCycleMax = static_cast<cpu_cycles_count_t>(in.cycle_old_max);
    CPU_CyclePercUsed = static_cast<cpu_cycles_count_t>(in.cycle_percent_used);
    CPU_CycleLimit = static_cast<cpu_cycles_count_t>(in.cycle_limit);
    CPU_CyclesSet = static_cast<cpu_cycles_count_t>(in.cycles_set);
    CPU_IODelayRemoved = static_cast<cpu_cycles_count_t>(in.io_delay_removed);
    CPU_extflags_toggle = static_cast<Bitu>(in.extflags_toggle);
    CPU_CycleAutoAdjust = in.cycle_auto_adjust != 0;
    CPU_SkipCycleAutoAdjust = in.skip_cycle_auto_adjust != 0;
    CPU_NMI_gate = in.nmi_gate != 0;
    CPU_NMI_active = in.nmi_active != 0;
    CPU_NMI_pending = in.nmi_pending != 0;
    if (in.halted == 0 && CPU_IsHLTed()) {
        cpudecoder = &CPU_Core_Simple_Run;
    }
}

// VGA snapshot/restore and helper functions are in vga_bridge.cpp
// (separate TU to avoid vga.h C7626 error under /permissive-)

} // namespace dosbox
