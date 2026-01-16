/**
 * @file cpu_bridge.cpp
 * @brief CPU execution bridge for library mode (stub implementation).
 *
 * This is a stub implementation for library mode builds that do not
 * have access to the full DOSBox-X CPU core. It simulates CPU execution
 * by incrementing cycle counters without executing actual instructions.
 *
 * In full DOSBox-X builds, this file is replaced with the real
 * implementation that bridges to the CPU core.
 *
 * @copyright GPL-2.0-or-later
 */

#include "dosbox/cpu_bridge.h"
#include "dosbox/dosbox_context.h"

#include <algorithm>

namespace dosbox {

namespace {

// Flag to track if bridge has been initialized
bool g_bridge_initialized = false;

// Maximum cycles per batch to allow for event checking
constexpr uint64_t MAX_CYCLES_PER_BATCH = 10000;

} // anonymous namespace

void init_cpu_bridge() {
    g_bridge_initialized = true;
}

bool is_cpu_bridge_ready() {
    return g_bridge_initialized;
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

    // Validate input
    if (ctx == nullptr) {
        result.stop_reason = CpuStopReason::Error;
        return result;
    }

    // Check for stop request
    if (ctx->stop_requested()) {
        result.stop_reason = CpuStopReason::UserRequest;
        return result;
    }

    // STUB IMPLEMENTATION: Simulate CPU execution
    // In a real implementation, this would execute actual CPU instructions
    // through the DOSBox-X core. Here we just increment counters.

    uint64_t cycles_remaining = cycles;

    while (cycles_remaining > 0) {
        // Check for stop request
        if (ctx->stop_requested()) {
            result.stop_reason = CpuStopReason::UserRequest;
            break;
        }

        // Simulate batch execution
        uint64_t batch = std::min(cycles_remaining, MAX_CYCLES_PER_BATCH);

        // In stub mode, we "execute" all requested cycles instantly
        result.cycles_executed += batch;
        cycles_remaining -= batch;

        // Simulate some event processing (1 event per batch)
        result.events_processed++;
    }

    // Update context timing state
    ctx->timing.total_cycles += result.cycles_executed;

    return result;
}

CpuExecuteResult execute_ms(DOSBoxContext* ctx, uint32_t ms, uint32_t cycles_per_ms) {
    uint64_t total_cycles = static_cast<uint64_t>(ms) * cycles_per_ms;
    auto result = execute_cycles(ctx, total_cycles);

    // Update virtual ticks if context provided
    if (ctx) {
        // Calculate actual ms executed based on cycles
        uint32_t ms_executed = static_cast<uint32_t>(result.cycles_executed / cycles_per_ms);
        ctx->timing.virtual_ticks_ms += ms_executed;
    }

    return result;
}

} // namespace dosbox
