/**
 * @file cpu_bridge.h
 * @brief CPU execution bridge for library mode.
 *
 * Provides a clean interface for executing CPU cycles in library mode,
 * bridging between the context-based API and the global-based DOSBox-X engine.
 *
 * @copyright GPL-2.0-or-later
 */

#ifndef DOSBOX_CPU_BRIDGE_H
#define DOSBOX_CPU_BRIDGE_H

#include <cstdint>

namespace dosbox {

// Forward declarations
class DOSBoxContext;

/**
 * @brief Stop reason codes from CPU execution.
 */
enum class CpuStopReason : uint32_t {
    Completed = 0,      ///< Requested cycles completed
    Halt = 1,           ///< CPU executed HLT instruction
    Breakpoint = 2,     ///< Hit debugger breakpoint
    Error = 3,          ///< CPU exception or error
    UserRequest = 4,    ///< User requested stop
    Callback = 5        ///< Callback needs external handling
};

/**
 * @brief Result from CPU cycle execution.
 */
struct CpuExecuteResult {
    uint64_t cycles_executed;   ///< Actual cycles executed
    uint32_t events_processed;  ///< Number of PIC events processed
    CpuStopReason stop_reason;  ///< Why execution stopped
    int32_t callback_id;        ///< If Callback, which one (-1 if none)
};

/**
 * @brief Execute CPU cycles in library mode.
 *
 * This function bridges the library mode API to the actual DOSBox-X
 * CPU execution. It sets up the cycle counters, calls the CPU decoder,
 * and handles events.
 *
 * @param ctx The DOSBox context (used for stop_requested check)
 * @param cycles Number of cycles to execute
 * @return Execution result with cycles executed and stop reason
 *
 * @note This function must be called from the emulation thread.
 * @note The context must be set as current before calling.
 */
CpuExecuteResult execute_cycles(DOSBoxContext* ctx, uint64_t cycles);

/**
 * @brief Execute one millisecond worth of emulation.
 *
 * Convenience wrapper that converts ms to cycles and executes.
 *
 * @param ctx The DOSBox context
 * @param ms Milliseconds to execute
 * @param cycles_per_ms CPU cycles per millisecond
 * @return Execution result
 */
CpuExecuteResult execute_ms(DOSBoxContext* ctx, uint32_t ms, uint32_t cycles_per_ms);

/**
 * @brief Initialize the CPU bridge.
 *
 * Must be called once before execute_cycles can be used.
 * Sets up the CPU decoder function pointer if not already set.
 */
void init_cpu_bridge();

/**
 * @brief Check if CPU bridge is ready for execution.
 *
 * @return true if cpudecoder is set and ready
 */
bool is_cpu_bridge_ready();

} // namespace dosbox

#endif // DOSBOX_CPU_BRIDGE_H
