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

/*
 * CPU Globals Sync Convention
 * ---------------------------
 * ENTRY: save CPU_Cycles, set CPU_Cycles = budget
 * EXIT:  consumed = budget - CPU_Cycles
 *        restore CPU_Cycles to saved value
 *        ctx->timing.total_cycles += consumed
 *
 * Registers remain in CPU globals between calls (single-instance).
 */

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

/**
 * @brief Reset CPU state to initial values.
 *
 * Re-initializes all x86 registers, segment descriptors, and flags
 * to their power-on defaults. Call this during instance reset to ensure
 * deterministic execution from a known state.
 */
void reset_cpu_bridge();

/**
 * @brief Snapshot CPU GPRs, EIP, EFLAGS, and segment registers.
 *
 * Reads from the cpu_regs and Segs globals and packs into fixed-width
 * fields for serialization. Used by V5 engine state save (REQ-SR-002).
 *
 * @param gpr      Output array of 8 uint32_t (AX,CX,DX,BX,SP,BP,SI,DI)
 * @param eip      Output EIP value
 * @param eflags   Output EFLAGS value
 * @param seg_val  Output array of 6 uint16_t segment selectors (ES,CS,SS,DS,FS,GS)
 * @param seg_phys Output array of 6 uint32_t segment physical bases
 * @param seg_limit Output array of 6 uint32_t segment limits
 */
void snapshot_cpu_gprs(
    uint32_t gpr[8], uint32_t& eip, uint32_t& eflags,
    uint16_t seg_val[6], uint32_t seg_phys[6], uint32_t seg_limit[6]);

/**
 * @brief Restore CPU GPRs, EIP, EFLAGS, and segment registers.
 *
 * Writes to the cpu_regs and Segs globals from fixed-width fields.
 * Used by V5 engine state load (REQ-SR-002).
 */
void restore_cpu_gprs(
    const uint32_t gpr[8], uint32_t eip, uint32_t eflags,
    const uint16_t seg_val[6], const uint32_t seg_phys[6], const uint32_t seg_limit[6]);

// Forward declaration
struct EngineStateVgaRegisters;
struct EngineStateCpu;

/**
 * @brief Snapshot CPU cycle/NMI control globals into a serialization struct.
 */
void snapshot_cpu_control(EngineStateCpu& out);

/**
 * @brief Restore CPU cycle/NMI control globals from a serialization struct.
 */
void restore_cpu_control(const EngineStateCpu& in);

/**
 * @brief Check if VGA hardware is available (mem.linear != nullptr).
 */
bool vga_hw_available();

/**
 * @brief Get pointer to VGA linear memory (VRAM).
 * @return Pointer to VRAM, or nullptr if not available.
 */
uint8_t* vga_mem_linear();

/**
 * @brief Get size of VGA memory in bytes.
 */
uint32_t vga_mem_size();

/**
 * @brief Recompute derived VGA state after register restore.
 *
 * Calls VGA_DetermineMode() + VGA_SetupHandlers().
 */
void vga_post_restore();

/**
 * @brief Snapshot VGA hardware registers into serialization struct.
 *
 * Reads from the vga global (VGA_Type) and packs into fixed-width fields
 * for serialization. Captures seq, attr, crtc, gfx, DAC, latch, config
 * subset, SVGA bank state, and memory metadata.
 *
 * Used by V5 engine state save (REQ-SR-003).
 *
 * @param out Output struct to fill
 */
void snapshot_vga_registers(EngineStateVgaRegisters& out);

/**
 * @brief Restore VGA hardware registers from serialization struct.
 *
 * Writes to the vga global (VGA_Type) from fixed-width fields.
 * After calling, invoke VGA_DetermineMode() + VGA_SetupHandlers()
 * to recompute derived rendering state.
 *
 * Used by V5 engine state load (REQ-SR-003).
 *
 * @param in Input struct to restore from
 */
void restore_vga_registers(const EngineStateVgaRegisters& in);

} // namespace dosbox

#endif // DOSBOX_CPU_BRIDGE_H
