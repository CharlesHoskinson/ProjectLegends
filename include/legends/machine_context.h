/**
 * @file machine_context.h
 * @brief Top-level emulator state container.
 *
 * MachineContext owns all emulator subsystems and provides
 * lifecycle management. This replaces the global variable
 * approach used in legacy DOSBox-X.
 *
 * Requirements implemented:
 * - REQ-GSE-001: Encapsulate all mutable state
 * - REQ-GSE-002: Explicit initialization
 * - REQ-GSE-010-012: Lifecycle management
 * - REQ-GSE-020-024: State machine enforcement
 *
 * @copyright GPL-2.0-or-later
 */

#pragma once

#include "error.h"
#include "memory.h"
#include "cpu_context.h"
#include "dma.h"

#include <memory>
#include <optional>
#include <atomic>
#include <string>

namespace legends {

// Forward declarations for subsystems not yet implemented
class VgaContext;
class DosKernel;
class PicController;
class PitTimer;
class KeyboardController;
class MouseController;
class SoundSubsystem;

// ─────────────────────────────────────────────────────────────────────────────
// Machine State
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Machine state enumeration.
 *
 * Defines the lifecycle states for MachineContext.
 */
enum class MachineState {
    Created,      ///< Constructed but not initialized
    Initialized,  ///< Ready to run
    Running,      ///< Currently executing
    Paused,       ///< Execution suspended
    Stopped,      ///< Execution completed
    Shutdown,     ///< Cleanup in progress
    Destroyed     ///< Resources released
};

/**
 * @brief Get string representation of machine state.
 */
[[nodiscard]] inline const char* to_string(MachineState state) noexcept {
    switch (state) {
        case MachineState::Created:     return "Created";
        case MachineState::Initialized: return "Initialized";
        case MachineState::Running:     return "Running";
        case MachineState::Paused:      return "Paused";
        case MachineState::Stopped:     return "Stopped";
        case MachineState::Shutdown:    return "Shutdown";
        case MachineState::Destroyed:   return "Destroyed";
    }
    return "Unknown";
}

// ─────────────────────────────────────────────────────────────────────────────
// Machine Type
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Machine type enumeration.
 */
enum class MachineType {
    PC,           ///< IBM PC/XT compatible
    Tandy,        ///< Tandy 1000
    PCjr,         ///< IBM PCjr
    Hercules,     ///< Hercules graphics
    CGA,          ///< CGA graphics
    EGA,          ///< EGA graphics
    VGA,          ///< VGA graphics
    SVGA_S3,      ///< S3 SVGA
    PC98          ///< NEC PC-98
};

// ─────────────────────────────────────────────────────────────────────────────
// Machine Configuration
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Configuration for machine creation.
 *
 * Contains all parameters needed to construct and initialize
 * a MachineContext.
 */
struct MachineConfig {
    // Memory configuration
    size_t memory_size = 16 * 1024 * 1024;  ///< Guest RAM (default 16MB)
    size_t vga_memory = 256 * 1024;         ///< VGA RAM (default 256KB)

    // CPU configuration
    uint32_t cpu_cycles = 3000;             ///< Cycles per millisecond
    bool cpu_dynamic_core = false;          ///< Use dynamic recompiler

    // Machine type
    MachineType machine_type = MachineType::VGA;

    // Timing
    bool deterministic = false;             ///< Deterministic mode for testing

    // Peripherals
    bool sound_enabled = true;              ///< Enable sound subsystem
    bool sb16_enabled = true;               ///< Enable Sound Blaster 16
    bool adlib_enabled = true;              ///< Enable AdLib/OPL

    // Debug
    bool debug_mode = false;                ///< Enable debug features

    /**
     * @brief Create minimal configuration for testing.
     *
     * Returns a configuration with minimal memory and
     * disabled peripherals suitable for unit tests.
     *
     * @return Minimal configuration
     */
    [[nodiscard]] static MachineConfig minimal() noexcept {
        MachineConfig config;
        config.memory_size = 1024 * 1024;   // 1MB
        config.vga_memory = 64 * 1024;      // 64KB
        config.sound_enabled = false;
        config.deterministic = true;
        return config;
    }

    /**
     * @brief Create default VGA machine configuration.
     * @return Default VGA configuration
     */
    [[nodiscard]] static MachineConfig vga_default() noexcept {
        return MachineConfig{};
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// Machine Context
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Top-level emulator context.
 *
 * Owns all subsystems and manages lifecycle. Single point of
 * access to all emulator state.
 *
 * ## Lifecycle
 * 1. Create: `MachineContext ctx(config)`
 * 2. Initialize: `ctx.initialize()`
 * 3. Run: `ctx.step(ms)` or `ctx.run()`
 * 4. Shutdown: `ctx.shutdown()`
 *
 * ## State Machine
 * @verbatim
 *   Created -> [initialize] -> Initialized
 *   Initialized -> [step/run] -> Running
 *   Running -> [pause] -> Paused
 *   Running -> [stop] -> Stopped
 *   Paused -> [resume] -> Running
 *   Any -> [shutdown] -> Shutdown
 * @endverbatim
 *
 * ## Thread Safety
 * Not thread-safe except for request_stop() which is atomic.
 * All other methods must be called from the main emulation thread.
 *
 * ## Example
 * @code
 *   MachineConfig config;
 *   config.memory_size = 16 * 1024 * 1024;
 *
 *   MachineContext ctx(config);
 *   auto result = ctx.initialize();
 *   if (!result.has_value()) {
 *       LOG_ERROR("Init failed: {}", result.error().format());
 *       return;
 *   }
 *
 *   while (ctx.state() == MachineState::Running) {
 *       ctx.step(10);  // Run 10ms
 *   }
 *
 *   ctx.shutdown();
 * @endcode
 *
 * @note Non-copyable. Movable only before initialization.
 */
class MachineContext {
public:
    /**
     * @brief Construct context with configuration.
     * @param config Machine configuration
     *
     * Does NOT initialize subsystems - call initialize() separately.
     * This allows configuration validation before resource allocation.
     *
     * @post state() == MachineState::Created
     */
    explicit MachineContext(const MachineConfig& config);

    /**
     * @brief Default constructor with default configuration.
     */
    MachineContext();

    /**
     * @brief Destructor - ensures cleanup.
     *
     * Calls shutdown() if not already in Shutdown/Destroyed state.
     */
    ~MachineContext();

    // Non-copyable
    MachineContext(const MachineContext&) = delete;
    MachineContext& operator=(const MachineContext&) = delete;

    // Movable only before initialization
    MachineContext(MachineContext&& other) noexcept;
    MachineContext& operator=(MachineContext&& other) noexcept;

    // ─────────────────────────────────────────────────────────────────────────
    // Lifecycle Operations
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Initialize all subsystems.
     *
     * Must be called before step/run. Initializes subsystems in
     * dependency order. On failure, cleans up partial initialization.
     *
     * @return Result indicating success or failure
     *
     * @pre state() == MachineState::Created
     * @post state() == MachineState::Initialized on success
     *
     * @note Errors are returned via Result, not thrown.
     */
    Result<void> initialize();

    /**
     * @brief Execute emulation for specified duration.
     *
     * Executes the specified number of milliseconds of emulated
     * time. The actual execution time depends on host performance.
     *
     * @param ms Milliseconds of emulated time to execute
     * @return Result with actual steps executed or error
     *
     * @pre state() == Initialized, Running, or Paused
     * @post state() == Running (or Stopped if stop requested)
     */
    Result<uint32_t> step(uint32_t ms);

    /**
     * @brief Run until stop requested.
     *
     * Blocks until request_stop() is called or error occurs.
     * Suitable for simple use cases without external event loop.
     *
     * @return Result indicating completion reason
     *
     * @pre state() == Initialized
     * @post state() == Stopped
     */
    Result<void> run();

    /**
     * @brief Request stop from another thread.
     *
     * Thread-safe. Sets flag checked by run/step loop.
     * The emulator will stop at the next safe point.
     *
     * @note This is the ONLY thread-safe method.
     */
    void request_stop() noexcept;

    /**
     * @brief Pause execution.
     *
     * Suspends execution but keeps state. Can resume later.
     *
     * @return Result indicating success or error
     *
     * @pre state() == MachineState::Running
     * @post state() == MachineState::Paused on success
     */
    Result<void> pause();

    /**
     * @brief Resume paused execution.
     *
     * @return Result indicating success or error
     *
     * @pre state() == MachineState::Paused
     * @post state() == MachineState::Running on success
     */
    Result<void> resume();

    /**
     * @brief Shutdown all subsystems.
     *
     * Releases resources in reverse initialization order.
     * Safe to call multiple times (idempotent).
     * Called automatically by destructor.
     *
     * @post state() == MachineState::Shutdown
     */
    void shutdown() noexcept;

    /**
     * @brief Reset machine to initial state.
     *
     * Equivalent to power cycling. Reinitializes all subsystems
     * but keeps the same configuration.
     *
     * @return Result indicating success or error
     *
     * @pre state() != Created
     * @post state() == Initialized on success
     */
    Result<void> reset();

    // ─────────────────────────────────────────────────────────────────────────
    // Subsystem Access (Public Members)
    // ─────────────────────────────────────────────────────────────────────────

    /** @brief CPU state (registers, flags, segments) */
    CpuContext cpu;

    /** @brief Guest memory (nullptr until initialized) */
    std::unique_ptr<GuestMemory> memory;

    /** @brief DMA subsystem (nullptr until initialized) */
    std::unique_ptr<DmaSubsystem> dma;

    // Future subsystems (nullptr until implemented)
    // std::unique_ptr<VgaContext> vga;
    // std::unique_ptr<DosKernel> dos;
    // std::unique_ptr<PicController> pic;
    // std::unique_ptr<PitTimer> pit;
    // std::unique_ptr<KeyboardController> keyboard;
    // std::unique_ptr<MouseController> mouse;
    // std::unique_ptr<SoundSubsystem> sound;

    // ─────────────────────────────────────────────────────────────────────────
    // State Queries
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Get current machine state.
     * @return Current state
     */
    [[nodiscard]] MachineState state() const noexcept { return state_; }

    /**
     * @brief Check if machine has been initialized.
     * @return true if initialize() has been called successfully
     */
    [[nodiscard]] bool is_initialized() const noexcept {
        return state_ != MachineState::Created &&
               state_ != MachineState::Destroyed;
    }

    /**
     * @brief Check if machine is currently running.
     * @return true if in Running state
     */
    [[nodiscard]] bool is_running() const noexcept {
        return state_ == MachineState::Running;
    }

    /**
     * @brief Check if stop has been requested.
     * @return true if request_stop() was called
     */
    [[nodiscard]] bool stop_requested() const noexcept {
        return stop_requested_.load(std::memory_order_acquire);
    }

    /**
     * @brief Get machine configuration.
     * @return Reference to configuration
     */
    [[nodiscard]] const MachineConfig& config() const noexcept {
        return config_;
    }

    /**
     * @brief Get last error (if any).
     * @return Optional error from last failed operation
     */
    [[nodiscard]] const std::optional<Error>& last_error() const noexcept {
        return last_error_;
    }

    /**
     * @brief Get total CPU cycles executed.
     * @return Total cycles since initialization
     */
    [[nodiscard]] uint64_t total_cycles() const noexcept {
        return total_cycles_;
    }

    /**
     * @brief Get virtual time in milliseconds.
     * @return Emulated milliseconds since initialization
     */
    [[nodiscard]] uint32_t virtual_ticks() const noexcept {
        return virtual_ticks_ms_;
    }

private:
    // Configuration
    MachineConfig config_;

    // State
    MachineState state_ = MachineState::Created;
    std::optional<Error> last_error_;

    // Timing
    uint64_t total_cycles_ = 0;
    uint32_t virtual_ticks_ms_ = 0;

    // Stop flag (atomic for thread safety)
    std::atomic<bool> stop_requested_{false};

    // ─────────────────────────────────────────────────────────────────────────
    // Initialization Tracking
    // ─────────────────────────────────────────────────────────────────────────

    /**
     * @brief Initialization stage for cleanup on failure.
     */
    enum class InitStage {
        None,
        Memory,
        Cpu,
        Pic,
        Pit,
        Dma,
        Vga,
        Input,
        Sound,
        Dos,
        Bios,
        Complete
    };

    InitStage init_stage_ = InitStage::None;

    // ─────────────────────────────────────────────────────────────────────────
    // Internal Initialization Functions
    // ─────────────────────────────────────────────────────────────────────────

    Result<void> init_memory();
    Result<void> init_cpu();
    Result<void> init_pic();
    Result<void> init_pit();
    Result<void> init_dma();
    Result<void> init_vga();
    Result<void> init_input();
    Result<void> init_sound();
    Result<void> init_dos();
    Result<void> init_bios();

    /**
     * @brief Cleanup subsystems down to specified stage.
     * @param target Stage to cleanup to (exclusive)
     */
    void cleanup_to_stage(InitStage target) noexcept;

    /**
     * @brief Set error state.
     * @param error Error to store
     */
    void set_error(Error error) noexcept {
        last_error_ = std::move(error);
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// Compatibility Shim
// ─────────────────────────────────────────────────────────────────────────────

namespace compat {

/**
 * @brief Set the current context for this thread.
 *
 * Must be called before any code using compat::current().
 * Typically called at the start of step() or run().
 *
 * @param ctx Context to set (may be nullptr to clear)
 */
void set_current_context(MachineContext* ctx) noexcept;

/**
 * @brief Get the current context.
 *
 * @return Reference to current context
 * @throws Nothing in release; asserts in debug if no context set
 *
 * @pre set_current_context() was called with non-null context
 */
[[nodiscard]] MachineContext& current();

/**
 * @brief Get current context pointer (may be null).
 *
 * Safer than current() for code that can handle no context.
 *
 * @return Pointer to current context, or nullptr if not set
 */
[[nodiscard]] MachineContext* current_ptr() noexcept;

/**
 * @brief Check if a context is set.
 * @return true if set_current_context was called with non-null
 */
[[nodiscard]] bool has_context() noexcept;

/**
 * @brief RAII guard for setting current context.
 *
 * Sets the current context on construction and restores
 * the previous context on destruction.
 *
 * @code
 *   {
 *       compat::ContextGuard guard(my_context);
 *       // compat::current() returns my_context here
 *   }
 *   // Previous context restored
 * @endcode
 */
class ContextGuard {
public:
    /**
     * @brief Set context and save previous.
     * @param ctx Context to set as current
     */
    explicit ContextGuard(MachineContext& ctx) noexcept;

    /**
     * @brief Restore previous context.
     */
    ~ContextGuard() noexcept;

    // Non-copyable, non-movable
    ContextGuard(const ContextGuard&) = delete;
    ContextGuard& operator=(const ContextGuard&) = delete;
    ContextGuard(ContextGuard&&) = delete;
    ContextGuard& operator=(ContextGuard&&) = delete;

private:
    MachineContext* previous_;
};

} // namespace compat

} // namespace legends
