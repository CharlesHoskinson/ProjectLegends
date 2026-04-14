/**
 * @file machine_context.cpp
 * @brief Implementation of MachineContext and compatibility shim.
 *
 * @copyright GPL-2.0-or-later
 */

#include <aibox/machine_context.h>
#include <aibox/exceptions.h>
#include <gsl-lite/gsl-lite.hpp>

namespace aibox {

// ─────────────────────────────────────────────────────────────────────────────
// Compatibility Shim Implementation
// ─────────────────────────────────────────────────────────────────────────────

namespace {
    // Thread-local current context pointer
    thread_local MachineContext* g_current_context = nullptr;
}

namespace compat {

void set_current_context(MachineContext* ctx) noexcept {
    g_current_context = ctx;
}

MachineContext& current() {
    gsl_Assert(g_current_context != nullptr);
    return *g_current_context;
}

MachineContext* current_ptr() noexcept {
    return g_current_context;
}

bool has_context() noexcept {
    return g_current_context != nullptr;
}

// ContextGuard implementation
ContextGuard::ContextGuard(MachineContext& ctx) noexcept
    : previous_(g_current_context)
{
    g_current_context = &ctx;
}

ContextGuard::~ContextGuard() noexcept {
    g_current_context = previous_;
}

} // namespace compat

// ─────────────────────────────────────────────────────────────────────────────
// MachineContext Construction/Destruction
// ─────────────────────────────────────────────────────────────────────────────

MachineContext::MachineContext()
    : MachineContext(MachineConfig{})
{
}

MachineContext::MachineContext(const MachineConfig& config)
    : config_(config)
    , state_(MachineState::Created)
{
}

MachineContext::~MachineContext() {
    shutdown();
}

MachineContext::MachineContext(MachineContext&& other) noexcept
    : config_(std::move(other.config_))
    , state_(other.state_)
    , last_error_(std::move(other.last_error_))
    , total_cycles_(other.total_cycles_)
    , virtual_ticks_ms_(other.virtual_ticks_ms_)
    , stop_requested_(other.stop_requested_.load())
    , init_stage_(other.init_stage_)
    , cpu(std::move(other.cpu))
    , memory(std::move(other.memory))
    , dma(std::move(other.dma))
{
    other.state_ = MachineState::Destroyed;
    other.init_stage_ = InitStage::None;
}

MachineContext& MachineContext::operator=(MachineContext&& other) noexcept {
    if (this != &other) {
        shutdown();

        config_ = std::move(other.config_);
        state_ = other.state_;
        last_error_ = std::move(other.last_error_);
        total_cycles_ = other.total_cycles_;
        virtual_ticks_ms_ = other.virtual_ticks_ms_;
        stop_requested_.store(other.stop_requested_.load());
        init_stage_ = other.init_stage_;
        cpu = std::move(other.cpu);
        memory = std::move(other.memory);
        dma = std::move(other.dma);

        other.state_ = MachineState::Destroyed;
        other.init_stage_ = InitStage::None;
    }
    return *this;
}

// ─────────────────────────────────────────────────────────────────────────────
// Lifecycle Operations
// ─────────────────────────────────────────────────────────────────────────────

Result<void> MachineContext::initialize() {
    // Check precondition (REQ-GSE-040)
    if (state_ != MachineState::Created) {
        auto err = Error(ErrorCode::InvalidState,
            "Context already initialized or destroyed");
        set_error(err);
        return Err(std::move(err));
    }

    // Initialize in dependency order (REQ-GSE-003, REQ-GSE-010)
    auto result = init_memory();
    if (!result.has_value()) {
        cleanup_to_stage(InitStage::None);
        return result;
    }
    init_stage_ = InitStage::Memory;

    result = init_cpu();
    if (!result.has_value()) {
        cleanup_to_stage(InitStage::Memory);
        return result;
    }
    init_stage_ = InitStage::Cpu;

    result = init_dma();
    if (!result.has_value()) {
        cleanup_to_stage(InitStage::Cpu);
        return result;
    }
    init_stage_ = InitStage::Dma;

    init_stage_ = InitStage::Complete;

    state_ = MachineState::Initialized;
    return Ok();
}

void MachineContext::request_stop() noexcept {
    stop_requested_.store(true, std::memory_order_release);
}

Result<void> MachineContext::pause() {
    if (state_ != MachineState::Running) {
        auto err = Error(ErrorCode::InvalidState, "Not running");
        set_error(err);
        return Err(std::move(err));
    }
    state_ = MachineState::Paused;
    return Ok();
}

Result<void> MachineContext::resume() {
    if (state_ != MachineState::Paused) {
        auto err = Error(ErrorCode::InvalidState, "Not paused");
        set_error(err);
        return Err(std::move(err));
    }
    state_ = MachineState::Running;
    return Ok();
}

void MachineContext::shutdown() noexcept {
    // Idempotent - safe to call multiple times (REQ-GSE-041)
    if (state_ == MachineState::Shutdown ||
        state_ == MachineState::Destroyed) {
        return;
    }

    state_ = MachineState::Shutdown;

    // Cleanup in reverse order (REQ-GSE-011)
    cleanup_to_stage(InitStage::None);

    init_stage_ = InitStage::None;
}

Result<void> MachineContext::reset() {
    if (state_ == MachineState::Created) {
        auto err = Error(ErrorCode::InvalidState,
            "Cannot reset uninitialized context");
        set_error(err);
        return Err(std::move(err));
    }

    shutdown();
    state_ = MachineState::Created;
    total_cycles_ = 0;
    virtual_ticks_ms_ = 0;
    last_error_.reset();

    return initialize();
}

// ─────────────────────────────────────────────────────────────────────────────
// Cleanup Helper
// ─────────────────────────────────────────────────────────────────────────────

void MachineContext::cleanup_to_stage(InitStage target) noexcept {
    // Cleanup from current stage down to target (REQ-GSE-012, REQ-GSE-043)
    if (init_stage_ >= InitStage::Dma && target < InitStage::Dma) {
        dma.reset();
    }
    if (init_stage_ >= InitStage::Cpu && target < InitStage::Cpu) {
        cpu.reset();
    }
    if (init_stage_ >= InitStage::Memory && target < InitStage::Memory) {
        memory.reset();
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Subsystem Initialization
// ─────────────────────────────────────────────────────────────────────────────

Result<void> MachineContext::init_memory() {
    try {
        memory = std::make_unique<GuestMemory>(config_.memory_size);
        return Ok();
    } catch (const std::bad_alloc&) {
        auto err = Error(ErrorCode::OutOfMemory,
            "Failed to allocate guest memory");
        set_error(err);
        return Err(std::move(err));
    }
}

Result<void> MachineContext::init_cpu() {
    cpu.reset();
    cpu.config.cycles_per_ms = config_.cpu_cycles;
    return Ok();
}

Result<void> MachineContext::init_dma() {
    dma = std::make_unique<DmaSubsystem>();
    return Ok();
}

} // namespace aibox
