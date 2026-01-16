/**
 * @file dosbox_context.cpp
 * @brief Implementation of DOSBox context for library mode.
 *
 * @copyright GPL-2.0-or-later
 */

#include "dosbox/dosbox_context.h"
#include "dosbox/safe_call.h"
#include "dosbox/state_hash.h"
#include "aibox/headless_stub.h"

#include <cassert>
#include <stdexcept>
#include <unordered_map>

// ═══════════════════════════════════════════════════════════════════════════════
// Thread-Local Context Storage
// ═══════════════════════════════════════════════════════════════════════════════

namespace {

thread_local dosbox::DOSBoxContext* g_current_context = nullptr;

// Context storage (owns the contexts)
std::mutex g_contexts_mutex;
std::unordered_map<uint32_t, std::unique_ptr<dosbox::DOSBoxContext>> g_contexts;

} // anonymous namespace

// ═══════════════════════════════════════════════════════════════════════════════
// TimingState Implementation
// ═══════════════════════════════════════════════════════════════════════════════

namespace dosbox {

void TimingState::hash_into(HashBuilder& builder) const {
    // Hash determinism-relevant timing state
    // Note: We explicitly do NOT hash wall-clock values (sdl_ticks_*, ticks_last_rt, etc.)
    // as those would make hashes non-deterministic across runs.

    // Core timing counters
    builder.update(total_cycles);
    builder.update(virtual_ticks_ms);

    // Frame timing (determinism-relevant)
    builder.update(ticks_done);
    builder.update(ticks_scheduled);
    builder.update(ticks_remain);
    builder.update(ticks_added);

    // Control state
    builder.update(locked);
    builder.update(frame_ticks);
}

// ═══════════════════════════════════════════════════════════════════════════════
// CpuState Implementation
// ═══════════════════════════════════════════════════════════════════════════════

void CpuState::hash_into(HashBuilder& builder) const {
    // Hash all CPU cycle state - all fields are determinism-relevant

    // Cycle counters
    builder.update(cycles);
    builder.update(cycle_left);
    builder.update(cycle_max);
    builder.update(cycle_old_max);
    builder.update(cycle_percent_used);
    builder.update(cycle_limit);
    builder.update(cycle_up);
    builder.update(cycle_down);
    builder.update(cycles_set);
    builder.update(io_delay_removed);

    // Auto-adjustment flags
    builder.update(cycle_auto_adjust);
    builder.update(skip_cycle_auto_adjust);

    // NMI state
    builder.update(nmi_gate);
    builder.update(nmi_active);
    builder.update(nmi_pending);

    // Flags and state
    builder.update(extflags_toggle);
    builder.update(halted);
}

// ═══════════════════════════════════════════════════════════════════════════════
// MixerState Implementation
// ═══════════════════════════════════════════════════════════════════════════════

void MixerState::hash_into(HashBuilder& builder) const {
    // Hash determinism-relevant mixer state
    // Note: We do NOT hash start_pic_time as it's wall-clock dependent

    // Core configuration
    builder.update(freq);
    builder.update(blocksize);

    // Volume state (affects output)
    builder.update(mastervol[0]);
    builder.update(mastervol[1]);
    builder.update(recordvol[0]);
    builder.update(recordvol[1]);

    // Ring buffer state (critical for determinism)
    builder.update(work_in);
    builder.update(work_out);
    builder.update(work_wrap);
    builder.update(pos);
    builder.update(done);

    // Fractional sample tracking
    builder.update(samples_per_ms.whole);
    builder.update(samples_per_ms.numerator);
    builder.update(samples_per_ms.denominator);
    builder.update(samples_this_ms.whole);
    builder.update(samples_this_ms.numerator);
    builder.update(samples_this_ms.denominator);
    builder.update(samples_rendered.whole);
    builder.update(samples_rendered.numerator);
    builder.update(samples_rendered.denominator);

    // Configuration flags
    builder.update(enabled);
    builder.update(nosound);
    builder.update(swapstereo);
    builder.update(sampleaccurate);
    builder.update(prebuffer_wait);
    builder.update(mute);

    // Prebuffer state
    builder.update(prebuffer_samples);

    // Statistics (sample_counter is determinism-relevant)
    builder.update(sample_counter);
    // Note: start_pic_time excluded (wall-clock dependent)
}

// ═══════════════════════════════════════════════════════════════════════════════
// VgaState Implementation
// ═══════════════════════════════════════════════════════════════════════════════

void VgaState::hash_into(HashBuilder& builder) const {
    // Hash determinism-relevant VGA state
    // Note: We do NOT hash fps as it's derived from timing

    // Display mode configuration
    builder.update(width);
    builder.update(height);
    builder.update(bpp);
    builder.update(static_cast<uint8_t>(mode));
    builder.update(static_cast<uint8_t>(svga_chip));

    // Timing (refresh_rate is config, frame_counter is determinism-relevant)
    builder.update(refresh_rate);
    builder.update(frame_counter);
    // Note: fps excluded (derived from timing, may vary)

    // Rendering flags
    builder.update(render_on_demand);
    builder.update(render_wait_for_changes);

    // Hardware configuration
    builder.update(dac_8bit);
    builder.update(pci_enabled);
    builder.update(vbe_enabled);

    // VESA capabilities (config, affects available modes)
    builder.update(vesa_32bpp);
    builder.update(vesa_24bpp);
    builder.update(vesa_16bpp);
    builder.update(vesa_15bpp);
    builder.update(vesa_8bpp);
    builder.update(vesa_4bpp);
    builder.update(vesa_lowres);
    builder.update(vesa_hd);

    // Display state flags
    builder.update(text_mode);
    builder.update(page_flip_occurred);
    builder.update(retrace_poll);

    // CGA/EGA compatibility
    builder.update(cga_snow);
    builder.update(ega_mode);
}

// ═══════════════════════════════════════════════════════════════════════════════
// PicState Implementation
// ═══════════════════════════════════════════════════════════════════════════════

void PicState::hash_into(HashBuilder& builder) const {
    // All PIC state is determinism-relevant

    // Tick counter
    builder.update(ticks);

    // IRQ state
    builder.update(irq_check);
    builder.update(irq_check_pending);

    // Cascade configuration
    builder.update(master_cascade_irq);

    // Event service state
    builder.update(in_event_service);
    builder.update(srv_lag);

    // IRQ timing
    builder.update(irq_delay_ns);

    // Controller state
    builder.update(master_imr);
    builder.update(slave_imr);
    builder.update(master_isr);
    builder.update(slave_isr);
    builder.update(auto_eoi);
}

// ═══════════════════════════════════════════════════════════════════════════════
// KeyboardState Implementation
// ═══════════════════════════════════════════════════════════════════════════════

void KeyboardState::hash_into(HashBuilder& builder) const {
    // All keyboard state is determinism-relevant

    // Scan code state
    builder.update(scanset);
    builder.update(enabled);
    builder.update(active);

    // Buffer state
    builder.update(buffer_size);
    builder.update(buffer_pos);

    // Lock state
    builder.update(num_lock);
    builder.update(caps_lock);
    builder.update(scroll_lock);

    // Command state
    builder.update(command);
    builder.update(expecting_data);

    // PS/2 controller state
    builder.update(ps2_mouse_enabled);
    builder.update(a20_gate);
}

// ═══════════════════════════════════════════════════════════════════════════════
// InputCaptureState Implementation
// ═══════════════════════════════════════════════════════════════════════════════

void InputCaptureState::hash_into(HashBuilder& builder) const {
    // Input capture state affects determinism when replaying
    builder.update(captured_num_lock);
    builder.update(captured_caps_lock);
    builder.update(input_captured);
}

} // namespace dosbox

// ═══════════════════════════════════════════════════════════════════════════════
// C API Implementation
// ═══════════════════════════════════════════════════════════════════════════════

extern "C" {

void dosbox_config_init(dosbox_config* config) {
    if (!config) return;

    config->memory_size = 16 * 1024 * 1024;  // 16MB
    config->cpu_cycles = 3000;
    config->deterministic = 0;
    config->sound_enabled = 1;
    config->debug_mode = 0;
}

dosbox_handle_t dosbox_create(const dosbox_config* config) {
    dosbox::ContextConfig cpp_config;

    if (config) {
        cpp_config.memory_size = config->memory_size;
        cpp_config.cpu_cycles = config->cpu_cycles;
        cpp_config.deterministic = config->deterministic != 0;
        cpp_config.sound_enabled = config->sound_enabled != 0;
        cpp_config.debug_mode = config->debug_mode != 0;
    }

    auto result = dosbox::create_instance(cpp_config);
    if (!result.has_value()) {
        return nullptr;
    }

    return result.value().first.to_opaque();
}

int dosbox_init(dosbox_handle_t handle) {
    auto* ctx = dosbox::get_context(dosbox::InstanceHandle::from_opaque(handle));
    if (!ctx) {
        return DOSBOX_ERR_INVALID_ARGUMENT;
    }

    auto result = ctx->initialize();
    if (!result.has_value()) {
        return static_cast<int>(result.error().code());
    }

    // Transition to Initialized state
    auto& registry = dosbox::get_instance_registry();
    auto h = dosbox::InstanceHandle::from_opaque(handle);
    registry.transition(h, dosbox::InstanceState::Initialized);

    return DOSBOX_OK;
}

int dosbox_step(dosbox_handle_t handle, uint32_t ms) {
    auto h = dosbox::InstanceHandle::from_opaque(handle);
    auto* ctx = dosbox::get_context(h);
    if (!ctx) {
        return DOSBOX_ERR_INVALID_ARGUMENT;
    }

    auto& registry = dosbox::get_instance_registry();

    // Check state allows running
    auto state = registry.get_state(h);
    if (!state || (state.value() != dosbox::InstanceState::Initialized &&
                   state.value() != dosbox::InstanceState::Running &&
                   state.value() != dosbox::InstanceState::Paused)) {
        return DOSBOX_ERR_INVALID_STATE;
    }

    // Transition to Running if not already
    if (state.value() != dosbox::InstanceState::Running) {
        registry.transition(h, dosbox::InstanceState::Running);
    }

    // Set current context for transitional code
    dosbox::ContextGuard guard(*ctx);

    auto result = ctx->step(ms);
    if (!result.has_value()) {
        return static_cast<int>(result.error().code());
    }

    return DOSBOX_OK;
}

int dosbox_pause(dosbox_handle_t handle) {
    auto h = dosbox::InstanceHandle::from_opaque(handle);
    auto& registry = dosbox::get_instance_registry();

    auto transition = registry.transition(h, dosbox::InstanceState::Paused);
    if (!transition.has_value()) {
        return DOSBOX_ERR_INVALID_STATE;
    }

    auto* ctx = dosbox::get_context(h);
    if (ctx) {
        ctx->pause();
    }

    return DOSBOX_OK;
}

int dosbox_resume(dosbox_handle_t handle) {
    auto h = dosbox::InstanceHandle::from_opaque(handle);
    auto& registry = dosbox::get_instance_registry();

    auto transition = registry.transition(h, dosbox::InstanceState::Running);
    if (!transition.has_value()) {
        return DOSBOX_ERR_INVALID_STATE;
    }

    auto* ctx = dosbox::get_context(h);
    if (ctx) {
        ctx->resume();
    }

    return DOSBOX_OK;
}

int dosbox_shutdown(dosbox_handle_t handle) {
    auto h = dosbox::InstanceHandle::from_opaque(handle);
    auto& registry = dosbox::get_instance_registry();

    auto transition = registry.transition(h, dosbox::InstanceState::Shutdown);
    if (!transition.has_value()) {
        return DOSBOX_ERR_INVALID_STATE;
    }

    auto* ctx = dosbox::get_context(h);
    if (ctx) {
        ctx->shutdown();
    }

    return DOSBOX_OK;
}

int dosbox_destroy(dosbox_handle_t handle) {
    auto h = dosbox::InstanceHandle::from_opaque(handle);

    auto result = dosbox::destroy_instance(h);
    if (!result.has_value()) {
        return static_cast<int>(result.error().code());
    }

    return DOSBOX_OK;
}

int dosbox_reset(dosbox_handle_t handle) {
    auto h = dosbox::InstanceHandle::from_opaque(handle);
    auto* ctx = dosbox::get_context(h);
    if (!ctx) {
        return DOSBOX_ERR_INVALID_ARGUMENT;
    }

    auto result = ctx->reset();
    if (!result.has_value()) {
        return static_cast<int>(result.error().code());
    }

    return DOSBOX_OK;
}

} // extern "C"

// ═══════════════════════════════════════════════════════════════════════════════
// C++ Implementation
// ═══════════════════════════════════════════════════════════════════════════════

namespace dosbox {

// ─────────────────────────────────────────────────────────────────────────────
// DOSBoxContext Implementation
// ─────────────────────────────────────────────────────────────────────────────

DOSBoxContext::DOSBoxContext(const ContextConfig& config)
    : config_(config)
    , initialized_(false)
    , stop_requested_(false)
{}

DOSBoxContext::~DOSBoxContext() {
    if (initialized_) {
        shutdown();
    }
}

DOSBoxContext::DOSBoxContext(DOSBoxContext&& other) noexcept
    : config_(std::move(other.config_))
    , initialized_(other.initialized_)
    , stop_requested_(other.stop_requested_.load())
    , last_error_(std::move(other.last_error_))
    , timing(std::move(other.timing))
    , cpu_state(std::move(other.cpu_state))
    , mixer(std::move(other.mixer))
    , vga(std::move(other.vga))
    , pic(std::move(other.pic))
    , keyboard(std::move(other.keyboard))
    , input(std::move(other.input))
{
    other.initialized_ = false;
}

DOSBoxContext& DOSBoxContext::operator=(DOSBoxContext&& other) noexcept {
    if (this != &other) {
        if (initialized_) {
            shutdown();
        }

        config_ = std::move(other.config_);
        initialized_ = other.initialized_;
        stop_requested_ = other.stop_requested_.load();
        last_error_ = std::move(other.last_error_);
        timing = std::move(other.timing);
        cpu_state = std::move(other.cpu_state);
        mixer = std::move(other.mixer);
        vga = std::move(other.vga);
        pic = std::move(other.pic);
        keyboard = std::move(other.keyboard);
        input = std::move(other.input);

        other.initialized_ = false;
    }
    return *this;
}

Result<void> DOSBoxContext::initialize() {
    if (initialized_) {
        return Err(Error(ErrorCode::InvalidState, "Already initialized"));
    }

    // Initialize subsystem state
    timing.reset();
    cpu_state.reset();
    mixer.reset();
    vga.reset();
    pic.reset();
    keyboard.reset();
    input.reset();

    // Apply configuration
    cpu_state.cycle_limit = config_.cpu_cycles;
    mixer.enabled = config_.sound_enabled;

    // TODO: In future PRs, this will initialize actual DOSBox subsystems
    // For now, we just set the initialized flag

    initialized_ = true;
    stop_requested_ = false;

    return Ok();
}

Result<uint32_t> DOSBoxContext::step(uint32_t ms) {
    if (!initialized_) {
        return Err(Error(ErrorCode::InvalidState, "Not initialized"));
    }

    if (stop_requested_.load(std::memory_order_acquire)) {
        return Err(Error(ErrorCode::InvalidState, "Stop requested"));
    }

    // Calculate cycles for this step
    uint32_t cycles = ms * config_.cpu_cycles;

    // TODO: In future PRs, this will execute actual CPU cycles
    // For now, just update timing state

    timing.total_cycles += cycles;
    timing.virtual_ticks_ms += ms;
    cpu_state.cycles += cycles;

    return Ok(cycles);
}

Result<void> DOSBoxContext::pause() {
    if (!initialized_) {
        return Err(Error(ErrorCode::InvalidState, "Not initialized"));
    }
    // Pause is handled by state machine in registry
    return Ok();
}

Result<void> DOSBoxContext::resume() {
    if (!initialized_) {
        return Err(Error(ErrorCode::InvalidState, "Not initialized"));
    }
    // Resume is handled by state machine in registry
    return Ok();
}

void DOSBoxContext::shutdown() noexcept {
    if (!initialized_) {
        return;
    }

    // Reset all subsystem state
    timing.reset();
    cpu_state.reset();
    mixer.reset();
    vga.reset();
    pic.reset();
    keyboard.reset();
    input.reset();

    initialized_ = false;
    stop_requested_ = true;
}

Result<void> DOSBoxContext::reset() {
    if (!initialized_) {
        return Err(Error(ErrorCode::InvalidState, "Not initialized"));
    }

    // Reset subsystem state
    timing.reset();
    cpu_state.reset();
    mixer.reset();
    vga.reset();
    pic.reset();
    keyboard.reset();
    input.reset();

    // Reapply configuration
    cpu_state.cycle_limit = config_.cpu_cycles;
    mixer.enabled = config_.sound_enabled;

    stop_requested_ = false;

    return Ok();
}

void DOSBoxContext::request_stop() noexcept {
    stop_requested_.store(true, std::memory_order_release);
}

void DOSBoxContext::set_timing_provider(platform::ITiming* timing) noexcept {
    timing_provider_ = timing;

    // If this is the current context, update the headless stub immediately
    if (g_current_context == this) {
        auto* provider = timing ? timing : &virtual_timing_;
        aibox::headless::SetTimingProvider(provider);
    }
}

void DOSBoxContext::set_display_provider(platform::IDisplay* display) noexcept {
    display_provider_ = display;

    // If this is the current context, update the headless stub immediately
    if (g_current_context == this) {
        auto* provider = display ? display : &headless_display_;
        aibox::headless::SetDisplayProvider(provider);
    }
}

void DOSBoxContext::set_input_provider(platform::IInput* input) noexcept {
    input_provider_ = input;

    // If this is the current context, update the headless stub immediately
    if (g_current_context == this) {
        auto* provider = input ? input : &thread_safe_input_;
        aibox::headless::SetInputProvider(provider);
    }
}

void DOSBoxContext::set_audio_provider(platform::IAudio* audio) noexcept {
    audio_provider_ = audio;

    // If this is the current context, update the headless stub immediately
    if (g_current_context == this) {
        auto* provider = audio ? audio : &buffer_audio_;
        aibox::headless::SetAudioProvider(provider);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Handle-Based API Implementation
// ─────────────────────────────────────────────────────────────────────────────

Result<std::pair<InstanceHandle, DOSBoxContext*>> create_instance(const ContextConfig& config) {
    auto& registry = get_instance_registry();

    // Create context
    auto context = std::make_unique<DOSBoxContext>(config);
    DOSBoxContext* ctx_ptr = context.get();

    // Allocate handle
    auto handle_result = registry.allocate(ctx_ptr);
    if (!handle_result.has_value()) {
        return Err(handle_result.error());
    }

    InstanceHandle handle = handle_result.value();

    // Store context
    {
        std::lock_guard lock(g_contexts_mutex);
        g_contexts[handle.value] = std::move(context);
    }

    return Ok(std::make_pair(handle, ctx_ptr));
}

DOSBoxContext* get_context(InstanceHandle handle) {
    auto& registry = get_instance_registry();

    if (registry.validate(handle) != HandleError::Ok) {
        return nullptr;
    }

    auto ctx_opt = registry.get_context(handle);
    if (!ctx_opt) {
        return nullptr;
    }

    return static_cast<DOSBoxContext*>(ctx_opt.value());
}

Result<void> destroy_instance(InstanceHandle handle) {
    auto& registry = get_instance_registry();

    // Validate handle
    if (registry.validate(handle) != HandleError::Ok) {
        return Err(Error(ErrorCode::InvalidHandle, "Invalid handle"));
    }

    // Get state and check if we can destroy
    auto state = registry.get_state(handle);
    if (state && state.value() != InstanceState::Shutdown &&
        state.value() != InstanceState::Failed &&
        state.value() != InstanceState::Created) {
        // Must shutdown first
        registry.transition(handle, InstanceState::Shutdown);
    }

    // Remove context from storage
    {
        std::lock_guard lock(g_contexts_mutex);
        g_contexts.erase(handle.value);
    }

    // Destroy handle in registry
    return registry.destroy(handle);
}

// ─────────────────────────────────────────────────────────────────────────────
// Thread-Local Context Implementation
// ─────────────────────────────────────────────────────────────────────────────

void set_current_context(DOSBoxContext* ctx) noexcept {
    g_current_context = ctx;

    // Wire up platform providers
    if (ctx) {
        // Wire up timing provider (PR #17)
        auto* timing = ctx->get_timing_provider();
        if (!timing) {
            // Use built-in virtual timing if no custom provider
            timing = &ctx->virtual_timing();
        }
        aibox::headless::SetTimingProvider(timing);

        // Wire up display provider (PR #18)
        auto* display = ctx->get_display_provider();
        if (!display) {
            // Use built-in headless display if no custom provider
            display = &ctx->headless_display();
        }
        aibox::headless::SetDisplayProvider(display);

        // Wire up input provider (PR #19)
        auto* input = ctx->get_input_provider();
        if (!input) {
            // Use built-in thread-safe input if no custom provider
            input = &ctx->thread_safe_input();
        }
        aibox::headless::SetInputProvider(input);

        // Wire up audio provider (PR #20)
        auto* audio = ctx->get_audio_provider();
        if (!audio) {
            // Use built-in buffer audio if no custom provider
            audio = &ctx->buffer_audio();
        }
        aibox::headless::SetAudioProvider(audio);
    } else {
        aibox::headless::SetTimingProvider(nullptr);
        aibox::headless::SetDisplayProvider(nullptr);
        aibox::headless::SetInputProvider(nullptr);
        aibox::headless::SetAudioProvider(nullptr);
    }
}

DOSBoxContext& current_context() {
    assert(g_current_context != nullptr && "No current context set");
    if (!g_current_context) {
        // In release mode, this is undefined behavior
        // But we try to fail gracefully
        throw std::runtime_error("No current DOSBox context set");
    }
    return *g_current_context;
}

DOSBoxContext* current_context_ptr() noexcept {
    return g_current_context;
}

bool has_current_context() noexcept {
    return g_current_context != nullptr;
}

// ─────────────────────────────────────────────────────────────────────────────
// ContextGuard Implementation
// ─────────────────────────────────────────────────────────────────────────────

ContextGuard::ContextGuard(DOSBoxContext& ctx) noexcept
    : previous_(g_current_context)
    , valid_(true)
{
    set_current_context(&ctx);
}

ContextGuard::ContextGuard(InstanceHandle handle)
    : previous_(g_current_context)
    , valid_(false)
{
    DOSBoxContext* ctx = get_context(handle);
    if (!ctx) {
        throw std::runtime_error("Invalid handle for ContextGuard");
    }
    set_current_context(ctx);
    valid_ = true;
}

ContextGuard::~ContextGuard() noexcept {
    set_current_context(previous_);
}

} // namespace dosbox
