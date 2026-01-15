/**
 * @file test_dosbox_context.cpp
 * @brief Unit tests for DOSBoxContext.
 *
 * Tests PR #9 requirements:
 * - Master context struct with subsystem state
 * - Thread-local current_context()
 * - Integration with handle system
 */

#include <gtest/gtest.h>
#include "dosbox/dosbox_context.h"

using namespace dosbox;

// ═══════════════════════════════════════════════════════════════════════════════
// Configuration Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(ContextConfigTest, DefaultValues) {
    ContextConfig config;

    EXPECT_EQ(config.memory_size, 16u * 1024 * 1024);
    EXPECT_EQ(config.cpu_cycles, 3000u);
    EXPECT_FALSE(config.deterministic);
    EXPECT_TRUE(config.sound_enabled);
    EXPECT_FALSE(config.debug_mode);
}

TEST(ContextConfigTest, MinimalConfig) {
    auto config = ContextConfig::minimal();

    EXPECT_EQ(config.memory_size, 1024u * 1024);  // 1MB
    EXPECT_FALSE(config.sound_enabled);
    EXPECT_TRUE(config.deterministic);
}

// ═══════════════════════════════════════════════════════════════════════════════
// DOSBoxContext Basic Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(DOSBoxContextTest, Construction) {
    DOSBoxContext ctx;

    EXPECT_FALSE(ctx.is_initialized());
    EXPECT_FALSE(ctx.stop_requested());
}

TEST(DOSBoxContextTest, ConstructWithConfig) {
    ContextConfig config;
    config.cpu_cycles = 5000;
    config.sound_enabled = false;

    DOSBoxContext ctx(config);

    EXPECT_EQ(ctx.config().cpu_cycles, 5000u);
    EXPECT_FALSE(ctx.config().sound_enabled);
}

TEST(DOSBoxContextTest, Initialize) {
    DOSBoxContext ctx;

    auto result = ctx.initialize();
    ASSERT_TRUE(result.has_value());
    EXPECT_TRUE(ctx.is_initialized());
}

TEST(DOSBoxContextTest, DoubleInitializeFails) {
    DOSBoxContext ctx;

    EXPECT_TRUE(ctx.initialize().has_value());
    EXPECT_FALSE(ctx.initialize().has_value());  // Second init fails
}

TEST(DOSBoxContextTest, StepRequiresInit) {
    DOSBoxContext ctx;

    auto result = ctx.step(10);
    EXPECT_FALSE(result.has_value());  // Fails without init
}

TEST(DOSBoxContextTest, StepUpdatesState) {
    DOSBoxContext ctx;
    ctx.initialize();

    EXPECT_EQ(ctx.timing.virtual_ticks_ms, 0u);
    EXPECT_EQ(ctx.timing.total_cycles, 0u);

    auto result = ctx.step(10);
    ASSERT_TRUE(result.has_value());

    EXPECT_EQ(ctx.timing.virtual_ticks_ms, 10u);
    EXPECT_GT(ctx.timing.total_cycles, 0u);
}

TEST(DOSBoxContextTest, RequestStop) {
    DOSBoxContext ctx;
    ctx.initialize();

    EXPECT_FALSE(ctx.stop_requested());

    ctx.request_stop();
    EXPECT_TRUE(ctx.stop_requested());

    // Step should fail when stop requested
    auto result = ctx.step(10);
    EXPECT_FALSE(result.has_value());
}

TEST(DOSBoxContextTest, Shutdown) {
    DOSBoxContext ctx;
    ctx.initialize();

    EXPECT_TRUE(ctx.is_initialized());

    ctx.shutdown();
    EXPECT_FALSE(ctx.is_initialized());
}

TEST(DOSBoxContextTest, Reset) {
    DOSBoxContext ctx;
    ctx.initialize();
    ctx.step(100);

    EXPECT_GT(ctx.timing.virtual_ticks_ms, 0u);

    auto result = ctx.reset();
    ASSERT_TRUE(result.has_value());

    // State should be reset
    EXPECT_EQ(ctx.timing.virtual_ticks_ms, 0u);
    EXPECT_EQ(ctx.timing.total_cycles, 0u);

    // But still initialized
    EXPECT_TRUE(ctx.is_initialized());
}

// ═══════════════════════════════════════════════════════════════════════════════
// Handle-Based API Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(DOSBoxContextTest, CreateInstance) {
    auto result = create_instance();
    ASSERT_TRUE(result.has_value());

    auto [handle, ctx] = result.value();
    EXPECT_FALSE(handle.is_null());
    EXPECT_NE(ctx, nullptr);

    // Cleanup
    destroy_instance(handle);
}

TEST(DOSBoxContextTest, GetContextFromHandle) {
    auto result = create_instance();
    ASSERT_TRUE(result.has_value());

    auto [handle, ctx] = result.value();

    // Get context from handle
    DOSBoxContext* retrieved = get_context(handle);
    EXPECT_EQ(retrieved, ctx);

    // Cleanup
    destroy_instance(handle);
}

TEST(DOSBoxContextTest, GetContextInvalidHandle) {
    InstanceHandle invalid{0};

    DOSBoxContext* ctx = get_context(invalid);
    EXPECT_EQ(ctx, nullptr);
}

TEST(DOSBoxContextTest, DestroyInstance) {
    auto result = create_instance();
    ASSERT_TRUE(result.has_value());

    auto [handle, ctx] = result.value();

    auto destroy_result = destroy_instance(handle);
    EXPECT_TRUE(destroy_result.has_value());

    // Handle should now be invalid
    EXPECT_EQ(get_context(handle), nullptr);
}

TEST(DOSBoxContextTest, DoubleDestroyFails) {
    auto result = create_instance();
    ASSERT_TRUE(result.has_value());

    auto [handle, ctx] = result.value();

    EXPECT_TRUE(destroy_instance(handle).has_value());
    EXPECT_FALSE(destroy_instance(handle).has_value());  // Second destroy fails
}

// ═══════════════════════════════════════════════════════════════════════════════
// Thread-Local Context Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(DOSBoxContextTest, CurrentContextNotSet) {
    // Clear any previous context
    set_current_context(nullptr);

    EXPECT_FALSE(has_current_context());
    EXPECT_EQ(current_context_ptr(), nullptr);
}

TEST(DOSBoxContextTest, SetCurrentContext) {
    DOSBoxContext ctx;

    set_current_context(&ctx);

    EXPECT_TRUE(has_current_context());
    EXPECT_EQ(current_context_ptr(), &ctx);
    EXPECT_EQ(&current_context(), &ctx);

    // Cleanup
    set_current_context(nullptr);
}

TEST(DOSBoxContextTest, ContextGuardSetsContext) {
    DOSBoxContext ctx;

    EXPECT_FALSE(has_current_context());

    {
        ContextGuard guard(ctx);

        EXPECT_TRUE(has_current_context());
        EXPECT_EQ(&current_context(), &ctx);
    }

    // Context cleared after guard destroyed
    EXPECT_FALSE(has_current_context());
}

TEST(DOSBoxContextTest, ContextGuardRestoresPrevious) {
    DOSBoxContext ctx1;
    DOSBoxContext ctx2;

    set_current_context(&ctx1);

    {
        ContextGuard guard(ctx2);
        EXPECT_EQ(&current_context(), &ctx2);
    }

    // Previous context restored
    EXPECT_EQ(&current_context(), &ctx1);

    // Cleanup
    set_current_context(nullptr);
}

TEST(DOSBoxContextTest, ContextGuardFromHandle) {
    auto result = create_instance();
    ASSERT_TRUE(result.has_value());

    auto [handle, ctx] = result.value();
    ctx->initialize();

    {
        ContextGuard guard(handle);
        EXPECT_TRUE(guard.valid());
        EXPECT_EQ(&current_context(), ctx);
    }

    // Cleanup
    destroy_instance(handle);
}

TEST(DOSBoxContextTest, NestedContextGuards) {
    DOSBoxContext ctx1;
    DOSBoxContext ctx2;
    DOSBoxContext ctx3;

    {
        ContextGuard guard1(ctx1);
        EXPECT_EQ(&current_context(), &ctx1);

        {
            ContextGuard guard2(ctx2);
            EXPECT_EQ(&current_context(), &ctx2);

            {
                ContextGuard guard3(ctx3);
                EXPECT_EQ(&current_context(), &ctx3);
            }

            EXPECT_EQ(&current_context(), &ctx2);
        }

        EXPECT_EQ(&current_context(), &ctx1);
    }

    EXPECT_FALSE(has_current_context());
}

// ═══════════════════════════════════════════════════════════════════════════════
// Subsystem State Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(DOSBoxContextTest, TimingStateReset) {
    TimingState timing;
    timing.total_cycles = 1000;
    timing.virtual_ticks_ms = 100;

    timing.reset();

    EXPECT_EQ(timing.total_cycles, 0u);
    EXPECT_EQ(timing.virtual_ticks_ms, 0u);
}

TEST(DOSBoxContextTest, CpuStateReset) {
    CpuState cpu;
    cpu.cycles = 5000;
    cpu.halted = true;

    cpu.reset();

    EXPECT_EQ(cpu.cycles, 0u);
    EXPECT_FALSE(cpu.halted);
}

TEST(DOSBoxContextTest, MixerStateReset) {
    MixerState mixer;
    mixer.enabled = true;
    mixer.sample_rate = 48000;

    mixer.reset();

    EXPECT_FALSE(mixer.enabled);
    EXPECT_EQ(mixer.sample_rate, 44100u);
}

TEST(DOSBoxContextTest, VgaStateReset) {
    VgaState vga;
    vga.width = 320;
    vga.height = 200;
    vga.bpp = 16;

    vga.reset();

    EXPECT_EQ(vga.width, 640);
    EXPECT_EQ(vga.height, 480);
    EXPECT_EQ(vga.bpp, 8);
}

// ═══════════════════════════════════════════════════════════════════════════════
// C API Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(DOSBoxContextCApiTest, ConfigInit) {
    dosbox_config config;
    dosbox_config_init(&config);

    EXPECT_EQ(config.memory_size, 16u * 1024 * 1024);
    EXPECT_EQ(config.cpu_cycles, 3000u);
    EXPECT_EQ(config.sound_enabled, 1);
}

TEST(DOSBoxContextCApiTest, CreateAndDestroy) {
    dosbox_handle_t handle = dosbox_create(nullptr);
    EXPECT_NE(handle, nullptr);

    int result = dosbox_destroy(handle);
    EXPECT_EQ(result, DOSBOX_OK);
}

TEST(DOSBoxContextCApiTest, FullLifecycle) {
    // Create
    dosbox_handle_t handle = dosbox_create(nullptr);
    ASSERT_NE(handle, nullptr);

    // Initialize
    int result = dosbox_init(handle);
    EXPECT_EQ(result, DOSBOX_OK);

    // Step
    result = dosbox_step(handle, 10);
    EXPECT_EQ(result, DOSBOX_OK);

    // Pause
    result = dosbox_pause(handle);
    EXPECT_EQ(result, DOSBOX_OK);

    // Resume
    result = dosbox_resume(handle);
    EXPECT_EQ(result, DOSBOX_OK);

    // Shutdown
    result = dosbox_shutdown(handle);
    EXPECT_EQ(result, DOSBOX_OK);

    // Destroy
    result = dosbox_destroy(handle);
    EXPECT_EQ(result, DOSBOX_OK);
}

TEST(DOSBoxContextCApiTest, NullHandleReturnsError) {
    EXPECT_NE(dosbox_init(nullptr), DOSBOX_OK);
    EXPECT_NE(dosbox_step(nullptr, 10), DOSBOX_OK);
    EXPECT_NE(dosbox_destroy(nullptr), DOSBOX_OK);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Move Semantics Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(DOSBoxContextTest, MoveConstruction) {
    DOSBoxContext ctx1;
    ctx1.initialize();
    ctx1.step(50);

    uint64_t cycles_before = ctx1.timing.total_cycles;

    DOSBoxContext ctx2(std::move(ctx1));

    // ctx2 should have the state
    EXPECT_TRUE(ctx2.is_initialized());
    EXPECT_EQ(ctx2.timing.total_cycles, cycles_before);

    // ctx1 should be uninitialized
    EXPECT_FALSE(ctx1.is_initialized());
}

TEST(DOSBoxContextTest, MoveAssignment) {
    DOSBoxContext ctx1;
    ctx1.initialize();
    ctx1.step(50);

    DOSBoxContext ctx2;

    ctx2 = std::move(ctx1);

    EXPECT_TRUE(ctx2.is_initialized());
    EXPECT_FALSE(ctx1.is_initialized());
}
