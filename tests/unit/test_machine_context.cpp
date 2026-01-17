/**
 * @file test_machine_context.cpp
 * @brief Unit tests for MachineContext class.
 */

#ifdef _MSC_VER
#pragma warning(disable: 4834) // discarding return value of [[nodiscard]] function
#endif

#include <gtest/gtest.h>
#include <legends/machine_context.h>

using namespace legends;

// ─────────────────────────────────────────────────────────────────────────────
// Test Fixture
// ─────────────────────────────────────────────────────────────────────────────

class MachineContextTest : public ::testing::Test {
protected:
    MachineConfig config_;

    void SetUp() override {
        config_ = MachineConfig::minimal();
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// MachineConfig Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(MachineConfigTest, DefaultValues) {
    MachineConfig config;

    EXPECT_EQ(config.memory_size, 16u * 1024 * 1024);
    EXPECT_EQ(config.vga_memory, 256u * 1024);
    EXPECT_EQ(config.cpu_cycles, 3000u);
    EXPECT_FALSE(config.cpu_dynamic_core);
    EXPECT_EQ(config.machine_type, MachineType::VGA);
    EXPECT_FALSE(config.deterministic);
    EXPECT_TRUE(config.sound_enabled);
    EXPECT_FALSE(config.debug_mode);
}

TEST(MachineConfigTest, MinimalConfig) {
    MachineConfig config = MachineConfig::minimal();

    EXPECT_EQ(config.memory_size, 1024u * 1024);  // 1MB
    EXPECT_EQ(config.vga_memory, 64u * 1024);     // 64KB
    EXPECT_FALSE(config.sound_enabled);
    EXPECT_TRUE(config.deterministic);
}

TEST(MachineConfigTest, VgaDefaultConfig) {
    MachineConfig config = MachineConfig::vga_default();

    EXPECT_EQ(config.machine_type, MachineType::VGA);
    EXPECT_EQ(config.memory_size, 16u * 1024 * 1024);
}

// ─────────────────────────────────────────────────────────────────────────────
// MachineState Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(MachineStateTest, ToStringConverts) {
    EXPECT_STREQ(to_string(MachineState::Created), "Created");
    EXPECT_STREQ(to_string(MachineState::Initialized), "Initialized");
    EXPECT_STREQ(to_string(MachineState::Running), "Running");
    EXPECT_STREQ(to_string(MachineState::Paused), "Paused");
    EXPECT_STREQ(to_string(MachineState::Stopped), "Stopped");
    EXPECT_STREQ(to_string(MachineState::Shutdown), "Shutdown");
    EXPECT_STREQ(to_string(MachineState::Destroyed), "Destroyed");
}

// ─────────────────────────────────────────────────────────────────────────────
// Construction Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(MachineContextTest, ConstructionSetsCreatedState) {
    MachineContext ctx(config_);
    EXPECT_EQ(ctx.state(), MachineState::Created);
}

TEST_F(MachineContextTest, DefaultConstructorWorks) {
    MachineContext ctx;
    EXPECT_EQ(ctx.state(), MachineState::Created);
}

TEST_F(MachineContextTest, ConstructionDoesNotInitialize) {
    MachineContext ctx(config_);

    EXPECT_FALSE(ctx.is_initialized());
    EXPECT_EQ(ctx.memory, nullptr);
    EXPECT_EQ(ctx.dma, nullptr);
}

TEST_F(MachineContextTest, ConfigIsStored) {
    config_.memory_size = 4 * 1024 * 1024;
    config_.cpu_cycles = 5000;

    MachineContext ctx(config_);

    EXPECT_EQ(ctx.config().memory_size, 4u * 1024 * 1024);
    EXPECT_EQ(ctx.config().cpu_cycles, 5000u);
}

// ─────────────────────────────────────────────────────────────────────────────
// Initialization Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(MachineContextTest, InitializeSucceeds) {
    MachineContext ctx(config_);

    auto result = ctx.initialize();

    EXPECT_TRUE(result.has_value());
    EXPECT_EQ(ctx.state(), MachineState::Initialized);
}

TEST_F(MachineContextTest, InitializeAllocatesMemory) {
    MachineContext ctx(config_);
    ctx.initialize();

    EXPECT_NE(ctx.memory, nullptr);
    EXPECT_EQ(ctx.memory->size(), config_.memory_size);
}

TEST_F(MachineContextTest, InitializeCreatesDma) {
    MachineContext ctx(config_);
    ctx.initialize();

    EXPECT_NE(ctx.dma, nullptr);
}

TEST_F(MachineContextTest, InitializeResetsCpu) {
    MachineContext ctx(config_);
    ctx.cpu.eax = 0x12345678;

    ctx.initialize();

    EXPECT_EQ(ctx.cpu.eax, 0u);
    EXPECT_EQ(ctx.cpu.eip, 0xFFF0u);  // Reset vector
}

TEST_F(MachineContextTest, DoubleInitializeReturnsError) {
    MachineContext ctx(config_);
    ctx.initialize();

    auto result = ctx.initialize();

    EXPECT_FALSE(result.has_value());
    EXPECT_EQ(result.error().code(), ErrorCode::InvalidState);
}

TEST_F(MachineContextTest, IsInitializedAfterInit) {
    MachineContext ctx(config_);

    EXPECT_FALSE(ctx.is_initialized());

    ctx.initialize();

    EXPECT_TRUE(ctx.is_initialized());
}

// ─────────────────────────────────────────────────────────────────────────────
// Step/Run Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(MachineContextTest, StepRequiresInitialization) {
    MachineContext ctx(config_);

    auto result = ctx.step(10);

    EXPECT_FALSE(result.has_value());
    EXPECT_EQ(result.error().code(), ErrorCode::InvalidState);
}

TEST_F(MachineContextTest, StepSucceedsAfterInit) {
    MachineContext ctx(config_);
    ctx.initialize();

    auto result = ctx.step(10);

    EXPECT_TRUE(result.has_value());
}

TEST_F(MachineContextTest, StepReturnsStepCount) {
    MachineContext ctx(config_);
    ctx.initialize();

    auto result = ctx.step(10);

    EXPECT_TRUE(result.has_value());
    EXPECT_EQ(result.value(), 10u);
}

TEST_F(MachineContextTest, StepUpdatesVirtualTicks) {
    MachineContext ctx(config_);
    ctx.initialize();

    EXPECT_EQ(ctx.virtual_ticks(), 0u);

    ctx.step(5);
    EXPECT_EQ(ctx.virtual_ticks(), 5u);

    ctx.step(10);
    EXPECT_EQ(ctx.virtual_ticks(), 15u);
}

TEST_F(MachineContextTest, StepUpdatesTotalCycles) {
    MachineContext ctx(config_);
    ctx.initialize();

    EXPECT_EQ(ctx.total_cycles(), 0u);

    ctx.step(10);

    EXPECT_GT(ctx.total_cycles(), 0u);
}

TEST_F(MachineContextTest, StepSetsRunningState) {
    MachineContext ctx(config_);
    ctx.initialize();

    ctx.step(1);

    // After step completes (without stop), state may be Running
    EXPECT_TRUE(ctx.state() == MachineState::Running ||
                ctx.state() == MachineState::Initialized);
}

TEST_F(MachineContextTest, RequestStopStopsExecution) {
    MachineContext ctx(config_);
    ctx.initialize();

    ctx.request_stop();
    ctx.step(1000);

    EXPECT_EQ(ctx.state(), MachineState::Stopped);
}

TEST_F(MachineContextTest, StopRequestedQueryWorks) {
    MachineContext ctx(config_);

    EXPECT_FALSE(ctx.stop_requested());

    ctx.request_stop();

    EXPECT_TRUE(ctx.stop_requested());
}

// ─────────────────────────────────────────────────────────────────────────────
// Pause/Resume Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(MachineContextTest, PauseRequiresRunning) {
    MachineContext ctx(config_);
    ctx.initialize();

    // Not running yet
    auto result = ctx.pause();

    EXPECT_FALSE(result.has_value());
    EXPECT_EQ(result.error().code(), ErrorCode::InvalidState);
}

TEST_F(MachineContextTest, ResumeRequiresPaused) {
    MachineContext ctx(config_);
    ctx.initialize();

    auto result = ctx.resume();

    EXPECT_FALSE(result.has_value());
    EXPECT_EQ(result.error().code(), ErrorCode::InvalidState);
}

// ─────────────────────────────────────────────────────────────────────────────
// Shutdown Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(MachineContextTest, ShutdownReleasesMemory) {
    MachineContext ctx(config_);
    ctx.initialize();
    EXPECT_NE(ctx.memory, nullptr);

    ctx.shutdown();

    EXPECT_EQ(ctx.memory, nullptr);
}

TEST_F(MachineContextTest, ShutdownReleasesDma) {
    MachineContext ctx(config_);
    ctx.initialize();
    EXPECT_NE(ctx.dma, nullptr);

    ctx.shutdown();

    EXPECT_EQ(ctx.dma, nullptr);
}

TEST_F(MachineContextTest, ShutdownSetsShutdownState) {
    MachineContext ctx(config_);
    ctx.initialize();

    ctx.shutdown();

    EXPECT_EQ(ctx.state(), MachineState::Shutdown);
}

TEST_F(MachineContextTest, ShutdownIsIdempotent) {
    MachineContext ctx(config_);
    ctx.initialize();

    ctx.shutdown();
    EXPECT_NO_THROW(ctx.shutdown());
    EXPECT_NO_THROW(ctx.shutdown());

    EXPECT_EQ(ctx.state(), MachineState::Shutdown);
}

TEST_F(MachineContextTest, ShutdownOnUninitializedIsNoOp) {
    MachineContext ctx(config_);

    EXPECT_NO_THROW(ctx.shutdown());

    // Should stay in Created or go to Shutdown
    EXPECT_TRUE(ctx.state() == MachineState::Created ||
                ctx.state() == MachineState::Shutdown);
}

TEST_F(MachineContextTest, DestructorCallsShutdown) {
    auto ctx = std::make_unique<MachineContext>(config_);
    ctx->initialize();

    EXPECT_NE(ctx->memory, nullptr);

    // Destructor should clean up
    ctx.reset();

    // No assertion needed - just checking it doesn't crash
}

// ─────────────────────────────────────────────────────────────────────────────
// Reset Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(MachineContextTest, ResetReinitializes) {
    MachineContext ctx(config_);
    ctx.initialize();
    ctx.step(100);
    EXPECT_GT(ctx.virtual_ticks(), 0u);

    auto result = ctx.reset();

    EXPECT_TRUE(result.has_value());
    EXPECT_EQ(ctx.state(), MachineState::Initialized);
    EXPECT_EQ(ctx.virtual_ticks(), 0u);
    EXPECT_EQ(ctx.total_cycles(), 0u);
}

TEST_F(MachineContextTest, ResetOnUninitializedFails) {
    MachineContext ctx(config_);

    auto result = ctx.reset();

    EXPECT_FALSE(result.has_value());
    EXPECT_EQ(result.error().code(), ErrorCode::InvalidState);
}

// ─────────────────────────────────────────────────────────────────────────────
// Move Semantics Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(MachineContextTest, MoveConstructorTransfersState) {
    MachineContext original(config_);
    original.initialize();

    MachineContext moved(std::move(original));

    EXPECT_EQ(moved.state(), MachineState::Initialized);
    EXPECT_EQ(original.state(), MachineState::Destroyed);
    EXPECT_NE(moved.memory, nullptr);
}

TEST_F(MachineContextTest, MoveAssignmentTransfersState) {
    MachineContext a(config_);
    a.initialize();

    MachineContext b(config_);
    b = std::move(a);

    EXPECT_EQ(b.state(), MachineState::Initialized);
    EXPECT_NE(b.memory, nullptr);
}

TEST_F(MachineContextTest, MoveAssignmentCleansUpTarget) {
    MachineContext a(config_);
    a.initialize();

    MachineContext b(config_);
    b.initialize();
    auto* b_memory = b.memory.get();

    b = std::move(a);

    // b should have a's memory now, old memory should be freed
    EXPECT_NE(b.memory.get(), b_memory);
}

// ─────────────────────────────────────────────────────────────────────────────
// Error State Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(MachineContextTest, LastErrorInitiallyEmpty) {
    MachineContext ctx(config_);

    EXPECT_FALSE(ctx.last_error().has_value());
}

TEST_F(MachineContextTest, LastErrorSetOnFailure) {
    MachineContext ctx(config_);

    // Try to step without init (will fail)
    ctx.step(10);

    EXPECT_TRUE(ctx.last_error().has_value());
}

// ─────────────────────────────────────────────────────────────────────────────
// Stress Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(MachineContextTest, RepeatedInitShutdown) {
    for (int i = 0; i < 50; i++) {
        MachineContext ctx(config_);
        EXPECT_TRUE(ctx.initialize().has_value());
        ctx.shutdown();
    }
    // ASan will catch any leaks
}

TEST_F(MachineContextTest, ManySteps) {
    MachineContext ctx(config_);
    ctx.initialize();

    for (int i = 0; i < 100; i++) {
        auto result = ctx.step(1);
        EXPECT_TRUE(result.has_value());
    }

    EXPECT_EQ(ctx.virtual_ticks(), 100u);
}

// ─────────────────────────────────────────────────────────────────────────────
// IsRunning Query Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(MachineContextTest, IsRunningQuery) {
    MachineContext ctx(config_);

    EXPECT_FALSE(ctx.is_running());

    ctx.initialize();
    EXPECT_FALSE(ctx.is_running());  // Initialized, not running

    // Note: Without async, we can't easily test is_running during execution
}
