/**
 * @file test_builder.cpp
 * @brief Unit tests for MachineBuilder and memory literals.
 */

#include <gtest/gtest.h>
#include <legends/builder.h>

using namespace legends;
using namespace legends::literals;

// ─────────────────────────────────────────────────────────────────────────────
// User-Defined Literal Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(MemoryLiteralsTest, Kilobytes) {
    EXPECT_EQ(1_KB, 1024u);
    EXPECT_EQ(64_KB, 65536u);
    EXPECT_EQ(640_KB, 655360u);
}

TEST(MemoryLiteralsTest, Megabytes) {
    EXPECT_EQ(1_MB, 1048576u);
    EXPECT_EQ(16_MB, 16777216u);
    EXPECT_EQ(256_MB, 268435456u);
}

TEST(MemoryLiteralsTest, Gigabytes) {
    EXPECT_EQ(1_GB, 1073741824u);
    EXPECT_EQ(4_GB, 4294967296u);
}

TEST(MemoryLiteralsTest, Cycles) {
    EXPECT_EQ(3000_cycles, 3000u);
    EXPECT_EQ(10000_cycles, 10000u);
}

TEST(MemoryLiteralsTest, CombinedExpressions) {
    EXPECT_EQ(1_MB + 512_KB, 1572864u);
    EXPECT_EQ(2_GB - 1_MB, 2146435072u);
}

// ─────────────────────────────────────────────────────────────────────────────
// Default Builder Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(MachineBuilderTest, DefaultBuildSucceeds) {
    auto result = MachineBuilder().build();

    EXPECT_TRUE(result.has_value());
}

TEST(MachineBuilderTest, DefaultConfigValues) {
    auto result = MachineBuilder().build();
    ASSERT_TRUE(result.has_value());

    auto config = result.value();
    EXPECT_EQ(config.memory_size, 16_MB);
    EXPECT_EQ(config.vga_memory, 256_KB);
    EXPECT_EQ(config.cpu_cycles, 3000u);
}

// ─────────────────────────────────────────────────────────────────────────────
// Memory Configuration Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(MachineBuilderTest, SetMemory) {
    auto result = MachineBuilder()
        .with_memory(4_MB)
        .build();

    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result.value().memory_size, 4_MB);
}

TEST(MachineBuilderTest, MemoryTooSmallFails) {
    auto result = MachineBuilder()
        .with_memory(512_KB)  // Less than 1MB
        .build();

    EXPECT_FALSE(result.has_value());
    EXPECT_EQ(result.error().code(), ErrorCode::ConfigValueInvalid);
}

TEST(MachineBuilderTest, MemoryTooLargeFails) {
    auto result = MachineBuilder()
        .with_memory(512_MB)  // More than 256MB
        .build();

    EXPECT_FALSE(result.has_value());
}

TEST(MachineBuilderTest, MemoryAtMinimum) {
    auto result = MachineBuilder()
        .with_memory(1_MB)
        .build();

    EXPECT_TRUE(result.has_value());
}

TEST(MachineBuilderTest, MemoryAtMaximum) {
    auto result = MachineBuilder()
        .with_memory(256_MB)
        .build();

    EXPECT_TRUE(result.has_value());
}

TEST(MachineBuilderTest, VgaMemoryTooSmallFails) {
    auto result = MachineBuilder()
        .with_vga_memory(32_KB)  // Less than 64KB
        .build();

    EXPECT_FALSE(result.has_value());
}

TEST(MachineBuilderTest, VgaMemoryTooLargeFails) {
    auto result = MachineBuilder()
        .with_vga_memory(32_MB)  // More than 16MB
        .build();

    EXPECT_FALSE(result.has_value());
}

// ─────────────────────────────────────────────────────────────────────────────
// CPU Configuration Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(MachineBuilderTest, SetCycles) {
    auto result = MachineBuilder()
        .with_cycles(10000)
        .build();

    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result.value().cpu_cycles, 10000u);
}

TEST(MachineBuilderTest, CyclesTooLowFails) {
    auto result = MachineBuilder()
        .with_cycles(50)  // Less than 100
        .build();

    EXPECT_FALSE(result.has_value());
}

TEST(MachineBuilderTest, CyclesTooHighFails) {
    auto result = MachineBuilder()
        .with_cycles(2000000)  // More than 1000000
        .build();

    EXPECT_FALSE(result.has_value());
}

TEST(MachineBuilderTest, DynamicCore) {
    auto result = MachineBuilder()
        .with_dynamic_core()
        .build();

    ASSERT_TRUE(result.has_value());
    EXPECT_TRUE(result.value().cpu_dynamic_core);
}

// ─────────────────────────────────────────────────────────────────────────────
// Machine Type Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(MachineBuilderTest, SetMachineType) {
    auto result = MachineBuilder()
        .with_machine_type(MachineType::EGA)
        .build();

    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result.value().machine_type, MachineType::EGA);
}

TEST(MachineBuilderTest, SvgaRequiresVgaMemory) {
    auto result = MachineBuilder()
        .with_machine_type(MachineType::SVGA_S3)
        .with_vga_memory(256_KB)  // Not enough for SVGA
        .build();

    EXPECT_FALSE(result.has_value());
}

TEST(MachineBuilderTest, SvgaWithSufficientVgaMemory) {
    auto result = MachineBuilder()
        .with_machine_type(MachineType::SVGA_S3)
        .with_vga_memory(2_MB)
        .build();

    EXPECT_TRUE(result.has_value());
}

// ─────────────────────────────────────────────────────────────────────────────
// Peripheral Configuration Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(MachineBuilderTest, DeterministicMode) {
    auto result = MachineBuilder()
        .deterministic()
        .build();

    ASSERT_TRUE(result.has_value());
    EXPECT_TRUE(result.value().deterministic);
}

TEST(MachineBuilderTest, DisableSound) {
    auto result = MachineBuilder()
        .with_sound(false)
        .build();

    ASSERT_TRUE(result.has_value());
    EXPECT_FALSE(result.value().sound_enabled);
}

TEST(MachineBuilderTest, DisableSb16) {
    auto result = MachineBuilder()
        .with_sb16(false)
        .build();

    ASSERT_TRUE(result.has_value());
    EXPECT_FALSE(result.value().sb16_enabled);
}

TEST(MachineBuilderTest, DisableAdlib) {
    auto result = MachineBuilder()
        .with_adlib(false)
        .build();

    ASSERT_TRUE(result.has_value());
    EXPECT_FALSE(result.value().adlib_enabled);
}

TEST(MachineBuilderTest, DebugMode) {
    auto result = MachineBuilder()
        .with_debug()
        .build();

    ASSERT_TRUE(result.has_value());
    EXPECT_TRUE(result.value().debug_mode);
}

// ─────────────────────────────────────────────────────────────────────────────
// Preset Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(MachineBuilderTest, MinimalPreset) {
    auto result = MachineBuilder()
        .minimal()
        .build();

    ASSERT_TRUE(result.has_value());
    auto config = result.value();
    EXPECT_EQ(config.memory_size, 1_MB);
    EXPECT_EQ(config.vga_memory, 64_KB);
    EXPECT_FALSE(config.sound_enabled);
    EXPECT_TRUE(config.deterministic);
}

TEST(MachineBuilderTest, VgaStandardPreset) {
    auto result = MachineBuilder()
        .vga_standard()
        .build();

    ASSERT_TRUE(result.has_value());
    auto config = result.value();
    EXPECT_EQ(config.machine_type, MachineType::VGA);
    EXPECT_EQ(config.memory_size, 16_MB);
}

// ─────────────────────────────────────────────────────────────────────────────
// Chaining Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(MachineBuilderTest, ChainedBuildWorks) {
    auto result = MachineBuilder()
        .with_memory(8_MB)
        .with_vga_memory(512_KB)
        .with_cycles(5000)
        .with_machine_type(MachineType::VGA)
        .deterministic()
        .with_sound(false)
        .build();

    ASSERT_TRUE(result.has_value());

    auto config = result.value();
    EXPECT_EQ(config.memory_size, 8_MB);
    EXPECT_EQ(config.vga_memory, 512_KB);
    EXPECT_EQ(config.cpu_cycles, 5000u);
    EXPECT_EQ(config.machine_type, MachineType::VGA);
    EXPECT_TRUE(config.deterministic);
    EXPECT_FALSE(config.sound_enabled);
}

TEST(MachineBuilderTest, ChainedOverwrite) {
    auto result = MachineBuilder()
        .with_memory(4_MB)
        .with_memory(8_MB)  // Overwrite
        .build();

    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result.value().memory_size, 8_MB);
}

// ─────────────────────────────────────────────────────────────────────────────
// Validation Query Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(MachineBuilderTest, IsValidForValidConfig) {
    MachineBuilder builder;
    builder.with_memory(16_MB);

    EXPECT_TRUE(builder.is_valid());
}

TEST(MachineBuilderTest, IsValidForInvalidConfig) {
    MachineBuilder builder;
    builder.with_memory(512_KB);

    EXPECT_FALSE(builder.is_valid());
}

TEST(MachineBuilderTest, ErrorsAfterBuild) {
    MachineBuilder builder;
    builder.with_memory(512_KB);
    (void)builder.build();

    EXPECT_FALSE(builder.errors().empty());
}

TEST(MachineBuilderTest, CurrentConfigAccess) {
    MachineBuilder builder;
    builder.with_memory(8_MB);

    EXPECT_EQ(builder.current_config().memory_size, 8_MB);
}

// ─────────────────────────────────────────────────────────────────────────────
// Build or Throw Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(MachineBuilderTest, BuildOrThrowSuccess) {
    EXPECT_NO_THROW({
        auto config = MachineBuilder()
            .with_memory(16_MB)
            .build_or_throw();
        EXPECT_EQ(config.memory_size, 16_MB);
    });
}

TEST(MachineBuilderTest, BuildOrThrowFailure) {
    EXPECT_THROW({
        (void)MachineBuilder()
            .with_memory(512_KB)
            .build_or_throw();
    }, std::runtime_error);
}

// ─────────────────────────────────────────────────────────────────────────────
// Multiple Errors Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(MachineBuilderTest, MultipleErrorsCollected) {
    auto result = MachineBuilder()
        .with_memory(512_KB)    // Error 1
        .with_cycles(50)        // Error 2
        .build();

    EXPECT_FALSE(result.has_value());

    MachineBuilder builder;
    builder.with_memory(512_KB);
    builder.with_cycles(50);
    (void)builder.build();

    EXPECT_GE(builder.errors().size(), 2u);
}
