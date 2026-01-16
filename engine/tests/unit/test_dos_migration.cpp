/**
 * @file test_dos_migration.cpp
 * @brief Sprint 2 Phase 4: DOS Block Migration Tests
 *
 * Tests for migrating DOS state to DOSBoxContext.
 * These tests verify the DosState struct and its integration with
 * the context-based architecture.
 *
 * Test IDs from phase-04-dos-block.md:
 * - TEST-P04-U01: DOS State Default Initialization
 * - TEST-P04-U02: PSP Address Calculation
 * - TEST-P04-U03: DTA Address Calculation
 * - TEST-P04-U04: Compatibility Layer PSP Access
 * - TEST-P04-U05: Compatibility Layer DTA Access
 * - TEST-P04-U06: Kernel Disabled Flag
 * - TEST-P04-I01: DOS Boot Succeeds
 * - TEST-P04-I02: File Operations Work
 * - TEST-P04-I03: DOS Isolation Between Instances
 * - TEST-P04-D01: DOS State In Hash
 * - TEST-P04-D02: PSP Change Affects Hash
 */

#include <gtest/gtest.h>
#include "dosbox/dosbox_context.h"
#include "dosbox/state_hash.h"

using namespace dosbox;

// ===============================================================================
// Unit Tests
// ===============================================================================

/**
 * TEST-P04-U01: DOS State Default Initialization
 * Verify new context has correct default DOS state.
 */
TEST(DosMigration, DefaultStateCorrect) {
    DOSBoxContext ctx(ContextConfig::minimal());

    // Kernel should be disabled by default
    EXPECT_TRUE(ctx.dos.kernel_disabled);
    EXPECT_FALSE(ctx.dos.kernel_running);

    // PSP and DTA should be zero
    EXPECT_EQ(ctx.dos.psp_segment, 0);
    EXPECT_EQ(ctx.dos.dta_segment, 0);
    EXPECT_EQ(ctx.dos.dta_offset, 0);

    // Default DOS version 5.0
    EXPECT_EQ(ctx.dos.version.major, 5);
    EXPECT_EQ(ctx.dos.version.minor, 0);

    // Default drive is C: (2)
    EXPECT_EQ(ctx.dos.current_drive, 2);

    // Other defaults
    EXPECT_EQ(ctx.dos.verify, 0);
    EXPECT_EQ(ctx.dos.return_code, 0);
    EXPECT_FALSE(ctx.dos.return_mode);
    EXPECT_EQ(ctx.dos.country, 1);
    EXPECT_EQ(ctx.dos.codepage, 437);
}

/**
 * TEST-P04-U02: PSP Address Calculation
 * Verify PSP physical address = segment * 16.
 */
TEST(DosMigration, PspAddressCalculation) {
    DOSBoxContext ctx(ContextConfig::minimal());

    ctx.dos.psp_segment = 0x1234;
    EXPECT_EQ(ctx.dos.psp_address(), 0x12340);  // 0x1234 * 16

    ctx.dos.psp_segment = 0x0000;
    EXPECT_EQ(ctx.dos.psp_address(), 0x00000);

    ctx.dos.psp_segment = 0xFFFF;
    EXPECT_EQ(ctx.dos.psp_address(), 0xFFFF0);  // Max segment
}

/**
 * TEST-P04-U03: DTA Address Calculation
 * Verify DTA physical address = segment * 16 + offset.
 */
TEST(DosMigration, DtaAddressCalculation) {
    DOSBoxContext ctx(ContextConfig::minimal());

    ctx.dos.dta_segment = 0x1000;
    ctx.dos.dta_offset = 0x80;
    EXPECT_EQ(ctx.dos.dta_address(), 0x10080);  // 0x1000*16 + 0x80

    ctx.dos.dta_segment = 0x1238;
    ctx.dos.dta_offset = 0x0;
    EXPECT_EQ(ctx.dos.dta_address(), 0x12380);

    ctx.dos.dta_segment = 0x0;
    ctx.dos.dta_offset = 0x100;
    EXPECT_EQ(ctx.dos.dta_address(), 0x100);
}

/**
 * TEST-P04-U04: Compatibility Layer PSP Access
 * Verify PSP can be set and retrieved via context.
 */
TEST(DosMigration, PspAccessViaContext) {
    DOSBoxContext ctx(ContextConfig::minimal());

    ctx.dos.psp_segment = 0x2000;
    EXPECT_EQ(ctx.dos.psp_segment, 0x2000);
    EXPECT_EQ(ctx.dos.psp_address(), 0x20000);
}

/**
 * TEST-P04-U05: Compatibility Layer DTA Access
 * Verify DTA can be set and retrieved via context.
 */
TEST(DosMigration, DtaAccessViaContext) {
    DOSBoxContext ctx(ContextConfig::minimal());

    // Set DTA to physical address 0x12380
    ctx.dos.dta_segment = 0x1238;
    ctx.dos.dta_offset = 0x0;

    EXPECT_EQ(ctx.dos.dta_address(), 0x12380);
    EXPECT_EQ(ctx.dos.dta_segment, 0x1238);
    EXPECT_EQ(ctx.dos.dta_offset, 0x0);
}

/**
 * TEST-P04-U06: Kernel Disabled Flag
 * Verify kernel disabled flag behavior.
 */
TEST(DosMigration, KernelDisabledFlag) {
    DOSBoxContext ctx(ContextConfig::minimal());

    // Default: kernel disabled
    EXPECT_TRUE(ctx.dos.kernel_disabled);
    EXPECT_FALSE(ctx.dos.kernel_running);

    // Can enable kernel
    ctx.dos.kernel_disabled = false;
    ctx.dos.kernel_running = true;
    EXPECT_FALSE(ctx.dos.kernel_disabled);
    EXPECT_TRUE(ctx.dos.kernel_running);
}

/**
 * TEST-P04-U07: DOS State Reset
 * Verify reset() restores default values.
 */
TEST(DosMigration, ResetRestoresDefaults) {
    DOSBoxContext ctx(ContextConfig::minimal());

    // Modify state
    ctx.dos.kernel_disabled = false;
    ctx.dos.kernel_running = true;
    ctx.dos.psp_segment = 0x1234;
    ctx.dos.dta_segment = 0x5678;
    ctx.dos.dta_offset = 0x9ABC;
    ctx.dos.version.major = 6;
    ctx.dos.version.minor = 22;
    ctx.dos.current_drive = 0;
    ctx.dos.return_code = 42;
    ctx.dos.codepage = 850;

    // Reset
    ctx.dos.reset();

    // Verify defaults restored
    EXPECT_TRUE(ctx.dos.kernel_disabled);
    EXPECT_FALSE(ctx.dos.kernel_running);
    EXPECT_EQ(ctx.dos.psp_segment, 0);
    EXPECT_EQ(ctx.dos.dta_segment, 0);
    EXPECT_EQ(ctx.dos.dta_offset, 0);
    EXPECT_EQ(ctx.dos.version.major, 5);
    EXPECT_EQ(ctx.dos.version.minor, 0);
    EXPECT_EQ(ctx.dos.current_drive, 2);
    EXPECT_EQ(ctx.dos.return_code, 0);
    EXPECT_EQ(ctx.dos.codepage, 437);
}

// ===============================================================================
// Integration Tests
// ===============================================================================

/**
 * TEST-P04-I01: DOS Boot Succeeds
 * Verify context can be initialized with DOS state.
 */
TEST(DosIntegration, ContextInitializesWithDos) {
    DOSBoxContext ctx(ContextConfig::defaults());
    auto result = ctx.initialize();
    ASSERT_TRUE(result.has_value()) << "Context initialization failed";

    // DOS state should exist and have valid defaults
    EXPECT_EQ(ctx.dos.version.major, 5);
    EXPECT_EQ(ctx.dos.current_drive, 2);

    ctx.shutdown();
}

/**
 * TEST-P04-I02: File Operations Work
 * Verify DOS state can track file-related state.
 */
TEST(DosIntegration, DosStateTracksFileInfo) {
    DOSBoxContext ctx(ContextConfig::defaults());
    auto result = ctx.initialize();
    ASSERT_TRUE(result.has_value());

    // Set PSP for a "running program"
    ctx.dos.psp_segment = 0x1000;

    // Set DTA for file operations
    ctx.dos.dta_segment = 0x1000;
    ctx.dos.dta_offset = 0x80;  // Standard DTA offset

    EXPECT_EQ(ctx.dos.psp_address(), 0x10000);
    EXPECT_EQ(ctx.dos.dta_address(), 0x10080);

    ctx.shutdown();
}

/**
 * TEST-P04-I03: DOS Isolation Between Instances
 * Verify DOS state is isolated per context.
 */
TEST(DosIntegration, InstanceIsolation) {
    // First instance - modify DOS state
    {
        DOSBoxContext ctx1(ContextConfig::defaults());
        ctx1.initialize();
        ctx1.dos.version.major = 6;
        ctx1.dos.version.minor = 22;
        ctx1.dos.return_code = 42;
        ctx1.dos.psp_segment = 0xABCD;
        ctx1.shutdown();
    }

    // Second instance - should have default state
    {
        DOSBoxContext ctx2(ContextConfig::defaults());
        ctx2.initialize();

        EXPECT_EQ(ctx2.dos.version.major, 5);   // Default, not 6
        EXPECT_EQ(ctx2.dos.version.minor, 0);   // Default, not 22
        EXPECT_EQ(ctx2.dos.return_code, 0);     // Default, not 42
        EXPECT_EQ(ctx2.dos.psp_segment, 0);     // Default, not 0xABCD

        ctx2.shutdown();
    }
}

// ===============================================================================
// Determinism Tests
// ===============================================================================

/**
 * TEST-P04-D01: DOS State In Hash
 * Verify DOS state affects determinism hash.
 */
TEST(DosDeterminism, StateInHash) {
    StateHash hash1, hash2;

    {
        DOSBoxContext ctx(ContextConfig::defaults());
        ctx.initialize();
        ctx.dos.return_code = 0;
        auto result = get_state_hash(&ctx, HashMode::Fast);
        ASSERT_TRUE(result.has_value());
        hash1 = result.value();
        ctx.shutdown();
    }

    {
        DOSBoxContext ctx(ContextConfig::defaults());
        ctx.initialize();
        ctx.dos.return_code = 1;  // Different return code
        auto result = get_state_hash(&ctx, HashMode::Fast);
        ASSERT_TRUE(result.has_value());
        hash2 = result.value();
        ctx.shutdown();
    }

    // Hashes should differ due to different return_code
    EXPECT_NE(hash1, hash2);
}

/**
 * TEST-P04-D02: PSP Change Affects Hash
 * Verify PSP segment changes affect hash.
 */
TEST(DosDeterminism, PspInHash) {
    StateHash hash1, hash2;

    {
        DOSBoxContext ctx(ContextConfig::defaults());
        ctx.initialize();
        ctx.dos.psp_segment = 0x1000;
        auto result = get_state_hash(&ctx, HashMode::Fast);
        ASSERT_TRUE(result.has_value());
        hash1 = result.value();
        ctx.shutdown();
    }

    {
        DOSBoxContext ctx(ContextConfig::defaults());
        ctx.initialize();
        ctx.dos.psp_segment = 0x2000;  // Different PSP
        auto result = get_state_hash(&ctx, HashMode::Fast);
        ASSERT_TRUE(result.has_value());
        hash2 = result.value();
        ctx.shutdown();
    }

    // Hashes should differ due to different PSP
    EXPECT_NE(hash1, hash2);
}

/**
 * TEST-P04-D03: Same DOS State Produces Same Hash
 * Verify identical DOS state produces identical hash.
 */
TEST(DosDeterminism, SameStatesSameHash) {
    StateHash hash1, hash2;

    {
        DOSBoxContext ctx(ContextConfig::defaults());
        ctx.initialize();
        // Use all defaults
        auto result = get_state_hash(&ctx, HashMode::Fast);
        ASSERT_TRUE(result.has_value());
        hash1 = result.value();
        ctx.shutdown();
    }

    {
        DOSBoxContext ctx(ContextConfig::defaults());
        ctx.initialize();
        // Same defaults
        auto result = get_state_hash(&ctx, HashMode::Fast);
        ASSERT_TRUE(result.has_value());
        hash2 = result.value();
        ctx.shutdown();
    }

    // Hashes should be identical
    EXPECT_EQ(hash1, hash2);
}
