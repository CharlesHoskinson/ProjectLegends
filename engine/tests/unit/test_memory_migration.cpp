/**
 * @file test_memory_migration.cpp
 * @brief Unit tests for memory state in DOSBoxContext.
 *
 * Tests for memory state members: base, pages, a20.
 */

#include <gtest/gtest.h>
#include "dosbox/dosbox_context.h"

using namespace dosbox;

// ===============================================================================
// Unit Tests
// ===============================================================================

/**
 * TEST-P07-U01: Memory Base Default (nullptr)
 * Verify new context has nullptr base.
 */
TEST(MemoryMigration, MemoryBaseDefault) {
    DOSBoxContext ctx(ContextConfig::minimal());

    EXPECT_EQ(ctx.memory.base, nullptr);
    EXPECT_EQ(ctx.memory.size, 0u);
}

/**
 * TEST-P07-U02: Memory Pages Default
 * Verify memory page counts are zero.
 */
TEST(MemoryMigration, MemoryPagesDefault) {
    DOSBoxContext ctx(ContextConfig::minimal());

    EXPECT_EQ(ctx.memory.pages, 0u);
    EXPECT_EQ(ctx.memory.handler_pages, 0u);
    EXPECT_EQ(ctx.memory.reported_pages, 0u);
}

/**
 * TEST-P07-U03: Memory State Modification
 * Verify memory state can be modified.
 */
TEST(MemoryMigration, MemoryModification) {
    DOSBoxContext ctx(ContextConfig::minimal());

    ctx.memory.pages = 1024;
    ctx.memory.handler_pages = 256;
    ctx.memory.address_bits = 24;

    EXPECT_EQ(ctx.memory.pages, 1024u);
    EXPECT_EQ(ctx.memory.handler_pages, 256u);
    EXPECT_EQ(ctx.memory.address_bits, 24u);
}

/**
 * TEST-P07-U04: A20 Gate State
 * Verify A20 gate state is accessible.
 */
TEST(MemoryMigration, A20GateState) {
    DOSBoxContext ctx(ContextConfig::minimal());

    // Default A20 state
    EXPECT_FALSE(ctx.memory.a20.enabled);
    EXPECT_EQ(ctx.memory.a20.controlport, 0u);

    // Modify A20 state
    ctx.memory.a20.enabled = true;
    ctx.memory.a20.controlport = 0x92;

    EXPECT_TRUE(ctx.memory.a20.enabled);
    EXPECT_EQ(ctx.memory.a20.controlport, 0x92u);
}

/**
 * TEST-P07-U05: Memory State Reset
 * Verify reset clears appropriate fields.
 */
TEST(MemoryMigration, MemoryReset) {
    DOSBoxContext ctx(ContextConfig::minimal());

    // Set some values
    ctx.memory.pages = 1024;
    ctx.memory.handler_pages = 256;
    ctx.memory.a20.enabled = true;
    ctx.memory.address_bits = 32;

    // Reset
    ctx.memory.reset();

    // Check reset values
    EXPECT_EQ(ctx.memory.pages, 0u);
    EXPECT_EQ(ctx.memory.handler_pages, 0u);
    EXPECT_FALSE(ctx.memory.a20.enabled);
    EXPECT_EQ(ctx.memory.address_bits, 20u);  // Default 8086
}

// ===============================================================================
// Integration Tests
// ===============================================================================

/**
 * TEST-P07-I01: Memory Isolation Between Instances
 * Verify memory state is isolated per instance.
 */
TEST(MemoryMigration, MemoryIsolation) {
    DOSBoxContext ctx1(ContextConfig::minimal());
    DOSBoxContext ctx2(ContextConfig::minimal());

    // Modify ctx1
    ctx1.memory.pages = 1000;
    ctx1.memory.a20.enabled = true;

    // Modify ctx2 differently
    ctx2.memory.pages = 2000;
    ctx2.memory.a20.enabled = false;

    // Verify isolation
    EXPECT_EQ(ctx1.memory.pages, 1000u);
    EXPECT_TRUE(ctx1.memory.a20.enabled);

    EXPECT_EQ(ctx2.memory.pages, 2000u);
    EXPECT_FALSE(ctx2.memory.a20.enabled);
}

/**
 * TEST-P07-I02: LFB Region State
 * Verify LFB region state is accessible.
 */
TEST(MemoryMigration, LfbRegionState) {
    DOSBoxContext ctx(ContextConfig::minimal());

    // Set LFB region
    ctx.memory.lfb.start_page = 0xA0;
    ctx.memory.lfb.end_page = 0xBF;
    ctx.memory.lfb.pages = 32;

    EXPECT_EQ(ctx.memory.lfb.start_page, 0xA0u);
    EXPECT_EQ(ctx.memory.lfb.end_page, 0xBFu);
    EXPECT_EQ(ctx.memory.lfb.pages, 32u);
}

/**
 * TEST-P07-I03: Address Aliasing State
 * Verify address aliasing masks are accessible.
 */
TEST(MemoryMigration, AddressAliasingState) {
    DOSBoxContext ctx(ContextConfig::minimal());

    ctx.memory.mem_alias_pagemask = 0x000FF;
    ctx.memory.mem_alias_pagemask_active = 0x000FF;
    ctx.memory.address_bits = 20;

    EXPECT_EQ(ctx.memory.mem_alias_pagemask, 0x000FFu);
    EXPECT_EQ(ctx.memory.mem_alias_pagemask_active, 0x000FFu);
    EXPECT_EQ(ctx.memory.address_bits, 20u);
}
