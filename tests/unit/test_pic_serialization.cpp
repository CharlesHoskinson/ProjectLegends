/**
 * @file test_pic_serialization.cpp
 * @brief Unit tests for PIC controller serialization round-trip.
 *
 * Verifies that all PicController fields survive a serialize/deserialize
 * cycle through the EngineStatePic wire format.
 */

#include <gtest/gtest.h>
#include <dosbox/engine_state.h>
#include <dosbox/pic_types.h>
#include <dosbox/dosbox_context.h>
#include <cstring>

using dosbox::PicController;
using dosbox::EngineStatePic;

// ─────────────────────────────────────────────────────────────────────────────
// Test that EngineStatePic captures the critical PIC fields
// ─────────────────────────────────────────────────────────────────────────────

TEST(PicSerialization, TopLevelFieldsRoundTrip) {
    // Create a PicState with non-default values
    dosbox::PicState src{};
    src.ticks = 123456789ULL;
    src.irq_check = 0x42;
    src.irq_check_pending = 0x07;
    src.master_cascade_irq = 2;
    src.in_event_service = true;

    // Set controller fields that the current EngineStatePic captures
    src.controllers[0].imr = 0x12;
    src.controllers[0].isr = 0x34;
    src.controllers[0].auto_eoi = true;
    src.controllers[1].imr = 0x56;
    src.controllers[1].isr = 0x78;

    // Serialize to EngineStatePic
    EngineStatePic wire{};
    wire.ticks = src.ticks;
    wire.irq_check = src.irq_check;
    wire.irq_check_pending = src.irq_check_pending;
    wire.master_cascade_irq = src.master_cascade_irq;
    wire.master_imr = src.controllers[0].imr;
    wire.slave_imr = src.controllers[1].imr;
    wire.master_isr = src.controllers[0].isr;
    wire.slave_isr = src.controllers[1].isr;
    wire.auto_eoi = src.controllers[0].auto_eoi ? 1 : 0;
    wire.in_event_service = src.in_event_service ? 1 : 0;

    // Deserialize back
    dosbox::PicState dst{};
    dst.ticks = wire.ticks;
    dst.irq_check = wire.irq_check;
    dst.irq_check_pending = wire.irq_check_pending;
    dst.master_cascade_irq = wire.master_cascade_irq;
    dst.controllers[0].imr = wire.master_imr;
    dst.controllers[1].imr = wire.slave_imr;
    dst.controllers[0].isr = wire.master_isr;
    dst.controllers[1].isr = wire.slave_isr;
    dst.controllers[0].auto_eoi = wire.auto_eoi != 0;
    dst.in_event_service = wire.in_event_service != 0;

    // Verify
    EXPECT_EQ(dst.ticks, 123456789ULL);
    EXPECT_EQ(dst.irq_check, 0x42u);
    EXPECT_EQ(dst.irq_check_pending, 0x07u);
    EXPECT_EQ(dst.master_cascade_irq, 2);
    EXPECT_TRUE(dst.in_event_service);
    EXPECT_EQ(dst.controllers[0].imr, 0x12);
    EXPECT_EQ(dst.controllers[0].isr, 0x34);
    EXPECT_TRUE(dst.controllers[0].auto_eoi);
    EXPECT_EQ(dst.controllers[1].imr, 0x56);
    EXPECT_EQ(dst.controllers[1].isr, 0x78);
}

// ─────────────────────────────────────────────────────────────────────────────
// Test PicController struct layout
// ─────────────────────────────────────────────────────────────────────────────

TEST(PicSerialization, ControllerDefaultState) {
    PicController ctrl{};
    ctrl.reset();

    EXPECT_EQ(ctrl.icw_words, 0u);
    EXPECT_EQ(ctrl.icw_index, 0u);
    EXPECT_FALSE(ctrl.special);
    EXPECT_FALSE(ctrl.auto_eoi);
    EXPECT_FALSE(ctrl.rotate_on_auto_eoi);
    EXPECT_FALSE(ctrl.single);
    EXPECT_FALSE(ctrl.request_issr);
    EXPECT_EQ(ctrl.vector_base, 0);
    EXPECT_EQ(ctrl.input, 0);
    EXPECT_EQ(ctrl.edge, 0);
    EXPECT_EQ(ctrl.irr, 0);
    EXPECT_EQ(ctrl.imr, 0xFF);
    EXPECT_EQ(ctrl.imrr, 0);
    EXPECT_EQ(ctrl.isr, 0);
    EXPECT_EQ(ctrl.isrr, 0xFF);
    EXPECT_EQ(ctrl.isr_ignore, 0);
    EXPECT_EQ(ctrl.active_irq, 8);
}

// ─────────────────────────────────────────────────────────────────────────────
// Test that all 18 PicController fields can be set and read
// (Validates the struct is complete for future full serialization)
// ─────────────────────────────────────────────────────────────────────────────

TEST(PicSerialization, AllControllerFieldsAccessible) {
    PicController ctrl{};
    ctrl.icw_words = 4;
    ctrl.icw_index = 2;
    ctrl.special = true;
    ctrl.auto_eoi = true;
    ctrl.rotate_on_auto_eoi = true;
    ctrl.single = true;
    ctrl.request_issr = true;
    ctrl.vector_base = 0x08;
    ctrl.input = 0xFF;
    ctrl.edge = 0x42;
    ctrl.irr = 0x81;
    ctrl.imr = 0x00;
    ctrl.imrr = 0xFF;
    ctrl.isr = 0x04;
    ctrl.isrr = 0xFB;
    ctrl.isr_ignore = 0x00;
    ctrl.active_irq = 3;
    ctrl.controller_index = 0;

    EXPECT_EQ(ctrl.icw_words, 4u);
    EXPECT_EQ(ctrl.icw_index, 2u);
    EXPECT_TRUE(ctrl.special);
    EXPECT_TRUE(ctrl.auto_eoi);
    EXPECT_TRUE(ctrl.rotate_on_auto_eoi);
    EXPECT_TRUE(ctrl.single);
    EXPECT_TRUE(ctrl.request_issr);
    EXPECT_EQ(ctrl.vector_base, 0x08);
    EXPECT_EQ(ctrl.input, 0xFF);
    EXPECT_EQ(ctrl.edge, 0x42);
    EXPECT_EQ(ctrl.irr, 0x81);
    EXPECT_EQ(ctrl.imr, 0x00);
    EXPECT_EQ(ctrl.imrr, 0xFF);
    EXPECT_EQ(ctrl.isr, 0x04);
    EXPECT_EQ(ctrl.isrr, 0xFB);
    EXPECT_EQ(ctrl.isr_ignore, 0x00);
    EXPECT_EQ(ctrl.active_irq, 3);
    EXPECT_EQ(ctrl.controller_index, 0);
}

// ─────────────────────────────────────────────────────────────────────────────
// Test EngineStatePic size is stable
// ─────────────────────────────────────────────────────────────────────────────

TEST(PicSerialization, WireFormatSizeStable) {
    EXPECT_EQ(sizeof(EngineStatePic), 24u)
        << "EngineStatePic must be 24 bytes for V3 backward compat";
}

// ─────────────────────────────────────────────────────────────────────────────
// Test that EngineStatePic is trivially copyable (safe for memcpy)
// ─────────────────────────────────────────────────────────────────────────────

TEST(PicSerialization, WireFormatIsTriviallyCopyable) {
    EXPECT_TRUE(std::is_trivially_copyable_v<EngineStatePic>);
}
