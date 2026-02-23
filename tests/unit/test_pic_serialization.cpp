/**
 * @file test_pic_serialization.cpp
 * @brief Unit tests for PIC controller serialization round-trip.
 *
 * V4: full 18-field controller serialization for both master and slave.
 */

#include <gtest/gtest.h>
#include <dosbox/engine_state.h>
#include <dosbox/pic_types.h>
#include <dosbox/dosbox_context.h>
#include <cstring>

using dosbox::PicController;
using dosbox::EngineStatePic;
using dosbox::EngineStatePicController;
using dosbox::EngineStatePicV3;

// ─────────────────────────────────────────────────────────────────────────────
// Helper: serialize one controller to wire format
// ─────────────────────────────────────────────────────────────────────────────

static void serialize_controller(const PicController& src, EngineStatePicController& dst) {
    dst = {};
    dst.icw_words = src.icw_words;
    dst.icw_index = src.icw_index;
    dst.special = src.special ? 1 : 0;
    dst.auto_eoi = src.auto_eoi ? 1 : 0;
    dst.rotate_on_auto_eoi = src.rotate_on_auto_eoi ? 1 : 0;
    dst.single = src.single ? 1 : 0;
    dst.request_issr = src.request_issr ? 1 : 0;
    dst.vector_base = src.vector_base;
    dst.input = src.input;
    dst.edge = src.edge;
    dst.irr = src.irr;
    dst.imr = src.imr;
    dst.imrr = src.imrr;
    dst.isr = src.isr;
    dst.isrr = src.isrr;
    dst.isr_ignore = src.isr_ignore;
    dst.active_irq = src.active_irq;
    dst.controller_index = src.controller_index;
}

static void deserialize_controller(const EngineStatePicController& src, PicController& dst) {
    dst.icw_words = src.icw_words;
    dst.icw_index = src.icw_index;
    dst.special = src.special != 0;
    dst.auto_eoi = src.auto_eoi != 0;
    dst.rotate_on_auto_eoi = src.rotate_on_auto_eoi != 0;
    dst.single = src.single != 0;
    dst.request_issr = src.request_issr != 0;
    dst.vector_base = src.vector_base;
    dst.input = src.input;
    dst.edge = src.edge;
    dst.irr = src.irr;
    dst.imr = src.imr;
    dst.imrr = src.imrr;
    dst.isr = src.isr;
    dst.isrr = src.isrr;
    dst.isr_ignore = src.isr_ignore;
    dst.active_irq = src.active_irq;
    dst.controller_index = src.controller_index;
}

// ─────────────────────────────────────────────────────────────────────────────
// Full PIC round-trip (V4 format)
// ─────────────────────────────────────────────────────────────────────────────

TEST(PicSerialization, TopLevelFieldsRoundTrip) {
    dosbox::PicState src{};
    src.ticks = 123456789ULL;
    src.irq_check = 0x42;
    src.irq_check_pending = 0x07;
    src.master_cascade_irq = 2;
    src.in_event_service = true;
    src.enable_slave_pic = true;

    // Set all controller fields to non-default
    src.controllers[0].icw_words = 4;
    src.controllers[0].icw_index = 2;
    src.controllers[0].special = true;
    src.controllers[0].auto_eoi = true;
    src.controllers[0].rotate_on_auto_eoi = true;
    src.controllers[0].single = false;
    src.controllers[0].request_issr = true;
    src.controllers[0].vector_base = 0x08;
    src.controllers[0].input = 0xFF;
    src.controllers[0].edge = 0x42;
    src.controllers[0].irr = 0x81;
    src.controllers[0].imr = 0x12;
    src.controllers[0].imrr = 0xED;
    src.controllers[0].isr = 0x34;
    src.controllers[0].isrr = 0xCB;
    src.controllers[0].isr_ignore = 0x00;
    src.controllers[0].active_irq = 3;
    src.controllers[0].controller_index = 0;

    src.controllers[1].icw_words = 3;
    src.controllers[1].vector_base = 0x70;
    src.controllers[1].imr = 0x56;
    src.controllers[1].isr = 0x78;
    src.controllers[1].controller_index = 1;

    // Serialize to wire format
    EngineStatePic wire{};
    wire.ticks = src.ticks;
    wire.irq_check = src.irq_check;
    wire.irq_check_pending = src.irq_check_pending;
    wire.master_cascade_irq = src.master_cascade_irq;
    wire.in_event_service = src.in_event_service ? 1 : 0;
    wire.enable_slave_pic = src.enable_slave_pic ? 1 : 0;
    serialize_controller(src.controllers[0], wire.controllers[0]);
    serialize_controller(src.controllers[1], wire.controllers[1]);

    // Deserialize back
    dosbox::PicState dst{};
    dst.ticks = wire.ticks;
    dst.irq_check = wire.irq_check;
    dst.irq_check_pending = wire.irq_check_pending;
    dst.master_cascade_irq = wire.master_cascade_irq;
    dst.in_event_service = wire.in_event_service != 0;
    dst.enable_slave_pic = wire.enable_slave_pic != 0;
    deserialize_controller(wire.controllers[0], dst.controllers[0]);
    deserialize_controller(wire.controllers[1], dst.controllers[1]);

    // Verify top-level
    EXPECT_EQ(dst.ticks, 123456789ULL);
    EXPECT_EQ(dst.irq_check, 0x42u);
    EXPECT_EQ(dst.irq_check_pending, 0x07u);
    EXPECT_EQ(dst.master_cascade_irq, 2);
    EXPECT_TRUE(dst.in_event_service);
    EXPECT_TRUE(dst.enable_slave_pic);

    // Verify master controller (all 18 fields)
    EXPECT_EQ(dst.controllers[0].icw_words, 4u);
    EXPECT_EQ(dst.controllers[0].icw_index, 2u);
    EXPECT_TRUE(dst.controllers[0].special);
    EXPECT_TRUE(dst.controllers[0].auto_eoi);
    EXPECT_TRUE(dst.controllers[0].rotate_on_auto_eoi);
    EXPECT_FALSE(dst.controllers[0].single);
    EXPECT_TRUE(dst.controllers[0].request_issr);
    EXPECT_EQ(dst.controllers[0].vector_base, 0x08);
    EXPECT_EQ(dst.controllers[0].input, 0xFF);
    EXPECT_EQ(dst.controllers[0].edge, 0x42);
    EXPECT_EQ(dst.controllers[0].irr, 0x81);
    EXPECT_EQ(dst.controllers[0].imr, 0x12);
    EXPECT_EQ(dst.controllers[0].imrr, 0xED);
    EXPECT_EQ(dst.controllers[0].isr, 0x34);
    EXPECT_EQ(dst.controllers[0].isrr, 0xCB);
    EXPECT_EQ(dst.controllers[0].isr_ignore, 0x00);
    EXPECT_EQ(dst.controllers[0].active_irq, 3);
    EXPECT_EQ(dst.controllers[0].controller_index, 0);

    // Verify slave controller
    EXPECT_EQ(dst.controllers[1].icw_words, 3u);
    EXPECT_EQ(dst.controllers[1].vector_base, 0x70);
    EXPECT_EQ(dst.controllers[1].imr, 0x56);
    EXPECT_EQ(dst.controllers[1].isr, 0x78);
    EXPECT_EQ(dst.controllers[1].controller_index, 1);
}

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

TEST(PicSerialization, WireFormatSizeStable) {
    EXPECT_EQ(sizeof(EngineStatePicController), 24u);
    EXPECT_EQ(sizeof(EngineStatePic), 72u);
    EXPECT_EQ(sizeof(EngineStatePicV3), 24u);
}

TEST(PicSerialization, WireFormatIsTriviallyCopyable) {
    EXPECT_TRUE(std::is_trivially_copyable_v<EngineStatePic>);
    EXPECT_TRUE(std::is_trivially_copyable_v<EngineStatePicController>);
    EXPECT_TRUE(std::is_trivially_copyable_v<EngineStatePicV3>);
}
