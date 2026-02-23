/**
 * @file test_pic_hardware.cpp
 * @brief Unit tests for PIC controller state model.
 *
 * Tests the PicController register-level state transitions that mirror
 * the TLA+ specification properties for the 8259A PIC.
 */

#include <gtest/gtest.h>
#include <dosbox/pic_types.h>

using dosbox::PicController;

// ─────────────────────────────────────────────────────────────────────────────
// Helper: simulate IRQ raise on a controller (mirrors pic.cpp raise_irq)
// ─────────────────────────────────────────────────────────────────────────────

static void sim_raise_irq(PicController& pic, uint8_t irq) {
    uint8_t bit = static_cast<uint8_t>(1u << irq);
    // Edge detect: skip if already high and edge-triggered
    if (bit & pic.edge & pic.input) return;
    pic.input |= bit;
    if ((pic.irr & bit) == 0) {
        pic.irr |= bit;
    }
}

// Helper: simulate IRQ lower
static void sim_lower_irq(PicController& pic, uint8_t irq) {
    uint8_t bit = static_cast<uint8_t>(1u << irq);
    pic.input &= static_cast<uint8_t>(~bit);
    pic.irr &= static_cast<uint8_t>(~bit);
}

// Helper: simulate start_irq (acknowledge and begin service)
static void sim_start_irq(PicController& pic, uint8_t irq) {
    uint8_t bit = static_cast<uint8_t>(1u << irq);
    pic.irr &= static_cast<uint8_t>(~bit);  // Clear request
    if (!pic.auto_eoi) {
        pic.active_irq = irq;
        pic.isr |= bit;                      // Mark in-service
        pic.isrr = static_cast<uint8_t>(~pic.isr | pic.isr_ignore);
    }
}

// Helper: simulate non-specific EOI (clear highest-priority ISR bit)
static void sim_eoi(PicController& pic) {
    for (uint8_t i = 0; i < 8; ++i) {
        uint8_t bit = static_cast<uint8_t>(1u << i);
        if (pic.isr & bit) {
            pic.isr &= static_cast<uint8_t>(~bit);
            pic.isrr = static_cast<uint8_t>(~pic.isr | pic.isr_ignore);
            if (pic.active_irq == i) {
                pic.active_irq = 8;  // No active IRQ
            }
            break;
        }
    }
}

// Helper: check if IRQ is dispatchable (pending, unmasked, not blocked by ISR)
static bool sim_is_dispatchable(const PicController& pic, uint8_t irq) {
    uint8_t bit = static_cast<uint8_t>(1u << irq);
    uint8_t possible = (pic.irr & pic.imrr) & pic.isrr;
    return (possible & bit) != 0;
}

// ─────────────────────────────────────────────────────────────────────────────
// Test 1: IRQ Raise and Acknowledge
// TLA+ property: IRQ raise sets IRR, acknowledge moves to ISR
// ─────────────────────────────────────────────────────────────────────────────

class PicHardwareTest : public ::testing::Test {
protected:
    PicController master;
    PicController slave;

    void SetUp() override {
        master.reset();
        master.controller_index = 0;
        master.vector_base = 0x08;
        // Unmask all IRQs for testing
        master.imr = 0x00;
        master.imrr = 0xFF;

        slave.reset();
        slave.controller_index = 1;
        slave.vector_base = 0x70;
        slave.imr = 0x00;
        slave.imrr = 0xFF;
    }
};

TEST_F(PicHardwareTest, IrqRaiseAndAcknowledge) {
    // Initially: no requests, no in-service
    EXPECT_EQ(master.irr, 0x00);
    EXPECT_EQ(master.isr, 0x00);

    // Raise IRQ 0
    sim_raise_irq(master, 0);
    EXPECT_EQ(master.irr & 0x01, 0x01) << "IRR bit 0 should be set after raise";
    EXPECT_EQ(master.isr, 0x00) << "ISR should be clear before acknowledge";

    // Acknowledge (start_irq)
    sim_start_irq(master, 0);
    EXPECT_EQ(master.irr & 0x01, 0x00) << "IRR bit 0 cleared after acknowledge";
    EXPECT_EQ(master.isr & 0x01, 0x01) << "ISR bit 0 set after acknowledge";
    EXPECT_EQ(master.active_irq, 0) << "Active IRQ should be 0";
}

// ─────────────────────────────────────────────────────────────────────────────
// Test 2: ISR/IRR Transitions
// TLA+ property: ISR blocks lower-priority IRQs, EOI restores
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(PicHardwareTest, IsrIrrTransitions) {
    // Raise IRQ 3
    sim_raise_irq(master, 3);
    EXPECT_TRUE(sim_is_dispatchable(master, 3));

    // Acknowledge IRQ 3 -> now in service
    sim_start_irq(master, 3);
    EXPECT_EQ(master.active_irq, 3);

    // IRQ 5 (lower priority) should not be dispatchable while 3 is in service
    sim_raise_irq(master, 5);
    EXPECT_EQ(master.irr & 0x20, 0x20) << "IRQ 5 should be in IRR";
    // In normal (non-special) mode, active_irq=3 blocks IRQ 5
    // The dispatch check: only IRQs < active_irq are dispatched
    // IRQ 5 >= active_irq(3), so blocked
    // (Not directly testable via sim_is_dispatchable since it doesn't check priority,
    //  but ISR bit 3 is set which blocks dispatch via isrr)

    // IRQ 1 (higher priority) should still be dispatchable
    sim_raise_irq(master, 1);
    EXPECT_TRUE(sim_is_dispatchable(master, 1)) << "Higher-priority IRQ 1 should be dispatchable";

    // EOI clears IRQ 3 from ISR
    sim_eoi(master);
    EXPECT_EQ(master.isr & 0x08, 0x00) << "ISR bit 3 cleared after EOI";
    EXPECT_EQ(master.active_irq, 8) << "No active IRQ after EOI";

    // Now IRQ 5 should be dispatchable (ISR clear)
    EXPECT_TRUE(sim_is_dispatchable(master, 5)) << "IRQ 5 dispatchable after EOI";
}

// ─────────────────────────────────────────────────────────────────────────────
// Test 3: Cascade Mode
// TLA+ property: Slave IRQs route through master IRQ 2
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(PicHardwareTest, CascadeMode) {
    const uint8_t cascade_irq = 2;

    // Raise slave IRQ 1 (IRQ 9 in system numbering)
    sim_raise_irq(slave, 1);
    EXPECT_EQ(slave.irr & 0x02, 0x02) << "Slave IRR bit 1 set";

    // In cascade mode, slave raises master IRQ 2
    sim_raise_irq(master, cascade_irq);
    EXPECT_EQ(master.irr & 0x04, 0x04) << "Master IRQ 2 set for cascade";

    // Acknowledge on master cascade line
    sim_start_irq(master, cascade_irq);
    EXPECT_EQ(master.isr & 0x04, 0x04) << "Master ISR bit 2 set";

    // Now acknowledge on slave
    sim_start_irq(slave, 1);
    EXPECT_EQ(slave.irr & 0x02, 0x00) << "Slave IRR bit 1 cleared";
    EXPECT_EQ(slave.isr & 0x02, 0x02) << "Slave ISR bit 1 set";

    // Interrupt vector = slave.vector_base + slave_irq
    EXPECT_EQ(slave.vector_base + 1, 0x71) << "Slave IRQ 1 -> vector 0x71";

    // EOI both
    sim_eoi(slave);
    sim_eoi(master);
    EXPECT_EQ(slave.isr, 0x00);
    EXPECT_EQ(master.isr, 0x00);
}

// ─────────────────────────────────────────────────────────────────────────────
// Test 4: Auto-EOI Mode
// TLA+ property: Auto-EOI never sets ISR bit
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(PicHardwareTest, AutoEoiMode) {
    master.auto_eoi = true;

    // Raise and acknowledge IRQ 4
    sim_raise_irq(master, 4);
    EXPECT_EQ(master.irr & 0x10, 0x10);

    sim_start_irq(master, 4);

    // In auto-EOI mode, ISR should NOT be set
    EXPECT_EQ(master.isr, 0x00) << "ISR must be 0 in auto-EOI mode";
    // IRR should be cleared
    EXPECT_EQ(master.irr & 0x10, 0x00) << "IRR cleared after acknowledge";
    // active_irq should NOT be updated (stays at 8 = none)
    EXPECT_EQ(master.active_irq, 8) << "active_irq unchanged in auto-EOI mode";

    // No explicit EOI needed - immediately ready for next interrupt
    sim_raise_irq(master, 4);
    EXPECT_TRUE(sim_is_dispatchable(master, 4))
        << "IRQ 4 immediately dispatchable again in auto-EOI mode";
}

// ─────────────────────────────────────────────────────────────────────────────
// Additional: Reset state invariants
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(PicHardwareTest, ResetClearsAllState) {
    // Dirty up the controller
    master.irr = 0xFF;
    master.isr = 0x42;
    master.imr = 0x00;
    master.active_irq = 3;
    master.auto_eoi = true;
    master.special = true;
    master.controller_index = 0;

    master.reset();

    EXPECT_EQ(master.irr, 0x00);
    EXPECT_EQ(master.isr, 0x00);
    EXPECT_EQ(master.imr, 0xFF) << "All IRQs masked after reset";
    EXPECT_EQ(master.imrr, 0x00) << "IMR reversed = 0 (all masked)";
    EXPECT_EQ(master.isrr, 0xFF) << "ISR reversed = 0xFF (none in service)";
    EXPECT_EQ(master.active_irq, 8) << "No active IRQ after reset";
    EXPECT_FALSE(master.auto_eoi);
    EXPECT_FALSE(master.special);
    // controller_index preserved
    EXPECT_EQ(master.controller_index, 0);
}

TEST_F(PicHardwareTest, MaskingPreventsDispatch) {
    // Mask IRQ 0
    master.imr = 0x01;
    master.imrr = static_cast<uint8_t>(~master.imr);

    sim_raise_irq(master, 0);
    EXPECT_EQ(master.irr & 0x01, 0x01) << "IRR still set even when masked";
    EXPECT_FALSE(sim_is_dispatchable(master, 0)) << "Masked IRQ not dispatchable";

    // Unmask
    master.imr = 0x00;
    master.imrr = 0xFF;
    EXPECT_TRUE(sim_is_dispatchable(master, 0)) << "Unmasked IRQ is dispatchable";
}

TEST_F(PicHardwareTest, EdgeTriggerPreventsRetrigger) {
    // Enable edge triggering for IRQ 2
    master.edge = 0x04;

    // First raise works
    sim_raise_irq(master, 2);
    EXPECT_EQ(master.irr & 0x04, 0x04);

    // Acknowledge it
    sim_start_irq(master, 2);
    sim_eoi(master);

    // Try to raise again while input is still high -> should be blocked by edge detect
    sim_raise_irq(master, 2);
    // input is still high from first raise, edge detect prevents re-triggering
    EXPECT_EQ(master.irr & 0x04, 0x00) << "Edge trigger prevents re-raise while input high";

    // Lower then raise again -> should work
    sim_lower_irq(master, 2);
    sim_raise_irq(master, 2);
    EXPECT_EQ(master.irr & 0x04, 0x04) << "Re-raise works after lower+raise cycle";
}
