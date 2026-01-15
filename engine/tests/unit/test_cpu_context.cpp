/**
 * @file test_cpu_context.cpp
 * @brief Unit tests for CpuContext class.
 */

#include <gtest/gtest.h>
#include <aibox/cpu_context.h>

using namespace aibox;

// ─────────────────────────────────────────────────────────────────────────────
// CpuFlags Tests
// ─────────────────────────────────────────────────────────────────────────────

class CpuFlagsTest : public ::testing::Test {
protected:
    CpuFlags flags_;
};

TEST_F(CpuFlagsTest, DefaultState) {
    CpuFlags flags;
    EXPECT_FALSE(flags.carry);
    EXPECT_FALSE(flags.zero);
    EXPECT_FALSE(flags.sign);
    EXPECT_TRUE(flags.interrupt);  // Enabled by default
    EXPECT_FALSE(flags.direction);
    EXPECT_FALSE(flags.overflow);
}

TEST_F(CpuFlagsTest, ToEflagsIncludesReservedBit) {
    CpuFlags flags;
    flags.reset();
    uint32_t eflags = flags.to_eflags();

    // Bit 1 is always 1
    EXPECT_EQ(eflags & 0x02, 0x02);
}

TEST_F(CpuFlagsTest, ToEflagsCarry) {
    flags_.reset();
    flags_.carry = true;
    EXPECT_EQ(flags_.to_eflags() & 0x01, 0x01);
}

TEST_F(CpuFlagsTest, ToEflagsParity) {
    flags_.reset();
    flags_.parity = true;
    EXPECT_EQ(flags_.to_eflags() & 0x04, 0x04);
}

TEST_F(CpuFlagsTest, ToEflagsZero) {
    flags_.reset();
    flags_.zero = true;
    EXPECT_EQ(flags_.to_eflags() & 0x40, 0x40);
}

TEST_F(CpuFlagsTest, ToEflagsSign) {
    flags_.reset();
    flags_.sign = true;
    EXPECT_EQ(flags_.to_eflags() & 0x80, 0x80);
}

TEST_F(CpuFlagsTest, ToEflagsInterrupt) {
    flags_.reset();
    flags_.interrupt = true;
    EXPECT_EQ(flags_.to_eflags() & 0x200, 0x200);
}

TEST_F(CpuFlagsTest, ToEflagsDirection) {
    flags_.reset();
    flags_.direction = true;
    EXPECT_EQ(flags_.to_eflags() & 0x400, 0x400);
}

TEST_F(CpuFlagsTest, ToEflagsOverflow) {
    flags_.reset();
    flags_.overflow = true;
    EXPECT_EQ(flags_.to_eflags() & 0x800, 0x800);
}

TEST_F(CpuFlagsTest, ToEflagsIopl) {
    flags_.reset();
    flags_.iopl = 3;
    EXPECT_EQ((flags_.to_eflags() >> 12) & 0x03, 0x03);
}

TEST_F(CpuFlagsTest, ToEflagsVirtual8086) {
    flags_.reset();
    flags_.virtual_8086 = true;
    EXPECT_EQ(flags_.to_eflags() & 0x20000, 0x20000);
}

TEST_F(CpuFlagsTest, FromEflagsRoundTrip) {
    // Set various flags
    uint32_t original = 0x00000246;  // Zero, Parity, Interrupt, reserved
    flags_.from_eflags(original);

    EXPECT_FALSE(flags_.carry);
    EXPECT_TRUE(flags_.parity);
    EXPECT_TRUE(flags_.zero);
    EXPECT_TRUE(flags_.interrupt);

    uint32_t converted = flags_.to_eflags();
    EXPECT_EQ(converted, original);
}

TEST_F(CpuFlagsTest, FromEflagsAllFlags) {
    // All common flags set (IOPL is bits 12-13, need 0x3000 for IOPL=3)
    uint32_t all = 0x00033FD7;  // Most flags including IOPL=3
    flags_.from_eflags(all);

    EXPECT_TRUE(flags_.carry);
    EXPECT_TRUE(flags_.parity);
    EXPECT_TRUE(flags_.auxiliary);
    EXPECT_TRUE(flags_.zero);
    EXPECT_TRUE(flags_.sign);
    EXPECT_TRUE(flags_.trap);
    EXPECT_TRUE(flags_.interrupt);
    EXPECT_TRUE(flags_.direction);
    EXPECT_TRUE(flags_.overflow);
    EXPECT_EQ(flags_.iopl, 3);
}

TEST_F(CpuFlagsTest, Reset) {
    flags_.carry = true;
    flags_.zero = true;
    flags_.sign = true;
    flags_.interrupt = false;

    flags_.reset();

    EXPECT_FALSE(flags_.carry);
    EXPECT_FALSE(flags_.zero);
    EXPECT_FALSE(flags_.sign);
    EXPECT_TRUE(flags_.interrupt);
}

// ─────────────────────────────────────────────────────────────────────────────
// SegmentRegister Tests
// ─────────────────────────────────────────────────────────────────────────────

class SegmentRegisterTest : public ::testing::Test {
protected:
    SegmentRegister seg_;
};

TEST_F(SegmentRegisterTest, DefaultValues) {
    EXPECT_EQ(seg_.selector, 0);
    EXPECT_EQ(seg_.base, 0u);
    EXPECT_EQ(seg_.limit, 0xFFFF);
}

TEST_F(SegmentRegisterTest, Reset) {
    seg_.selector = 0x1234;
    seg_.base = 0x12340;
    seg_.limit = 0x5678;

    seg_.reset(0xF000);

    EXPECT_EQ(seg_.selector, 0xF000);
    EXPECT_EQ(seg_.base, 0xF0000u);  // selector << 4
    EXPECT_EQ(seg_.limit, 0xFFFF);
}

TEST_F(SegmentRegisterTest, IsValidWhenPresentBitSet) {
    seg_.access = 0x80;  // Present bit
    EXPECT_TRUE(seg_.is_valid());
}

TEST_F(SegmentRegisterTest, IsValidWhenPresentBitClear) {
    seg_.access = 0x00;
    EXPECT_FALSE(seg_.is_valid());
}

TEST_F(SegmentRegisterTest, IsCodeSegment) {
    seg_.access = 0x98;  // Present, code segment
    EXPECT_TRUE(seg_.is_code());

    seg_.access = 0x92;  // Present, data segment
    EXPECT_FALSE(seg_.is_code());
}

TEST_F(SegmentRegisterTest, Dpl) {
    seg_.access = 0x00;  // DPL 0
    EXPECT_EQ(seg_.dpl(), 0);

    seg_.access = 0x60;  // DPL 3
    EXPECT_EQ(seg_.dpl(), 3);

    seg_.access = 0x20;  // DPL 1
    EXPECT_EQ(seg_.dpl(), 1);
}

// ─────────────────────────────────────────────────────────────────────────────
// CpuContext Tests
// ─────────────────────────────────────────────────────────────────────────────

class CpuContextTest : public ::testing::Test {
protected:
    CpuContext cpu_;

    void SetUp() override {
        cpu_.reset();
    }
};

TEST_F(CpuContextTest, ResetSetsInitialValues) {
    cpu_.eax = 0x12345678;
    cpu_.ebx = 0x87654321;
    cpu_.eip = 0x00001000;

    cpu_.reset();

    EXPECT_EQ(cpu_.eax, 0u);
    EXPECT_EQ(cpu_.ebx, 0u);
    EXPECT_EQ(cpu_.eip, 0xFFF0u);  // Reset vector
}

TEST_F(CpuContextTest, ResetSetsRealMode) {
    cpu_.cr0 = 0x00000001;  // Protected mode
    cpu_.reset();

    EXPECT_TRUE(cpu_.is_real_mode());
    EXPECT_FALSE(cpu_.is_protected_mode());
}

TEST_F(CpuContextTest, ResetInitializesSegments) {
    cpu_.reset();

    EXPECT_EQ(cpu_.cs.selector, 0xF000);
    EXPECT_EQ(cpu_.cs.base, 0xFFFF0000u);  // Special reset value
    EXPECT_EQ(cpu_.ds.selector, 0);
    EXPECT_EQ(cpu_.ds.base, 0u);
}

TEST_F(CpuContextTest, GeneralPurposeRegisterAliasing) {
    cpu_.eax = 0x12345678;

    EXPECT_EQ(cpu_.ax, 0x5678);
    EXPECT_EQ(cpu_.al, 0x78);
    EXPECT_EQ(cpu_.ah, 0x56);
}

TEST_F(CpuContextTest, RegisterModificationThroughAlias) {
    cpu_.eax = 0;
    cpu_.al = 0xAB;
    cpu_.ah = 0xCD;

    EXPECT_EQ(cpu_.ax, 0xCDAB);
    EXPECT_EQ(cpu_.eax, 0x0000CDAB);
}

TEST_F(CpuContextTest, IsProtectedMode) {
    EXPECT_FALSE(cpu_.is_protected_mode());

    cpu_.cr0 |= 0x01;  // Set PE bit
    EXPECT_TRUE(cpu_.is_protected_mode());
}

TEST_F(CpuContextTest, IsPagingEnabled) {
    EXPECT_FALSE(cpu_.is_paging_enabled());

    cpu_.cr0 |= 0x80000000;  // Set PG bit
    EXPECT_TRUE(cpu_.is_paging_enabled());
}

TEST_F(CpuContextTest, IsV86Mode) {
    EXPECT_FALSE(cpu_.is_v86_mode());

    cpu_.flags.virtual_8086 = true;
    EXPECT_TRUE(cpu_.is_v86_mode());
}

TEST_F(CpuContextTest, Cpl) {
    cpu_.cs.selector = 0x0008;  // Ring 0
    EXPECT_EQ(cpu_.cpl(), 0);

    cpu_.cs.selector = 0x001B;  // Ring 3
    EXPECT_EQ(cpu_.cpl(), 3);
}

TEST_F(CpuContextTest, DefaultAddressSizeRealMode) {
    cpu_.reset();
    EXPECT_EQ(cpu_.default_address_size(), 16);
}

TEST_F(CpuContextTest, DefaultAddressSizeV86Mode) {
    cpu_.flags.virtual_8086 = true;
    EXPECT_EQ(cpu_.default_address_size(), 16);
}

TEST_F(CpuContextTest, LinearAddress) {
    SegmentRegister seg;
    seg.base = 0x10000;

    EXPECT_EQ(cpu_.linear_address(seg, 0x1234), 0x11234u);
}

TEST_F(CpuContextTest, ControlRegistersInitialValues) {
    cpu_.reset();

    // CR0 should have ET bit set
    EXPECT_NE(cpu_.cr0 & 0x10, 0u);

    // Other control registers should be zero
    EXPECT_EQ(cpu_.cr2, 0u);
    EXPECT_EQ(cpu_.cr3, 0u);
    EXPECT_EQ(cpu_.cr4, 0u);
}

TEST_F(CpuContextTest, DebugRegistersInitialValues) {
    cpu_.reset();

    // DR0-DR3 should be zero
    for (int i = 0; i < 4; i++) {
        EXPECT_EQ(cpu_.dr[i], 0u);
    }

    // DR6 and DR7 have specific reset values
    EXPECT_EQ(cpu_.dr6, 0xFFFF0FF0u);
    EXPECT_EQ(cpu_.dr7, 0x00000400u);
}

TEST_F(CpuContextTest, IdtrRealModeDefault) {
    cpu_.reset();

    EXPECT_EQ(cpu_.idtr.base, 0u);
    EXPECT_EQ(cpu_.idtr.limit, 0x03FF);  // 256 vectors * 4 bytes - 1
}

TEST_F(CpuContextTest, HaltedState) {
    cpu_.reset();
    EXPECT_FALSE(cpu_.halted);

    cpu_.halted = true;
    EXPECT_TRUE(cpu_.halted);
}

TEST_F(CpuContextTest, ConfigDefaults) {
    EXPECT_TRUE(cpu_.config.nmi_enabled);
    EXPECT_TRUE(cpu_.config.fpu_enabled);
    EXPECT_EQ(cpu_.config.cycles_per_ms, 3000u);
}

// ─────────────────────────────────────────────────────────────────────────────
// CpuMode Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(CpuModeTest, EnumValues) {
    EXPECT_NE(CpuMode::Real, CpuMode::Protected16);
    EXPECT_NE(CpuMode::Protected16, CpuMode::Protected32);
    EXPECT_NE(CpuMode::Protected32, CpuMode::Virtual8086);
}

// ─────────────────────────────────────────────────────────────────────────────
// Edge Cases
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(CpuContextTest, EipAliasing) {
    cpu_.eip = 0xFFFF1234;
    EXPECT_EQ(cpu_.ip, 0x1234);
}

TEST_F(CpuContextTest, StackPointerAliasing) {
    cpu_.esp = 0x0000ABCD;
    EXPECT_EQ(cpu_.sp, 0xABCD);
}

TEST_F(CpuContextTest, AllGeneralPurposeRegisters) {
    cpu_.eax = 0x11111111;
    cpu_.ebx = 0x22222222;
    cpu_.ecx = 0x33333333;
    cpu_.edx = 0x44444444;
    cpu_.esi = 0x55555555;
    cpu_.edi = 0x66666666;
    cpu_.ebp = 0x77777777;
    cpu_.esp = 0x88888888;

    EXPECT_EQ(cpu_.eax, 0x11111111u);
    EXPECT_EQ(cpu_.ebx, 0x22222222u);
    EXPECT_EQ(cpu_.ecx, 0x33333333u);
    EXPECT_EQ(cpu_.edx, 0x44444444u);
    EXPECT_EQ(cpu_.esi, 0x55555555u);
    EXPECT_EQ(cpu_.edi, 0x66666666u);
    EXPECT_EQ(cpu_.ebp, 0x77777777u);
    EXPECT_EQ(cpu_.esp, 0x88888888u);
}

TEST_F(CpuContextTest, AllSegmentRegisters) {
    cpu_.cs.selector = 0x0008;
    cpu_.ds.selector = 0x0010;
    cpu_.es.selector = 0x0018;
    cpu_.fs.selector = 0x0020;
    cpu_.gs.selector = 0x0028;
    cpu_.ss.selector = 0x0030;

    EXPECT_EQ(cpu_.cs.selector, 0x0008);
    EXPECT_EQ(cpu_.ds.selector, 0x0010);
    EXPECT_EQ(cpu_.es.selector, 0x0018);
    EXPECT_EQ(cpu_.fs.selector, 0x0020);
    EXPECT_EQ(cpu_.gs.selector, 0x0028);
    EXPECT_EQ(cpu_.ss.selector, 0x0030);
}
