/**
 * @file test_memory.cpp
 * @brief Unit tests for GuestMemory and MemoryView classes.
 */

#include <gtest/gtest.h>
#include <legends/memory.h>
#include <numeric>
#include <vector>

using namespace legends;

// ─────────────────────────────────────────────────────────────────────────────
// GuestMemory Construction Tests
// ─────────────────────────────────────────────────────────────────────────────

class GuestMemoryTest : public ::testing::Test {
protected:
    static constexpr size_t TEST_SIZE = 1024 * 1024;  // 1MB

    void SetUp() override {
        mem_ = std::make_unique<GuestMemory>(TEST_SIZE);
    }

    std::unique_ptr<GuestMemory> mem_;
};

TEST_F(GuestMemoryTest, ConstructionAllocatesMemory) {
    EXPECT_NE(mem_->data(), nullptr);
    EXPECT_EQ(mem_->size(), TEST_SIZE);
    EXPECT_TRUE(mem_->valid());
}

TEST_F(GuestMemoryTest, MemoryIsZeroInitialized) {
    // REQ-MEM-004: Zero initialization
    for (size_t i = 0; i < 1000; i += 100) {
        EXPECT_EQ(mem_->read8(static_cast<uint32_t>(i)), 0);
    }
}

TEST_F(GuestMemoryTest, DefaultConstructorCreatesInvalid) {
    GuestMemory empty;
    EXPECT_FALSE(empty.valid());
    EXPECT_EQ(empty.size(), 0u);
    EXPECT_EQ(empty.data(), nullptr);
}

TEST_F(GuestMemoryTest, LargeAllocationSucceeds) {
    // 16MB - typical for DOS
    auto large = std::make_unique<GuestMemory>(16 * 1024 * 1024);
    EXPECT_TRUE(large->valid());
    EXPECT_EQ(large->size(), 16u * 1024 * 1024);
}

// ─────────────────────────────────────────────────────────────────────────────
// Read/Write Operations
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(GuestMemoryTest, Write8Read8Roundtrip) {
    mem_->write8(0x1000, 0x42);
    EXPECT_EQ(mem_->read8(0x1000), 0x42);
}

TEST_F(GuestMemoryTest, Write16Read16Roundtrip) {
    mem_->write16(0x2000, 0xABCD);
    EXPECT_EQ(mem_->read16(0x2000), 0xABCD);
}

TEST_F(GuestMemoryTest, Write32Read32Roundtrip) {
    mem_->write32(0x3000, 0xDEADBEEF);
    EXPECT_EQ(mem_->read32(0x3000), 0xDEADBEEF);
}

TEST_F(GuestMemoryTest, MultiByteIsLittleEndian) {
    mem_->write32(0x4000, 0x04030201);
    EXPECT_EQ(mem_->read8(0x4000), 0x01);
    EXPECT_EQ(mem_->read8(0x4001), 0x02);
    EXPECT_EQ(mem_->read8(0x4002), 0x03);
    EXPECT_EQ(mem_->read8(0x4003), 0x04);
}

TEST_F(GuestMemoryTest, Write16OverlappingRead8) {
    mem_->write16(0x5000, 0x1234);
    EXPECT_EQ(mem_->read8(0x5000), 0x34);
    EXPECT_EQ(mem_->read8(0x5001), 0x12);
}

// ─────────────────────────────────────────────────────────────────────────────
// Unchecked Operations
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(GuestMemoryTest, UncheckedWrite8Read8) {
    mem_->write8_unchecked(0x6000, 0xAB);
    EXPECT_EQ(mem_->read8_unchecked(0x6000), 0xAB);
}

TEST_F(GuestMemoryTest, UncheckedWrite16Read16) {
    mem_->write16_unchecked(0x7000, 0x5678);
    EXPECT_EQ(mem_->read16_unchecked(0x7000), 0x5678);
}

TEST_F(GuestMemoryTest, UncheckedWrite32Read32) {
    mem_->write32_unchecked(0x8000, 0xCAFEBABE);
    EXPECT_EQ(mem_->read32_unchecked(0x8000), 0xCAFEBABE);
}

// ─────────────────────────────────────────────────────────────────────────────
// Bounds Checking (Debug Builds)
// ─────────────────────────────────────────────────────────────────────────────

#if !defined(NDEBUG) || defined(LEGENDS_ALWAYS_BOUNDS_CHECK)

TEST_F(GuestMemoryTest, Read8OutOfBoundsThrows) {
    EXPECT_THROW(mem_->read8(static_cast<uint32_t>(TEST_SIZE)), MemoryAccessException);
    EXPECT_THROW(mem_->read8(static_cast<uint32_t>(TEST_SIZE + 1000)), MemoryAccessException);
}

TEST_F(GuestMemoryTest, Write8OutOfBoundsThrows) {
    EXPECT_THROW(mem_->write8(static_cast<uint32_t>(TEST_SIZE), 0x42), MemoryAccessException);
}

TEST_F(GuestMemoryTest, Read16CrossingBoundaryThrows) {
    EXPECT_THROW(mem_->read16(static_cast<uint32_t>(TEST_SIZE - 1)), MemoryAccessException);
}

TEST_F(GuestMemoryTest, Read32CrossingBoundaryThrows) {
    EXPECT_THROW(mem_->read32(static_cast<uint32_t>(TEST_SIZE - 3)), MemoryAccessException);
}

TEST_F(GuestMemoryTest, ExceptionContainsAddress) {
    try {
        mem_->read8(0xFFFFFFFF);
        FAIL() << "Expected MemoryAccessException";
    } catch (const MemoryAccessException& e) {
        EXPECT_EQ(e.address(), 0xFFFFFFFF);
    }
}

TEST_F(GuestMemoryTest, ExceptionContainsSize) {
    try {
        mem_->read32(static_cast<uint32_t>(TEST_SIZE - 2));
        FAIL() << "Expected MemoryAccessException";
    } catch (const MemoryAccessException& e) {
        EXPECT_EQ(e.size(), 4u);
    }
}

#endif

// ─────────────────────────────────────────────────────────────────────────────
// Block Operations
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(GuestMemoryTest, WriteBlockReadBlockRoundtrip) {
    std::vector<uint8_t> src = {0x01, 0x02, 0x03, 0x04, 0x05};
    std::vector<uint8_t> dest(5);

    mem_->write_block(0x9000, src.data(), src.size());
    mem_->read_block(0x9000, dest.data(), dest.size());

    EXPECT_EQ(src, dest);
}

TEST_F(GuestMemoryTest, WriteBlockLargeTransfer) {
    std::vector<uint8_t> data(64 * 1024);  // 64KB
    std::iota(data.begin(), data.end(), static_cast<uint8_t>(0));

    mem_->write_block(0, data.data(), data.size());

    for (size_t i = 0; i < data.size(); i += 1000) {
        EXPECT_EQ(mem_->read8(static_cast<uint32_t>(i)), static_cast<uint8_t>(i));
    }
}

TEST_F(GuestMemoryTest, FillMemory) {
    mem_->fill(0xA000, 0xAA, 100);

    for (uint32_t i = 0; i < 100; i++) {
        EXPECT_EQ(mem_->read8(0xA000 + i), 0xAA);
    }
}

TEST_F(GuestMemoryTest, CopyWithinMemory) {
    std::vector<uint8_t> data = {1, 2, 3, 4, 5};
    mem_->write_block(0xB000, data.data(), data.size());

    mem_->copy(0xB100, 0xB000, 5);

    for (size_t i = 0; i < 5; i++) {
        EXPECT_EQ(mem_->read8(0xB100 + static_cast<uint32_t>(i)), data[i]);
    }
}

TEST_F(GuestMemoryTest, CopyOverlapping) {
    // Write 1,2,3,4,5 at 0xC000
    uint8_t data[] = {1, 2, 3, 4, 5};
    mem_->write_block(0xC000, data, 5);

    // Copy with overlap: src=0xC000, dest=0xC002
    mem_->copy(0xC002, 0xC000, 5);

    // Should use memmove semantics
    EXPECT_EQ(mem_->read8(0xC002), 1);
    EXPECT_EQ(mem_->read8(0xC003), 2);
    EXPECT_EQ(mem_->read8(0xC006), 5);
}

// ─────────────────────────────────────────────────────────────────────────────
// Move Semantics
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(GuestMemoryTest, MoveConstructorTransfersOwnership) {
    mem_->write8(0x100, 0x42);
    uint8_t* original_ptr = mem_->data();

    GuestMemory moved(std::move(*mem_));

    EXPECT_EQ(moved.data(), original_ptr);
    EXPECT_EQ(moved.read8(0x100), 0x42);
    EXPECT_EQ(mem_->size(), 0u);  // Source invalidated
    EXPECT_FALSE(mem_->valid());
}

TEST_F(GuestMemoryTest, MoveAssignmentTransfersOwnership) {
    GuestMemory other(512);
    mem_->write8(0x100, 0x42);

    other = std::move(*mem_);

    EXPECT_EQ(other.size(), TEST_SIZE);
    EXPECT_EQ(other.read8(0x100), 0x42);
    EXPECT_FALSE(mem_->valid());
}

// ─────────────────────────────────────────────────────────────────────────────
// Bounds Checking Query
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(GuestMemoryTest, InBoundsReturnsTrueForValid) {
    EXPECT_TRUE(mem_->in_bounds(0, 1));
    EXPECT_TRUE(mem_->in_bounds(0x1000, 4));
    EXPECT_TRUE(mem_->in_bounds(static_cast<uint32_t>(TEST_SIZE - 1), 1));
}

TEST_F(GuestMemoryTest, InBoundsReturnsFalseForInvalid) {
    EXPECT_FALSE(mem_->in_bounds(static_cast<uint32_t>(TEST_SIZE), 1));
    EXPECT_FALSE(mem_->in_bounds(static_cast<uint32_t>(TEST_SIZE - 1), 2));
    EXPECT_FALSE(mem_->in_bounds(0xFFFFFFFF, 1));
}

// ─────────────────────────────────────────────────────────────────────────────
// Span Interface
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(GuestMemoryTest, AsSpanReturnsCorrectSize) {
    auto span = mem_->as_span();
    EXPECT_EQ(span.size(), TEST_SIZE);
    EXPECT_EQ(span.data(), mem_->data());
}

TEST_F(GuestMemoryTest, SubspanReturnsCorrectRegion) {
    mem_->write8(0x1000, 0x42);
    mem_->write8(0x1001, 0x43);

    auto sub = mem_->subspan(0x1000, 2);

    EXPECT_EQ(sub.size(), 2u);
    EXPECT_EQ(sub[0], 0x42);
    EXPECT_EQ(sub[1], 0x43);
}

TEST_F(GuestMemoryTest, ConstAsSpan) {
    mem_->write8(0x2000, 0x99);

    const GuestMemory& const_mem = *mem_;
    auto span = const_mem.as_span();

    EXPECT_EQ(span.size(), TEST_SIZE);
    EXPECT_EQ(span[0x2000], 0x99);
}

// ─────────────────────────────────────────────────────────────────────────────
// MemoryView Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(MemoryViewTest, ConstructFromPointerAndSize) {
    uint8_t buffer[100] = {0};
    buffer[50] = 0xAB;

    MemoryView view(buffer, 100);

    EXPECT_EQ(view.data(), buffer);
    EXPECT_EQ(view.size(), 100u);
    EXPECT_EQ(view[50], 0xAB);
}

TEST(MemoryViewTest, ConstructFromGuestMemory) {
    GuestMemory mem(1024);
    mem.write8(100, 0x42);

    MemoryView view(mem);

    EXPECT_EQ(view.data(), mem.data());
    EXPECT_EQ(view.size(), mem.size());
    EXPECT_EQ(view[100], 0x42);
}

TEST(MemoryViewTest, DefaultConstructorCreatesEmpty) {
    MemoryView view;

    EXPECT_EQ(view.data(), nullptr);
    EXPECT_EQ(view.size(), 0u);
    EXPECT_TRUE(view.empty());
    EXPECT_FALSE(view.valid());
}

TEST(MemoryViewTest, SubviewReturnsCorrectRegion) {
    uint8_t buffer[100];
    for (int i = 0; i < 100; i++) buffer[i] = static_cast<uint8_t>(i);

    MemoryView view(buffer, 100);
    auto sub = view.subview(10, 5);

    EXPECT_EQ(sub.size(), 5u);
    EXPECT_EQ(sub[0], 10);
    EXPECT_EQ(sub[4], 14);
}

TEST(MemoryViewTest, SubviewBeyondEndReturnsEmpty) {
    uint8_t buffer[100];
    MemoryView view(buffer, 100);

    auto sub = view.subview(100, 10);

    EXPECT_EQ(sub.size(), 0u);
    EXPECT_FALSE(sub.valid());
}

TEST(MemoryViewTest, ModificationThroughView) {
    uint8_t buffer[10] = {0};
    MemoryView view(buffer, 10);

    view[5] = 0xFF;

    EXPECT_EQ(buffer[5], 0xFF);
}

TEST(MemoryViewTest, AsSpan) {
    uint8_t buffer[50];
    MemoryView view(buffer, 50);

    auto span = view.as_span();

    EXPECT_EQ(span.size(), 50u);
    EXPECT_EQ(span.data(), buffer);
}

// ─────────────────────────────────────────────────────────────────────────────
// MemoryRegion Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(MemoryRegionTest, Construction) {
    MemoryRegion region("Conventional", 0x00000, 640 * 1024, MemoryAccess::ReadWrite);

    EXPECT_EQ(region.name(), "Conventional");
    EXPECT_EQ(region.base(), 0x00000u);
    EXPECT_EQ(region.size(), 640u * 1024);
    EXPECT_EQ(region.end(), 640u * 1024);
}

TEST(MemoryRegionTest, ContainsAddress) {
    MemoryRegion region("Test", 0x1000, 0x100);

    EXPECT_TRUE(region.contains(0x1000));
    EXPECT_TRUE(region.contains(0x1050));
    EXPECT_TRUE(region.contains(0x10FF));
    EXPECT_FALSE(region.contains(0x0FFF));
    EXPECT_FALSE(region.contains(0x1100));
}

TEST(MemoryRegionTest, OverlapsRange) {
    MemoryRegion region("Test", 0x1000, 0x100);

    // Fully inside
    EXPECT_TRUE(region.overlaps(0x1020, 0x20));

    // Partial overlap at start
    EXPECT_TRUE(region.overlaps(0x0F80, 0x100));

    // Partial overlap at end
    EXPECT_TRUE(region.overlaps(0x1080, 0x100));

    // Completely before
    EXPECT_FALSE(region.overlaps(0x0000, 0x100));

    // Completely after
    EXPECT_FALSE(region.overlaps(0x2000, 0x100));
}

TEST(MemoryRegionTest, AccessFlags) {
    MemoryRegion ro("ROM", 0xF0000, 0x10000, MemoryAccess::Read);
    MemoryRegion rw("RAM", 0x00000, 0xA0000, MemoryAccess::ReadWrite);
    MemoryRegion exec("Code", 0x10000, 0x1000, MemoryAccess::All);

    EXPECT_TRUE(ro.can_read());
    EXPECT_FALSE(ro.can_write());
    EXPECT_FALSE(ro.can_execute());

    EXPECT_TRUE(rw.can_read());
    EXPECT_TRUE(rw.can_write());
    EXPECT_FALSE(rw.can_execute());

    EXPECT_TRUE(exec.can_read());
    EXPECT_TRUE(exec.can_write());
    EXPECT_TRUE(exec.can_execute());
}

// ─────────────────────────────────────────────────────────────────────────────
// Stress Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(GuestMemoryTest, RepeatedCreateDestroy) {
    for (int i = 0; i < 100; i++) {
        auto mem = std::make_unique<GuestMemory>(64 * 1024);
        EXPECT_TRUE(mem->valid());
        mem->write32(0, static_cast<uint32_t>(i));
        EXPECT_EQ(mem->read32(0), static_cast<uint32_t>(i));
        // Implicit destruction
    }
    // No leaks (ASan will catch)
}

TEST_F(GuestMemoryTest, SequentialWrites) {
    // Write to every 4KB page
    for (size_t page = 0; page < TEST_SIZE / 4096; page++) {
        uint32_t addr = static_cast<uint32_t>(page * 4096);
        mem_->write32(addr, static_cast<uint32_t>(page));
    }

    // Verify
    for (size_t page = 0; page < TEST_SIZE / 4096; page++) {
        uint32_t addr = static_cast<uint32_t>(page * 4096);
        EXPECT_EQ(mem_->read32(addr), static_cast<uint32_t>(page));
    }
}

