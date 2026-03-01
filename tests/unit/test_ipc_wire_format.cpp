// SPDX-License-Identifier: MIT
#include <gtest/gtest.h>
#include <legends_ipc/wire_format.h>
#include <array>
#include <cstdint>
#include <limits>

using namespace legends_ipc::wire;

class IpcWireFormatTest : public ::testing::Test {
protected:
    std::array<uint8_t, 64> buf_{};
    std::span<uint8_t> buf() { return buf_; }
    std::span<const uint8_t> cbuf() { return buf_; }
};

// ── u8 round-trip ───────────────────────────────────────────────────────────

TEST_F(IpcWireFormatTest, U8RoundTrip_Zero) {
    write_u8(buf(), 0, 0);
    EXPECT_EQ(read_u8(cbuf(), 0), 0);
}

TEST_F(IpcWireFormatTest, U8RoundTrip_Max) {
    write_u8(buf(), 0, 255);
    EXPECT_EQ(read_u8(cbuf(), 0), 255);
}

TEST_F(IpcWireFormatTest, U8RoundTrip_Mid) {
    write_u8(buf(), 3, 0x42);
    EXPECT_EQ(read_u8(cbuf(), 3), 0x42);
}

// ── u16 round-trip ──────────────────────────────────────────────────────────

TEST_F(IpcWireFormatTest, U16RoundTrip_Zero) {
    write_u16_le(buf(), 0, 0);
    EXPECT_EQ(read_u16_le(cbuf(), 0), 0);
}

TEST_F(IpcWireFormatTest, U16RoundTrip_Max) {
    write_u16_le(buf(), 0, 0xFFFF);
    EXPECT_EQ(read_u16_le(cbuf(), 0), 0xFFFF);
}

TEST_F(IpcWireFormatTest, U16RoundTrip_Value) {
    write_u16_le(buf(), 2, 0x1234);
    EXPECT_EQ(read_u16_le(cbuf(), 2), 0x1234);
    // Verify little-endian byte order
    EXPECT_EQ(buf_[2], 0x34);
    EXPECT_EQ(buf_[3], 0x12);
}

// ── u32 round-trip ──────────────────────────────────────────────────────────

TEST_F(IpcWireFormatTest, U32RoundTrip_Zero) {
    write_u32_le(buf(), 0, 0);
    EXPECT_EQ(read_u32_le(cbuf(), 0), 0u);
}

TEST_F(IpcWireFormatTest, U32RoundTrip_Max) {
    write_u32_le(buf(), 0, 0xFFFFFFFF);
    EXPECT_EQ(read_u32_le(cbuf(), 0), 0xFFFFFFFF);
}

TEST_F(IpcWireFormatTest, U32RoundTrip_Value) {
    write_u32_le(buf(), 4, 0xDEADBEEF);
    EXPECT_EQ(read_u32_le(cbuf(), 4), 0xDEADBEEF);
    // Verify little-endian byte order
    EXPECT_EQ(buf_[4], 0xEF);
    EXPECT_EQ(buf_[5], 0xBE);
    EXPECT_EQ(buf_[6], 0xAD);
    EXPECT_EQ(buf_[7], 0xDE);
}

// ── u64 round-trip ──────────────────────────────────────────────────────────

TEST_F(IpcWireFormatTest, U64RoundTrip_Zero) {
    write_u64_le(buf(), 0, 0);
    EXPECT_EQ(read_u64_le(cbuf(), 0), 0ull);
}

TEST_F(IpcWireFormatTest, U64RoundTrip_Max) {
    write_u64_le(buf(), 0, std::numeric_limits<uint64_t>::max());
    EXPECT_EQ(read_u64_le(cbuf(), 0), std::numeric_limits<uint64_t>::max());
}

TEST_F(IpcWireFormatTest, U64RoundTrip_Value) {
    write_u64_le(buf(), 8, 0x0102030405060708ULL);
    EXPECT_EQ(read_u64_le(cbuf(), 8), 0x0102030405060708ULL);
}

// ── Signed round-trip ───────────────────────────────────────────────────────

TEST_F(IpcWireFormatTest, I16RoundTrip_Negative) {
    write_i16_le(buf(), 0, -1234);
    EXPECT_EQ(read_i16_le(cbuf(), 0), -1234);
}

TEST_F(IpcWireFormatTest, I16RoundTrip_Min) {
    write_i16_le(buf(), 0, std::numeric_limits<int16_t>::min());
    EXPECT_EQ(read_i16_le(cbuf(), 0), std::numeric_limits<int16_t>::min());
}

TEST_F(IpcWireFormatTest, I32RoundTrip_Negative) {
    write_i32_le(buf(), 0, -999999);
    EXPECT_EQ(read_i32_le(cbuf(), 0), -999999);
}

TEST_F(IpcWireFormatTest, I32RoundTrip_Min) {
    write_i32_le(buf(), 0, std::numeric_limits<int32_t>::min());
    EXPECT_EQ(read_i32_le(cbuf(), 0), std::numeric_limits<int32_t>::min());
}

TEST_F(IpcWireFormatTest, I64RoundTrip_Negative) {
    write_i64_le(buf(), 0, -123456789012345LL);
    EXPECT_EQ(read_i64_le(cbuf(), 0), -123456789012345LL);
}

TEST_F(IpcWireFormatTest, I64RoundTrip_Min) {
    write_i64_le(buf(), 0, std::numeric_limits<int64_t>::min());
    EXPECT_EQ(read_i64_le(cbuf(), 0), std::numeric_limits<int64_t>::min());
}

// ── Bool round-trip ─────────────────────────────────────────────────────────

TEST_F(IpcWireFormatTest, BoolRoundTrip_True) {
    write_bool(buf(), 0, true);
    EXPECT_TRUE(read_bool(cbuf(), 0));
}

TEST_F(IpcWireFormatTest, BoolRoundTrip_False) {
    write_bool(buf(), 0, false);
    EXPECT_FALSE(read_bool(cbuf(), 0));
}

TEST_F(IpcWireFormatTest, BoolRead_NonzeroIsTrue) {
    buf_[0] = 42;
    EXPECT_TRUE(read_bool(cbuf(), 0));
}

// ── Offset independence ─────────────────────────────────────────────────────

TEST_F(IpcWireFormatTest, MultipleValuesAtDifferentOffsets) {
    write_u8(buf(), 0, 0xAA);
    write_u16_le(buf(), 1, 0xBBCC);
    write_u32_le(buf(), 3, 0xDDEEFF00);
    write_u64_le(buf(), 7, 0x1122334455667788ULL);

    EXPECT_EQ(read_u8(cbuf(), 0), 0xAA);
    EXPECT_EQ(read_u16_le(cbuf(), 1), 0xBBCC);
    EXPECT_EQ(read_u32_le(cbuf(), 3), 0xDDEEFF00);
    EXPECT_EQ(read_u64_le(cbuf(), 7), 0x1122334455667788ULL);
}
