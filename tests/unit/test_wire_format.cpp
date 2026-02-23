/**
 * @file test_wire_format.cpp
 * @brief Unit tests for portable LE wire format helpers.
 */

#include <gtest/gtest.h>
#include <dosbox/wire_format.h>
#include <cstring>

using namespace dosbox::wire;

TEST(WireFormat, U8RoundTrip) {
    uint8_t buf[1]{};
    write_u8(buf, 0xAB);
    EXPECT_EQ(read_u8(buf), 0xAB);
}

TEST(WireFormat, U16LEWriteRead) {
    uint8_t buf[2]{};
    write_u16_le(buf, 0xCAFE);
    EXPECT_EQ(buf[0], 0xFE);
    EXPECT_EQ(buf[1], 0xCA);
    EXPECT_EQ(read_u16_le(buf), 0xCAFE);
}

TEST(WireFormat, U32LEWriteRead) {
    uint8_t buf[4]{};
    write_u32_le(buf, 0xDEADBEEF);
    EXPECT_EQ(buf[0], 0xEF);
    EXPECT_EQ(buf[1], 0xBE);
    EXPECT_EQ(buf[2], 0xAD);
    EXPECT_EQ(buf[3], 0xDE);
    EXPECT_EQ(read_u32_le(buf), 0xDEADBEEF);
}

TEST(WireFormat, U64LEWriteRead) {
    uint8_t buf[8]{};
    write_u64_le(buf, 0x0102030405060708ULL);
    EXPECT_EQ(buf[0], 0x08);
    EXPECT_EQ(buf[7], 0x01);
    EXPECT_EQ(read_u64_le(buf), 0x0102030405060708ULL);
}

TEST(WireFormat, I16LERoundTrip) {
    uint8_t buf[2]{};
    write_i16_le(buf, -1234);
    EXPECT_EQ(read_i16_le(buf), -1234);
}

TEST(WireFormat, I32LERoundTrip) {
    uint8_t buf[4]{};
    write_i32_le(buf, -42);
    EXPECT_EQ(read_i32_le(buf), -42);
}

TEST(WireFormat, I64LERoundTrip) {
    uint8_t buf[8]{};
    write_i64_le(buf, -9999999999LL);
    EXPECT_EQ(read_i64_le(buf), -9999999999LL);
}

TEST(WireFormat, BoolRoundTrip) {
    uint8_t buf[1]{};
    write_bool(buf, true);
    EXPECT_TRUE(read_bool(buf));
    write_bool(buf, false);
    EXPECT_FALSE(read_bool(buf));
}

TEST(WireFormat, ZeroValues) {
    uint8_t buf[8]{};
    std::memset(buf, 0xFF, sizeof(buf));

    write_u16_le(buf, 0);
    EXPECT_EQ(read_u16_le(buf), 0u);

    write_u32_le(buf, 0);
    EXPECT_EQ(read_u32_le(buf), 0u);

    write_u64_le(buf, 0);
    EXPECT_EQ(read_u64_le(buf), 0u);
}

TEST(WireFormat, MaxValues) {
    uint8_t buf[8]{};

    write_u16_le(buf, 0xFFFF);
    EXPECT_EQ(read_u16_le(buf), 0xFFFF);

    write_u32_le(buf, 0xFFFFFFFF);
    EXPECT_EQ(read_u32_le(buf), 0xFFFFFFFF);

    write_u64_le(buf, 0xFFFFFFFFFFFFFFFFULL);
    EXPECT_EQ(read_u64_le(buf), 0xFFFFFFFFFFFFFFFFULL);
}
