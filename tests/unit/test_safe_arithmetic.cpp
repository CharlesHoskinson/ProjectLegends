/**
 * @file test_safe_arithmetic.cpp
 * @brief Unit tests for safe_multiply overflow detection.
 */

#include <gtest/gtest.h>
#include <legends/safe_arithmetic.h>
#include <cstddef>
#include <climits>

using namespace legends;

// ─────────────────────────────────────────────────────────────────────────────
// safe_multiply() tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(SafeMultiply, SmallValues) {
    auto result = safe_multiply(3, 4);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(*result, 12u);
}

TEST(SafeMultiply, ZeroTimesAnything) {
    auto r1 = safe_multiply(0, 999);
    ASSERT_TRUE(r1.has_value());
    EXPECT_EQ(*r1, 0u);

    auto r2 = safe_multiply(999, 0);
    ASSERT_TRUE(r2.has_value());
    EXPECT_EQ(*r2, 0u);
}

TEST(SafeMultiply, OneTimesAnything) {
    auto result = safe_multiply(1, SIZE_MAX);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(*result, SIZE_MAX);
}

TEST(SafeMultiply, OverflowDetected) {
    auto result = safe_multiply(SIZE_MAX, 2);
    ASSERT_FALSE(result.has_value());
    EXPECT_EQ(result.error(), ErrorCode::InvalidState);
}

TEST(SafeMultiply, OverflowJustAboveMax) {
    // SIZE_MAX / 2 + 1 times 2 overflows
    std::size_t a = SIZE_MAX / 2 + 1;
    auto result = safe_multiply(a, 2);
    ASSERT_FALSE(result.has_value());
}

TEST(SafeMultiply, MaxNonOverflow) {
    // SIZE_MAX / 2 times 2 should not overflow (rounds down)
    std::size_t a = SIZE_MAX / 2;
    auto result = safe_multiply(a, 2);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(*result, a * 2);
}

TEST(SafeMultiply, LargeRealisticDimensions) {
    // 2048 * 2048 * 3 = 12,582,912 — should not overflow
    auto result = safe_multiply(2048u * 2048u, 3);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(*result, 12'582'912u);
}

TEST(SafeMultiply, BothMaxOverflow) {
    auto result = safe_multiply(SIZE_MAX, SIZE_MAX);
    ASSERT_FALSE(result.has_value());
}
