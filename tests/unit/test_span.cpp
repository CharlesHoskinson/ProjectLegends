/**
 * @file test_span.cpp
 * @brief Unit tests for std::span usage patterns.
 *
 * Tests verify that our usage patterns work correctly with std::span.
 */

#include <gtest/gtest.h>
#include <span>
#include <array>
#include <vector>

// ─────────────────────────────────────────────────────────────────────────────
// Construction Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(StdSpanTest, DefaultConstructorCreatesEmpty) {
    std::span<int> span;

    EXPECT_EQ(span.data(), nullptr);
    EXPECT_EQ(span.size(), 0u);
    EXPECT_TRUE(span.empty());
}

TEST(StdSpanTest, PointerSizeConstructor) {
    int arr[] = {1, 2, 3, 4, 5};
    std::span<int> span(arr, 5);

    EXPECT_EQ(span.data(), arr);
    EXPECT_EQ(span.size(), 5u);
    EXPECT_FALSE(span.empty());
}

TEST(StdSpanTest, PointerRangeConstructor) {
    int arr[] = {1, 2, 3, 4, 5};
    std::span<int> span(arr, arr + 5);

    EXPECT_EQ(span.size(), 5u);
    EXPECT_EQ(span[0], 1);
    EXPECT_EQ(span[4], 5);
}

TEST(StdSpanTest, CArrayConstructor) {
    int arr[] = {10, 20, 30};
    std::span<int> span(arr);

    EXPECT_EQ(span.size(), 3u);
    EXPECT_EQ(span[0], 10);
    EXPECT_EQ(span[2], 30);
}

TEST(StdSpanTest, StdArrayConstructor) {
    std::array<int, 4> arr = {1, 2, 3, 4};
    std::span<int> span(arr);

    EXPECT_EQ(span.size(), 4u);
    EXPECT_EQ(span[0], 1);
    EXPECT_EQ(span[3], 4);
}

TEST(StdSpanTest, VectorConstructor) {
    std::vector<int> vec = {1, 2, 3, 4};
    std::span<int> span(vec);

    EXPECT_EQ(span.size(), 4u);
    EXPECT_EQ(span[0], 1);
    EXPECT_EQ(span[3], 4);
}

TEST(StdSpanTest, CopyConstructor) {
    int arr[] = {1, 2, 3};
    std::span<int> span1(arr);
    std::span<int> span2(span1);

    EXPECT_EQ(span2.data(), span1.data());
    EXPECT_EQ(span2.size(), span1.size());
}

// ─────────────────────────────────────────────────────────────────────────────
// Element Access Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(StdSpanTest, SubscriptOperator) {
    int arr[] = {10, 20, 30, 40};
    std::span<int> span(arr);

    EXPECT_EQ(span[0], 10);
    EXPECT_EQ(span[1], 20);
    EXPECT_EQ(span[3], 40);
}

TEST(StdSpanTest, SubscriptOperatorModifies) {
    int arr[] = {1, 2, 3};
    std::span<int> span(arr);

    span[1] = 42;

    EXPECT_EQ(arr[1], 42);
}

TEST(StdSpanTest, FrontAndBack) {
    int arr[] = {10, 20, 30};
    std::span<int> span(arr);

    EXPECT_EQ(span.front(), 10);
    EXPECT_EQ(span.back(), 30);
}

TEST(StdSpanTest, DataReturnsPointer) {
    int arr[] = {1, 2, 3};
    std::span<int> span(arr);

    EXPECT_EQ(span.data(), &arr[0]);
}

// ─────────────────────────────────────────────────────────────────────────────
// Size Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(StdSpanTest, SizeReturnsCount) {
    int arr[] = {1, 2, 3, 4, 5, 6, 7};
    std::span<int> span(arr);

    EXPECT_EQ(span.size(), 7u);
}

TEST(StdSpanTest, SizeBytesReturnsCorrectValue) {
    int arr[] = {1, 2, 3, 4};
    std::span<int> span(arr);

    EXPECT_EQ(span.size_bytes(), 4 * sizeof(int));
}

TEST(StdSpanTest, EmptyReturnsTrueForEmpty) {
    std::span<int> span;
    EXPECT_TRUE(span.empty());
}

TEST(StdSpanTest, EmptyReturnsFalseForNonEmpty) {
    int arr[] = {1};
    std::span<int> span(arr);

    EXPECT_FALSE(span.empty());
}

// ─────────────────────────────────────────────────────────────────────────────
// Iterator Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(StdSpanTest, BeginEnd) {
    int arr[] = {1, 2, 3};
    std::span<int> span(arr);

    // Compare via dereferencing since iterator type may not be raw pointer
    EXPECT_EQ(&*span.begin(), &arr[0]);
    EXPECT_EQ(span.end() - span.begin(), 3);
}

TEST(StdSpanTest, RangeBasedFor) {
    int arr[] = {1, 2, 3, 4};
    std::span<int> span(arr);

    int sum = 0;
    for (int x : span) {
        sum += x;
    }

    EXPECT_EQ(sum, 10);
}

TEST(StdSpanTest, RangeBasedForModifies) {
    int arr[] = {1, 2, 3};
    std::span<int> span(arr);

    for (int& x : span) {
        x *= 2;
    }

    EXPECT_EQ(arr[0], 2);
    EXPECT_EQ(arr[1], 4);
    EXPECT_EQ(arr[2], 6);
}

// ─────────────────────────────────────────────────────────────────────────────
// Subview Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(StdSpanTest, SubspanWithOffsetAndCount) {
    int arr[] = {0, 1, 2, 3, 4, 5};
    std::span<int> span(arr);

    auto sub = span.subspan(2, 3);

    EXPECT_EQ(sub.size(), 3u);
    EXPECT_EQ(sub[0], 2);
    EXPECT_EQ(sub[1], 3);
    EXPECT_EQ(sub[2], 4);
}

TEST(StdSpanTest, SubspanWithOffsetOnly) {
    int arr[] = {0, 1, 2, 3, 4};
    std::span<int> span(arr);

    auto sub = span.subspan(2);

    EXPECT_EQ(sub.size(), 3u);
    EXPECT_EQ(sub[0], 2);
    EXPECT_EQ(sub[2], 4);
}

TEST(StdSpanTest, FirstN) {
    int arr[] = {10, 20, 30, 40, 50};
    std::span<int> span(arr);

    auto first3 = span.first(3);

    EXPECT_EQ(first3.size(), 3u);
    EXPECT_EQ(first3[0], 10);
    EXPECT_EQ(first3[2], 30);
}

TEST(StdSpanTest, LastN) {
    int arr[] = {10, 20, 30, 40, 50};
    std::span<int> span(arr);

    auto last2 = span.last(2);

    EXPECT_EQ(last2.size(), 2u);
    EXPECT_EQ(last2[0], 40);
    EXPECT_EQ(last2[1], 50);
}

// ─────────────────────────────────────────────────────────────────────────────
// Const Span Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(StdSpanTest, ConstSpanFromConstArray) {
    const int arr[] = {1, 2, 3};
    std::span<const int> span(arr);

    EXPECT_EQ(span.size(), 3u);
    EXPECT_EQ(span[0], 1);
}

TEST(StdSpanTest, ConstSpanFromMutableArray) {
    int arr[] = {1, 2, 3};
    std::span<const int> span(arr, 3);

    EXPECT_EQ(span[0], 1);
    // span[0] = 42;  // Should not compile
}

TEST(StdSpanTest, ImplicitConversionToConst) {
    int arr[] = {1, 2, 3};
    std::span<int> mutable_span(arr);
    std::span<const int> const_span = mutable_span;

    EXPECT_EQ(const_span.size(), 3u);
    EXPECT_EQ(const_span[0], 1);
}

// ─────────────────────────────────────────────────────────────────────────────
// Byte Type Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(StdSpanTest, Uint8Span) {
    uint8_t data[] = {0x00, 0x01, 0xFF, 0x80};
    std::span<uint8_t> span(data);

    EXPECT_EQ(span.size(), 4u);
    EXPECT_EQ(span[2], 0xFF);
}

TEST(StdSpanTest, CharSpan) {
    char str[] = "Hello";
    std::span<char> span(str, 5);  // Exclude null terminator

    EXPECT_EQ(span.size(), 5u);
    EXPECT_EQ(span[0], 'H');
    EXPECT_EQ(span[4], 'o');
}

// ─────────────────────────────────────────────────────────────────────────────
// C++23 Features
// ─────────────────────────────────────────────────────────────────────────────

TEST(StdSpanTest, AsBytes) {
    int arr[] = {0x01020304};
    std::span<int> span(arr);

    auto bytes = std::as_bytes(span);

    EXPECT_EQ(bytes.size(), sizeof(int));
}

TEST(StdSpanTest, AsWritableBytes) {
    int arr[] = {0};
    std::span<int> span(arr);

    auto bytes = std::as_writable_bytes(span);
    bytes[0] = std::byte{0xFF};

    // First byte of arr[0] should now be 0xFF
    EXPECT_EQ(reinterpret_cast<uint8_t*>(&arr[0])[0], 0xFF);
}
