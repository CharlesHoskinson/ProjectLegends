/**
 * @file test_optional_utils.cpp
 * @brief Unit tests for optional and variant utilities.
 */

#include <gtest/gtest.h>
#include <legends/optional_utils.h>
#include <string>

using namespace legends;

// ─────────────────────────────────────────────────────────────────────────────
// unwrap_or_throw Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(OptionalUtilsTest, UnwrapOrThrowWithValue) {
    std::optional<int> opt = 42;

    EXPECT_EQ(unwrap_or_throw(opt), 42);
}

TEST(OptionalUtilsTest, UnwrapOrThrowWithEmpty) {
    std::optional<int> opt;

    EXPECT_THROW((void)unwrap_or_throw(opt), std::runtime_error);
}

TEST(OptionalUtilsTest, UnwrapOrThrowCustomMessage) {
    std::optional<int> opt;

    try {
        (void)unwrap_or_throw(opt, "Custom error message");
        FAIL() << "Expected exception";
    } catch (const std::runtime_error& e) {
        EXPECT_STREQ(e.what(), "Custom error message");
    }
}

TEST(OptionalUtilsTest, UnwrapOrThrowConstOptional) {
    const std::optional<int> opt = 42;

    EXPECT_EQ(unwrap_or_throw(opt), 42);
}

TEST(OptionalUtilsTest, UnwrapOrThrowReturnsReference) {
    std::optional<int> opt = 10;
    int& ref = unwrap_or_throw(opt);

    ref = 20;

    EXPECT_EQ(*opt, 20);
}

// ─────────────────────────────────────────────────────────────────────────────
// value_or Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(OptionalUtilsTest, ValueOrWithValue) {
    std::optional<int> opt = 42;

    EXPECT_EQ(value_or(opt, 0), 42);
}

TEST(OptionalUtilsTest, ValueOrWithEmpty) {
    std::optional<int> opt;

    EXPECT_EQ(value_or(opt, 99), 99);
}

// ─────────────────────────────────────────────────────────────────────────────
// map_optional Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(OptionalUtilsTest, MapOptionalWithValue) {
    std::optional<int> opt = 21;
    auto result = map_optional(opt, [](int x) { return x * 2; });

    EXPECT_TRUE(result.has_value());
    EXPECT_EQ(*result, 42);
}

TEST(OptionalUtilsTest, MapOptionalWithEmpty) {
    std::optional<int> opt;
    auto result = map_optional(opt, [](int x) { return x * 2; });

    EXPECT_FALSE(result.has_value());
}

TEST(OptionalUtilsTest, MapOptionalChangesType) {
    std::optional<int> opt = 42;
    auto result = map_optional(opt, [](int x) { return std::to_string(x); });

    EXPECT_TRUE(result.has_value());
    EXPECT_EQ(*result, "42");
}

TEST(OptionalUtilsTest, MapOptionalMutable) {
    std::optional<int> opt = 10;
    auto result = map_optional(opt, [](int& x) { return x * 2; });

    EXPECT_TRUE(result.has_value());
    EXPECT_EQ(*result, 20);
}

// ─────────────────────────────────────────────────────────────────────────────
// flat_map_optional Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(OptionalUtilsTest, FlatMapOptionalWithValue) {
    std::optional<int> opt = 5;
    auto result = flat_map_optional(opt, [](int x) -> std::optional<int> {
        if (x > 0) return x * 2;
        return std::nullopt;
    });

    EXPECT_TRUE(result.has_value());
    EXPECT_EQ(*result, 10);
}

TEST(OptionalUtilsTest, FlatMapOptionalEmpty) {
    std::optional<int> opt;
    auto result = flat_map_optional(opt, [](int x) -> std::optional<int> {
        return x * 2;
    });

    EXPECT_FALSE(result.has_value());
}

TEST(OptionalUtilsTest, FlatMapOptionalReturnsNullopt) {
    std::optional<int> opt = -5;
    auto result = flat_map_optional(opt, [](int x) -> std::optional<int> {
        if (x > 0) return x * 2;
        return std::nullopt;
    });

    EXPECT_FALSE(result.has_value());
}

// ─────────────────────────────────────────────────────────────────────────────
// filter_optional Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(OptionalUtilsTest, FilterOptionalPasses) {
    std::optional<int> opt = 42;
    auto result = filter_optional(opt, [](int x) { return x > 0; });

    EXPECT_TRUE(result.has_value());
    EXPECT_EQ(*result, 42);
}

TEST(OptionalUtilsTest, FilterOptionalFails) {
    std::optional<int> opt = -1;
    auto result = filter_optional(opt, [](int x) { return x > 0; });

    EXPECT_FALSE(result.has_value());
}

TEST(OptionalUtilsTest, FilterOptionalEmpty) {
    std::optional<int> opt;
    auto result = filter_optional(opt, [](int x) { return x > 0; });

    EXPECT_FALSE(result.has_value());
}

// ─────────────────────────────────────────────────────────────────────────────
// if_present / if_empty Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(OptionalUtilsTest, IfPresentWithValue) {
    std::optional<int> opt = 42;
    int result = 0;

    if_present(opt, [&result](int x) { result = x; });

    EXPECT_EQ(result, 42);
}

TEST(OptionalUtilsTest, IfPresentWithEmpty) {
    std::optional<int> opt;
    int result = 0;

    if_present(opt, [&result](int x) { result = x; });

    EXPECT_EQ(result, 0);
}

TEST(OptionalUtilsTest, IfEmptyWithEmpty) {
    std::optional<int> opt;
    bool called = false;

    if_empty(opt, [&called]() { called = true; });

    EXPECT_TRUE(called);
}

TEST(OptionalUtilsTest, IfEmptyWithValue) {
    std::optional<int> opt = 42;
    bool called = false;

    if_empty(opt, [&called]() { called = true; });

    EXPECT_FALSE(called);
}

// ─────────────────────────────────────────────────────────────────────────────
// to_pointer Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(OptionalUtilsTest, ToPointerWithValue) {
    std::optional<int> opt = 42;
    int* ptr = to_pointer(opt);

    ASSERT_NE(ptr, nullptr);
    EXPECT_EQ(*ptr, 42);
}

TEST(OptionalUtilsTest, ToPointerWithEmpty) {
    std::optional<int> opt;
    int* ptr = to_pointer(opt);

    EXPECT_EQ(ptr, nullptr);
}

TEST(OptionalUtilsTest, ToPointerConst) {
    const std::optional<int> opt = 42;
    const int* ptr = to_pointer(opt);

    ASSERT_NE(ptr, nullptr);
    EXPECT_EQ(*ptr, 42);
}

// ─────────────────────────────────────────────────────────────────────────────
// Variant holds Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(VariantUtilsTest, HoldsReturnsTrue) {
    std::variant<int, std::string> v = 42;

    EXPECT_TRUE(holds<int>(v));
    EXPECT_FALSE(holds<std::string>(v));
}

TEST(VariantUtilsTest, HoldsAfterChange) {
    std::variant<int, std::string> v = 42;
    v = "hello";

    EXPECT_FALSE(holds<int>(v));
    EXPECT_TRUE(holds<std::string>(v));
}

// ─────────────────────────────────────────────────────────────────────────────
// Variant get_or Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(VariantUtilsTest, GetOrReturnsValue) {
    std::variant<int, std::string> v = 42;

    EXPECT_EQ(get_or<int>(v, 0), 42);
}

TEST(VariantUtilsTest, GetOrReturnsDefault) {
    std::variant<int, std::string> v = "hello";

    EXPECT_EQ(get_or<int>(v, 99), 99);
}

// ─────────────────────────────────────────────────────────────────────────────
// Variant get_if_ptr Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(VariantUtilsTest, GetIfPtrReturnsPointer) {
    std::variant<int, std::string> v = 42;
    int* ptr = get_if_ptr<int>(v);

    ASSERT_NE(ptr, nullptr);
    EXPECT_EQ(*ptr, 42);
}

TEST(VariantUtilsTest, GetIfPtrReturnsNull) {
    std::variant<int, std::string> v = "hello";
    int* ptr = get_if_ptr<int>(v);

    EXPECT_EQ(ptr, nullptr);
}

TEST(VariantUtilsTest, GetIfPtrConst) {
    const std::variant<int, std::string> v = 42;
    const int* ptr = get_if_ptr<int>(v);

    ASSERT_NE(ptr, nullptr);
    EXPECT_EQ(*ptr, 42);
}

// ─────────────────────────────────────────────────────────────────────────────
// visit_variant Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(VariantUtilsTest, VisitVariant) {
    std::variant<int, std::string> v = 42;

    auto result = visit_variant([](auto&& val) {
        using T = std::decay_t<decltype(val)>;
        if constexpr (std::is_same_v<T, int>) {
            return std::to_string(val);
        } else {
            return val;
        }
    }, v);

    EXPECT_EQ(result, "42");
}

// ─────────────────────────────────────────────────────────────────────────────
// overload Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(VariantUtilsTest, OverloadPattern) {
    std::variant<int, double, std::string> v = 3.14;

    std::string result = std::visit(overload{
        [](int i) { return "int: " + std::to_string(i); },
        [](double d) { return "double: " + std::to_string(d); },
        [](const std::string& s) { return "string: " + s; }
    }, v);

    EXPECT_TRUE(result.find("double") != std::string::npos);
}

// ─────────────────────────────────────────────────────────────────────────────
// match Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(VariantUtilsTest, MatchInt) {
    std::variant<int, std::string> v = 42;

    std::string result = match(v,
        [](int i) { return "int: " + std::to_string(i); },
        [](const std::string& s) { return "string: " + s; }
    );

    EXPECT_EQ(result, "int: 42");
}

TEST(VariantUtilsTest, MatchString) {
    std::variant<int, std::string> v = std::string("hello");

    std::string result = match(v,
        [](int i) { return "int: " + std::to_string(i); },
        [](const std::string& s) { return "string: " + s; }
    );

    EXPECT_EQ(result, "string: hello");
}

TEST(VariantUtilsTest, MatchWithThreeTypes) {
    std::variant<int, double, std::string> v = 3.14;

    int type_index = match(v,
        [](int) { return 0; },
        [](double) { return 1; },
        [](const std::string&) { return 2; }
    );

    EXPECT_EQ(type_index, 1);
}
