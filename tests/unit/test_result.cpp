/**
 * @file test_result.cpp
 * @brief Unit tests for Result<T> (std::expected<T, Error>).
 */

#include <gtest/gtest.h>
#include <legends/error.h>
#include <memory>
#include <string>
#include <vector>

using namespace legends;

// ─────────────────────────────────────────────────────────────────────────────
// Result<T> Success Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ResultTest, OkCreatesSuccess) {
    auto result = Ok(42);

    EXPECT_TRUE(result.has_value());
    EXPECT_TRUE(static_cast<bool>(result));
}

TEST(ResultTest, SuccessValueReturnsValue) {
    auto result = Ok(42);

    EXPECT_EQ(result.value(), 42);
}

TEST(ResultTest, SuccessValueConstReturnsValue) {
    const auto result = Ok(std::string("hello"));

    EXPECT_EQ(result.value(), "hello");
}

TEST(ResultTest, SuccessValueMutableModifiesValue) {
    auto result = Ok(10);
    result.value() = 20;

    EXPECT_EQ(result.value(), 20);
}

TEST(ResultTest, SuccessMoveValueReturnsValue) {
    auto result = Ok(std::string("hello"));

    std::string value = std::move(result).value();

    EXPECT_EQ(value, "hello");
}

TEST(ResultTest, SuccessErrorUndefinedBehavior) {
    // Note: In std::expected, calling error() on a success is undefined behavior
    // We don't test this as it would cause undefined behavior
    auto result = Ok(42);
    EXPECT_TRUE(result.has_value());
}

// ─────────────────────────────────────────────────────────────────────────────
// Result<T> Failure Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ResultTest, ErrCreatesFailure) {
    Result<int> result = Err(Error(ErrorCode::InvalidArgument, "bad"));

    EXPECT_FALSE(result.has_value());
    EXPECT_FALSE(static_cast<bool>(result));
}

TEST(ResultTest, FailureErrorReturnsError) {
    Result<int> result = Err(Error(ErrorCode::FileNotFound, "missing"));

    EXPECT_EQ(result.error().code(), ErrorCode::FileNotFound);
    EXPECT_EQ(result.error().message(), "missing");
}

TEST(ResultTest, FailureValueThrows) {
    Result<int> result = Err(Error(ErrorCode::InvalidState, "error"));

    EXPECT_THROW(result.value(), std::bad_expected_access<Error>);
}

TEST(ResultTest, FailureConstValueThrows) {
    const Result<int> result = Err(Error(ErrorCode::InvalidState, "error"));

    EXPECT_THROW(result.value(), std::bad_expected_access<Error>);
}

TEST(ResultTest, FailureErrorMutable) {
    Result<int> result = Err(Error(ErrorCode::Unknown, "original"));

    EXPECT_EQ(result.error().message(), "original");
}

// ─────────────────────────────────────────────────────────────────────────────
// Result<T> value_or Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ResultTest, ValueOrReturnsValueOnSuccess) {
    auto result = Ok(42);

    EXPECT_EQ(result.value_or(0), 42);
}

TEST(ResultTest, ValueOrReturnsDefaultOnFailure) {
    Result<int> result = Err(Error(ErrorCode::Unknown, "error"));

    EXPECT_EQ(result.value_or(99), 99);
}

TEST(ResultTest, ValueOrWithString) {
    Result<std::string> result = Err(Error(ErrorCode::Unknown, "error"));

    EXPECT_EQ(result.value_or("default"), "default");
}

TEST(ResultTest, ValueOrSuccessString) {
    auto result = Ok(std::string("actual"));

    EXPECT_EQ(result.value_or("default"), "actual");
}

// ─────────────────────────────────────────────────────────────────────────────
// Result<T> transform Tests (replaces map)
// ─────────────────────────────────────────────────────────────────────────────

TEST(ResultTest, TransformMapsSuccess) {
    auto result = Ok(21);

    auto transformed = result.transform([](int x) { return x * 2; });

    EXPECT_TRUE(transformed.has_value());
    EXPECT_EQ(transformed.value(), 42);
}

TEST(ResultTest, TransformPreservesError) {
    Result<int> result = Err(Error(ErrorCode::DmaError, "oops"));

    auto transformed = result.transform([](int x) { return x * 2; });

    EXPECT_FALSE(transformed.has_value());
    EXPECT_EQ(transformed.error().code(), ErrorCode::DmaError);
}

TEST(ResultTest, TransformChangesType) {
    auto result = Ok(42);

    auto transformed = result.transform([](int x) { return std::to_string(x); });

    EXPECT_TRUE(transformed.has_value());
    EXPECT_EQ(transformed.value(), "42");
}

TEST(ResultTest, TransformChaining) {
    auto result = Ok(10);

    auto final_result = result
        .transform([](int x) { return x * 2; })
        .transform([](int x) { return x + 1; })
        .transform([](int x) { return std::to_string(x); });

    EXPECT_TRUE(final_result.has_value());
    EXPECT_EQ(final_result.value(), "21");
}

// ─────────────────────────────────────────────────────────────────────────────
// Result<T> and_then Tests (monadic chaining)
// ─────────────────────────────────────────────────────────────────────────────

TEST(ResultTest, AndThenChainsSuccess) {
    auto double_it = [](int x) -> Result<int> {
        return Ok(x * 2);
    };

    auto result = Ok(21).and_then(double_it);

    EXPECT_TRUE(result.has_value());
    EXPECT_EQ(result.value(), 42);
}

TEST(ResultTest, AndThenPropagatesError) {
    auto double_it = [](int x) -> Result<int> {
        return Ok(x * 2);
    };

    Result<int> failure = Err(Error(ErrorCode::InvalidArgument, "bad"));
    auto result = failure.and_then(double_it);

    EXPECT_FALSE(result.has_value());
    EXPECT_EQ(result.error().code(), ErrorCode::InvalidArgument);
}

TEST(ResultTest, AndThenChainMultiple) {
    auto add_one = [](int x) -> Result<int> { return Ok(x + 1); };
    auto double_it = [](int x) -> Result<int> { return Ok(x * 2); };

    auto result = Ok(10)
        .and_then(add_one)
        .and_then(double_it);

    EXPECT_TRUE(result.has_value());
    EXPECT_EQ(result.value(), 22);  // (10 + 1) * 2
}

// ─────────────────────────────────────────────────────────────────────────────
// Result<void> Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ResultVoidTest, OkVoidIsSuccess) {
    auto result = Ok();

    EXPECT_TRUE(result.has_value());
    EXPECT_TRUE(static_cast<bool>(result));
}

TEST(ResultVoidTest, ErrVoidIsFailure) {
    Result<void> result = Err(Error(ErrorCode::FileWriteError, "denied"));

    EXPECT_FALSE(result.has_value());
    EXPECT_EQ(result.error().code(), ErrorCode::FileWriteError);
}

TEST(ResultVoidTest, VoidResultFromFunction) {
    auto success_fn = []() -> Result<void> {
        return Ok();
    };

    auto failure_fn = []() -> Result<void> {
        return Err(Error(ErrorCode::ConfigParseError, "syntax error"));
    };

    EXPECT_TRUE(success_fn().has_value());
    EXPECT_FALSE(failure_fn().has_value());
}

// ─────────────────────────────────────────────────────────────────────────────
// Move Semantics Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ResultTest, MoveOnlyTypeWorks) {
    auto result = Ok(std::make_unique<int>(42));

    EXPECT_TRUE(result.has_value());

    auto ptr = std::move(result).value();

    EXPECT_EQ(*ptr, 42);
}

TEST(ResultTest, MoveOnlyFailure) {
    Result<std::unique_ptr<int>> result = Err(
        Error(ErrorCode::OutOfMemory, "allocation failed"));

    EXPECT_FALSE(result.has_value());
    EXPECT_THROW(std::move(result).value(), std::bad_expected_access<Error>);
}

TEST(ResultTest, VectorMoveWorks) {
    std::vector<int> data = {1, 2, 3, 4, 5};
    auto result = Ok(std::move(data));

    EXPECT_TRUE(result.has_value());

    auto vec = std::move(result).value();
    EXPECT_EQ(vec.size(), 5u);
    EXPECT_EQ(vec[0], 1);
    EXPECT_EQ(vec[4], 5);
}

// ─────────────────────────────────────────────────────────────────────────────
// Complex Type Tests
// ─────────────────────────────────────────────────────────────────────────────

struct ComplexType {
    int x;
    std::string name;
    std::vector<double> values;
};

TEST(ResultTest, ComplexTypeSuccess) {
    ComplexType ct{42, "test", {1.0, 2.0, 3.0}};
    auto result = Ok(std::move(ct));

    EXPECT_TRUE(result.has_value());
    EXPECT_EQ(result.value().x, 42);
    EXPECT_EQ(result.value().name, "test");
    EXPECT_EQ(result.value().values.size(), 3u);
}

TEST(ResultTest, ComplexTypeFailure) {
    Result<ComplexType> result = Err(
        Error(ErrorCode::InvalidArgument, "bad input"));

    EXPECT_FALSE(result.has_value());
    EXPECT_THROW(result.value(), std::bad_expected_access<Error>);
}

// ─────────────────────────────────────────────────────────────────────────────
// Error Preservation Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ResultTest, ErrorPreservesLocation) {
    Result<int> result = Err(Error(ErrorCode::CpuError, "test"));

    auto& err = result.error();
    EXPECT_NE(err.location().line(), 0u);
}

TEST(ResultTest, ErrorChainPreservesOriginal) {
    Result<int> original = Err(Error(ErrorCode::MemoryError, "original error"));

    // Chain through transform - error should be preserved
    auto chained = original
        .transform([](int x) { return x * 2; })
        .transform([](int x) { return std::to_string(x); });

    EXPECT_FALSE(chained.has_value());
    EXPECT_EQ(chained.error().code(), ErrorCode::MemoryError);
    EXPECT_EQ(chained.error().message(), "original error");
}

// ─────────────────────────────────────────────────────────────────────────────
// Copy Behavior Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ResultTest, CopyableTypeCanBeCopied) {
    auto result1 = Ok(42);
    auto result2 = result1;  // Copy

    EXPECT_TRUE(result1.has_value());
    EXPECT_TRUE(result2.has_value());
    EXPECT_EQ(result1.value(), 42);
    EXPECT_EQ(result2.value(), 42);
}

TEST(ResultTest, ErrorResultCanBeCopied) {
    Result<int> result1 = Err(Error(ErrorCode::InvalidState, "test"));
    auto result2 = result1;  // Copy

    EXPECT_FALSE(result1.has_value());
    EXPECT_FALSE(result2.has_value());
    EXPECT_EQ(result1.error().code(), result2.error().code());
}

// ─────────────────────────────────────────────────────────────────────────────
// make_error Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ResultTest, MakeErrorCreatesError) {
    Result<int> result = make_error(ErrorCode::InvalidArgument, "bad value");

    EXPECT_FALSE(result.has_value());
    EXPECT_EQ(result.error().code(), ErrorCode::InvalidArgument);
    EXPECT_EQ(result.error().message(), "bad value");
}

TEST(ResultTest, MakeErrorCapturesLocation) {
    Result<int> result = make_error(ErrorCode::Unknown, "test");

    EXPECT_NE(result.error().location().line(), 0u);
    EXPECT_NE(result.error().location().file_name(), nullptr);
}

TEST(ResultTest, MakeErrorFmtFormatsMessage) {
    Result<int> result = make_error_fmt(
        ErrorCode::InvalidArgument, "value {} is invalid", 42);

    EXPECT_FALSE(result.has_value());
    EXPECT_EQ(result.error().message(), "value 42 is invalid");
}

// ─────────────────────────────────────────────────────────────────────────────
// Error Class Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ErrorTest, FormattedCreatesMessage) {
    auto err = Error::formatted(ErrorCode::InvalidArgument,
        "value {} is invalid", 123);

    EXPECT_EQ(err.code(), ErrorCode::InvalidArgument);
    EXPECT_EQ(err.message(), "value 123 is invalid");
}

TEST(ErrorTest, FormatProducesReadableString) {
    Error err(ErrorCode::FileNotFound, "config.ini not found");

    std::string formatted = err.format();

    EXPECT_TRUE(formatted.find("FileNotFound") != std::string::npos);
    EXPECT_TRUE(formatted.find("config.ini not found") != std::string::npos);
}

TEST(ErrorTest, IsChecksCode) {
    Error err(ErrorCode::OutOfMemory, "allocation failed");

    EXPECT_TRUE(err.is(ErrorCode::OutOfMemory));
    EXPECT_FALSE(err.is(ErrorCode::FileNotFound));
}
