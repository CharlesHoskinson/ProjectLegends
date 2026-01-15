/**
 * @file test_dosbox_safe_call.cpp
 * @brief Unit tests for DOSBox-X API boundary containment.
 *
 * Tests the safe_call wrapper defined in dosbox/safe_call.h.
 */

#include <gtest/gtest.h>
#include "dosbox/safe_call.h"

#include <stdexcept>

using namespace dosbox;

// ═══════════════════════════════════════════════════════════════════════════════
// Test Fixtures
// ═══════════════════════════════════════════════════════════════════════════════

class SafeCallTest : public ::testing::Test {
protected:
    void SetUp() override {
        dosbox_clear_last_error();
    }

    void TearDown() override {
        dosbox_clear_last_error();
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
// FatalException Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(FatalExceptionTest, ConstructionWorks) {
    FatalException ex("test message", "test.cpp", 42);

    EXPECT_STREQ(ex.what(), "test message");
    EXPECT_EQ(ex.message(), "test message");
    EXPECT_EQ(ex.file(), "test.cpp");
    EXPECT_EQ(ex.line(), 42);
}

TEST(FatalExceptionTest, NullMessageHandled) {
    FatalException ex(nullptr, nullptr, 0);

    EXPECT_STREQ(ex.what(), "Unknown fatal error");
    EXPECT_EQ(ex.file(), "unknown");
    EXPECT_EQ(ex.line(), 0);
}

TEST(FatalExceptionTest, IsStdException) {
    FatalException ex("test", "file.cpp", 1);
    std::exception& base = ex;

    EXPECT_STREQ(base.what(), "test");
}

// ═══════════════════════════════════════════════════════════════════════════════
// safe_call_void Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(SafeCallTest, SafeCallVoidSuccessReturnsOk) {
    dosbox_error_code result = safe_call_void([]() -> Result<void> {
        return Ok();
    });

    EXPECT_EQ(result, DOSBOX_OK);
    EXPECT_EQ(dosbox_get_last_error(), nullptr);
}

TEST_F(SafeCallTest, SafeCallVoidErrorReturnsCode) {
    dosbox_error_code result = safe_call_void([]() -> Result<void> {
        DOSBOX_FAIL(InvalidArgument, "test error");
    });

    EXPECT_EQ(result, DOSBOX_ERR_INVALID_ARGUMENT);

    const dosbox_error* err = dosbox_get_last_error();
    ASSERT_NE(err, nullptr);
    EXPECT_EQ(err->code, DOSBOX_ERR_INVALID_ARGUMENT);
}

TEST_F(SafeCallTest, SafeCallVoidCatchesStdException) {
    dosbox_error_code result = safe_call_void([]() -> Result<void> {
        throw std::runtime_error("runtime error");
    });

    EXPECT_EQ(result, DOSBOX_ERR_EXCEPTION);

    const dosbox_error* err = dosbox_get_last_error();
    ASSERT_NE(err, nullptr);
    EXPECT_EQ(err->code, DOSBOX_ERR_EXCEPTION);
    EXPECT_NE(std::string(err->message).find("runtime error"), std::string::npos);
}

TEST_F(SafeCallTest, SafeCallVoidCatchesFatalException) {
    dosbox_error_code result = safe_call_void([]() -> Result<void> {
        throw FatalException("fatal error", "test.cpp", 100);
    });

    EXPECT_EQ(result, DOSBOX_ERR_FATAL);

    const dosbox_error* err = dosbox_get_last_error();
    ASSERT_NE(err, nullptr);
    EXPECT_EQ(err->code, DOSBOX_ERR_FATAL);
}

TEST_F(SafeCallTest, SafeCallVoidCatchesUnknownException) {
    dosbox_error_code result = safe_call_void([]() -> Result<void> {
        throw 42; // Non-standard exception
    });

    EXPECT_EQ(result, DOSBOX_ERR_EXCEPTION);

    const dosbox_error* err = dosbox_get_last_error();
    ASSERT_NE(err, nullptr);
    EXPECT_EQ(err->code, DOSBOX_ERR_EXCEPTION);
}

TEST_F(SafeCallTest, SafeCallVoidCatchesErrorDirectly) {
    dosbox_error_code result = safe_call_void([]() -> Result<void> {
        throw Error{ErrorCode::MemoryError, "memory issue"};
    });

    EXPECT_EQ(result, DOSBOX_ERR_MEMORY);

    const dosbox_error* err = dosbox_get_last_error();
    ASSERT_NE(err, nullptr);
    EXPECT_EQ(err->code, DOSBOX_ERR_MEMORY);
}

// ═══════════════════════════════════════════════════════════════════════════════
// safe_call_code Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(SafeCallTest, SafeCallCodeSuccessReturnsOk) {
    dosbox_error_code result = safe_call_code([]() -> dosbox_error_code {
        return DOSBOX_OK;
    });

    EXPECT_EQ(result, DOSBOX_OK);
}

TEST_F(SafeCallTest, SafeCallCodeReturnsErrorCode) {
    dosbox_error_code result = safe_call_code([]() -> dosbox_error_code {
        return DOSBOX_ERR_FILE_NOT_FOUND;
    });

    EXPECT_EQ(result, DOSBOX_ERR_FILE_NOT_FOUND);
}

TEST_F(SafeCallTest, SafeCallCodeCatchesException) {
    dosbox_error_code result = safe_call_code([]() -> dosbox_error_code {
        throw std::logic_error("logic error");
    });

    EXPECT_EQ(result, DOSBOX_ERR_EXCEPTION);
}

TEST_F(SafeCallTest, SafeCallCodeCatchesFatal) {
    dosbox_error_code result = safe_call_code([]() -> dosbox_error_code {
        throw FatalException("fatal", "file.cpp", 1);
    });

    EXPECT_EQ(result, DOSBOX_ERR_FATAL);
}

// ═══════════════════════════════════════════════════════════════════════════════
// safe_call Tests (Result<T> with value)
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(SafeCallTest, SafeCallReturnsValue) {
    int result = safe_call([]() -> Result<int> {
        return Ok(42);
    });

    EXPECT_EQ(result, 42);
}

TEST_F(SafeCallTest, SafeCallErrorReturnsDefault) {
    int result = safe_call([]() -> Result<int> {
        DOSBOX_FAIL(InvalidArgument, "bad arg");
    });

    EXPECT_EQ(result, 0); // Default-constructed int

    const dosbox_error* err = dosbox_get_last_error();
    ASSERT_NE(err, nullptr);
    EXPECT_EQ(err->code, DOSBOX_ERR_INVALID_ARGUMENT);
}

TEST_F(SafeCallTest, SafeCallExceptionReturnsDefault) {
    int result = safe_call([]() -> Result<int> {
        throw std::runtime_error("oops");
    });

    EXPECT_EQ(result, 0);

    const dosbox_error* err = dosbox_get_last_error();
    ASSERT_NE(err, nullptr);
    EXPECT_EQ(err->code, DOSBOX_ERR_EXCEPTION);
}

TEST_F(SafeCallTest, SafeCallWithPointerType) {
    int value = 100;

    int* result = safe_call([&]() -> Result<int*> {
        return Ok(&value);
    });

    ASSERT_NE(result, nullptr);
    EXPECT_EQ(*result, 100);
}

TEST_F(SafeCallTest, SafeCallPointerErrorReturnsNull) {
    int* result = safe_call([]() -> Result<int*> {
        DOSBOX_FAIL(ResourceNotFound, "not found");
    });

    EXPECT_EQ(result, nullptr);
}

// ═══════════════════════════════════════════════════════════════════════════════
// DOSBOX_PANIC / DOSBOX_TRAP in safe_call
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(SafeCallTest, SafeCallHandlesPanic) {
    dosbox_error_code result = safe_call_void([]() -> Result<void> {
        DOSBOX_PANIC("invariant violated");
    });

    EXPECT_EQ(result, DOSBOX_ERR_PANIC);

    const dosbox_error* err = dosbox_get_last_error();
    ASSERT_NE(err, nullptr);
    EXPECT_EQ(err->code, DOSBOX_ERR_PANIC);
}

TEST_F(SafeCallTest, SafeCallHandlesTrap) {
    dosbox_error_code result = safe_call_void([]() -> Result<void> {
        DOSBOX_TRAP("memory corruption");
    });

    EXPECT_EQ(result, DOSBOX_ERR_TRAP);

    const dosbox_error* err = dosbox_get_last_error();
    ASSERT_NE(err, nullptr);
    EXPECT_EQ(err->code, DOSBOX_ERR_TRAP);
}

// ═══════════════════════════════════════════════════════════════════════════════
// API Boundary Macro Tests
// ═══════════════════════════════════════════════════════════════════════════════

namespace {

// Simulate a C API function using the macros
dosbox_error_code test_api_function_success() {
    DOSBOX_API_BOUNDARY {
        return DOSBOX_OK;
    } DOSBOX_API_BOUNDARY_END;
}

dosbox_error_code test_api_function_error() {
    DOSBOX_API_BOUNDARY {
        return DOSBOX_ERR_INVALID_STATE;
    } DOSBOX_API_BOUNDARY_END;
}

dosbox_error_code test_api_function_throws() {
    DOSBOX_API_BOUNDARY {
        throw std::runtime_error("API error");
    } DOSBOX_API_BOUNDARY_END;
}

} // anonymous namespace

TEST_F(SafeCallTest, ApiBoundaryMacroSuccess) {
    dosbox_error_code result = test_api_function_success();
    EXPECT_EQ(result, DOSBOX_OK);
}

TEST_F(SafeCallTest, ApiBoundaryMacroError) {
    dosbox_error_code result = test_api_function_error();
    EXPECT_EQ(result, DOSBOX_ERR_INVALID_STATE);
}

TEST_F(SafeCallTest, ApiBoundaryMacroCatchesException) {
    dosbox_error_code result = test_api_function_throws();
    EXPECT_EQ(result, DOSBOX_ERR_EXCEPTION);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Nested Exception Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(SafeCallTest, NestedSafeCallWorks) {
    dosbox_error_code result = safe_call_void([]() -> Result<void> {
        // Inner safe_call
        int inner = safe_call([]() -> Result<int> {
            return Ok(42);
        });
        (void)inner;
        return Ok();
    });

    EXPECT_EQ(result, DOSBOX_OK);
}

TEST_F(SafeCallTest, NestedSafeCallPropagatesError) {
    dosbox_error_code result = safe_call_void([]() -> Result<void> {
        // Inner safe_call that fails
        int inner = safe_call([]() -> Result<int> {
            DOSBOX_FAIL(CpuError, "cpu fault");
        });
        (void)inner;
        // Outer continues but inner set last error
        return Ok();
    });

    // Outer succeeds but last error was set by inner
    EXPECT_EQ(result, DOSBOX_OK);

    const dosbox_error* err = dosbox_get_last_error();
    ASSERT_NE(err, nullptr);
    EXPECT_EQ(err->code, DOSBOX_ERR_CPU);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Edge Cases
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(SafeCallTest, MultipleExceptionsInSequence) {
    // First call
    safe_call_void([]() -> Result<void> {
        throw std::runtime_error("first");
    });

    const dosbox_error* err1 = dosbox_get_last_error();
    ASSERT_NE(err1, nullptr);
    EXPECT_NE(std::string(err1->message).find("first"), std::string::npos);

    // Second call overwrites
    safe_call_void([]() -> Result<void> {
        throw std::runtime_error("second");
    });

    const dosbox_error* err2 = dosbox_get_last_error();
    ASSERT_NE(err2, nullptr);
    EXPECT_NE(std::string(err2->message).find("second"), std::string::npos);
}

TEST_F(SafeCallTest, ClearErrorAfterSuccess) {
    // Set an error
    safe_call_void([]() -> Result<void> {
        DOSBOX_FAIL(InvalidArgument, "error");
    });

    EXPECT_NE(dosbox_get_last_error(), nullptr);

    // Clear it
    dosbox_clear_last_error();

    EXPECT_EQ(dosbox_get_last_error(), nullptr);

    // Success doesn't set error
    safe_call_void([]() -> Result<void> {
        return Ok();
    });

    EXPECT_EQ(dosbox_get_last_error(), nullptr);
}
