/**
 * @file test_dosbox_error_model.cpp
 * @brief Unit tests for DOSBox-X FAIL/PANIC/TRAP error model.
 *
 * Tests the error handling infrastructure defined in dosbox/error_model.h.
 */

#include <gtest/gtest.h>
#include "dosbox/error_model.h"

#include <thread>
#include <atomic>

using namespace dosbox;

// ═══════════════════════════════════════════════════════════════════════════════
// ErrorCode Tests (C++ enum class)
// ═══════════════════════════════════════════════════════════════════════════════

TEST(DosboxErrorCodeTest, CodeNameReturnsCorrectStrings) {
    EXPECT_STREQ(error_code_name(ErrorCode::Ok), "OK");
    EXPECT_STREQ(error_code_name(ErrorCode::Unknown), "ERR_UNKNOWN");
    EXPECT_STREQ(error_code_name(ErrorCode::InvalidArgument), "ERR_INVALID_ARGUMENT");
    EXPECT_STREQ(error_code_name(ErrorCode::InvalidState), "ERR_INVALID_STATE");
}

TEST(DosboxErrorCodeTest, ResourceErrorCodes) {
    EXPECT_STREQ(error_code_name(ErrorCode::OutOfMemory), "ERR_OUT_OF_MEMORY");
    EXPECT_STREQ(error_code_name(ErrorCode::ResourceExhausted), "ERR_RESOURCE_EXHAUSTED");
    EXPECT_STREQ(error_code_name(ErrorCode::ResourceBusy), "ERR_RESOURCE_BUSY");
    EXPECT_STREQ(error_code_name(ErrorCode::ResourceNotFound), "ERR_RESOURCE_NOT_FOUND");
}

TEST(DosboxErrorCodeTest, IoErrorCodes) {
    EXPECT_STREQ(error_code_name(ErrorCode::FileNotFound), "ERR_FILE_NOT_FOUND");
    EXPECT_STREQ(error_code_name(ErrorCode::FileAccessDenied), "ERR_FILE_ACCESS_DENIED");
    EXPECT_STREQ(error_code_name(ErrorCode::FileReadError), "ERR_FILE_READ_ERROR");
    EXPECT_STREQ(error_code_name(ErrorCode::FileWriteError), "ERR_FILE_WRITE_ERROR");
}

TEST(DosboxErrorCodeTest, FatalErrorCodes) {
    EXPECT_STREQ(error_code_name(ErrorCode::Panic), "ERR_PANIC");
    EXPECT_STREQ(error_code_name(ErrorCode::Trap), "ERR_TRAP");
    EXPECT_STREQ(error_code_name(ErrorCode::Fatal), "ERR_FATAL");
}

TEST(DosboxErrorCodeTest, UnknownCodeReturnsUnknown) {
    EXPECT_STREQ(error_code_name(static_cast<ErrorCode>(99999)), "ERR_UNKNOWN");
}

// ═══════════════════════════════════════════════════════════════════════════════
// C ABI Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(DosboxErrorCAbiTest, ErrorCodeNameWorks) {
    EXPECT_STREQ(dosbox_error_code_name(DOSBOX_OK), "OK");
    EXPECT_STREQ(dosbox_error_code_name(DOSBOX_ERR_INVALID_ARGUMENT), "ERR_INVALID_ARGUMENT");
    EXPECT_STREQ(dosbox_error_code_name(DOSBOX_ERR_PANIC), "ERR_PANIC");
}

TEST(DosboxErrorCAbiTest, ClearLastErrorWorks) {
    dosbox_clear_last_error();
    EXPECT_EQ(dosbox_get_last_error(), nullptr);
}

TEST(DosboxErrorCAbiTest, GetLastErrorStringWithNoError) {
    dosbox_clear_last_error();

    char buffer[256];
    size_t length = 0;
    int result = dosbox_get_last_error_string(buffer, sizeof(buffer), &length);

    EXPECT_EQ(result, DOSBOX_OK);
    EXPECT_EQ(length, 0u);
    EXPECT_STREQ(buffer, "");
}

TEST(DosboxErrorCAbiTest, GetLastErrorStringWithNullBuffer) {
    int result = dosbox_get_last_error_string(nullptr, 0, nullptr);
    EXPECT_EQ(result, DOSBOX_ERR_INVALID_ARGUMENT);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Error Class Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(DosboxErrorTest, ConstructionCapturesAllFields) {
    Error err(ErrorCode::FileNotFound, "test.conf not found");

    EXPECT_EQ(err.code(), ErrorCode::FileNotFound);
    EXPECT_EQ(err.message(), "test.conf not found");
    EXPECT_NE(err.line(), 0u);
}

TEST(DosboxErrorTest, LocationCapturesFile) {
    Error err(ErrorCode::Unknown, "test");
    std::string file = err.file();
    EXPECT_NE(std::string(file).find("test_dosbox_error_model"), std::string::npos);
}

TEST(DosboxErrorTest, FormatIncludesCode) {
    Error err(ErrorCode::InvalidArgument, "bad value");
    std::string formatted = err.format();
    EXPECT_NE(formatted.find("ERR_INVALID_ARGUMENT"), std::string::npos);
}

TEST(DosboxErrorTest, FormatIncludesMessage) {
    Error err(ErrorCode::CpuError, "illegal instruction");
    std::string formatted = err.format();
    EXPECT_NE(formatted.find("illegal instruction"), std::string::npos);
}

TEST(DosboxErrorTest, ToFfiPreservesCode) {
    Error err(ErrorCode::MemoryError, "out of bounds");
    dosbox_error ffi = err.to_ffi();

    EXPECT_EQ(ffi.code, DOSBOX_ERR_MEMORY);
}

TEST(DosboxErrorTest, ToFfiPreservesMessage) {
    Error err(ErrorCode::DmaError, "channel overflow");
    dosbox_error ffi = err.to_ffi();

    EXPECT_STREQ(ffi.message, "channel overflow");
}

TEST(DosboxErrorTest, ToFfiTruncatesLongMessage) {
    std::string long_msg(500, 'x');
    Error err(ErrorCode::Unknown, long_msg);
    dosbox_error ffi = err.to_ffi();

    // Message buffer is 256 bytes, so should be truncated
    EXPECT_EQ(std::strlen(ffi.message), 255u);
}

TEST(DosboxErrorTest, FromFfiWorks) {
    dosbox_error ffi = {};
    ffi.code = DOSBOX_ERR_FILE_NOT_FOUND;
    std::strcpy(ffi.message, "missing file");

    Error err = Error::from_ffi(ffi);

    EXPECT_EQ(err.code(), ErrorCode::FileNotFound);
    EXPECT_EQ(err.message(), "missing file");
}

// ═══════════════════════════════════════════════════════════════════════════════
// Result<T> Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(DosboxResultTest, OkHasValue) {
    Result<int> result = Ok(42);
    EXPECT_TRUE(result.has_value());
    EXPECT_EQ(result.value(), 42);
}

TEST(DosboxResultTest, OkVoidHasValue) {
    Result<void> result = Ok();
    EXPECT_TRUE(result.has_value());
}

TEST(DosboxResultTest, ErrHasError) {
    Result<int> result = Err(Error{ErrorCode::InvalidArgument, "bad"});
    EXPECT_FALSE(result.has_value());
    EXPECT_EQ(result.error().code(), ErrorCode::InvalidArgument);
}

TEST(DosboxResultTest, MakeErrorWorks) {
    auto result = make_error(ErrorCode::FileNotFound, "not found");
    EXPECT_EQ(result.error().code(), ErrorCode::FileNotFound);
    EXPECT_EQ(result.error().message(), "not found");
}

// ═══════════════════════════════════════════════════════════════════════════════
// Handler Tests
// ═══════════════════════════════════════════════════════════════════════════════

namespace {
    std::atomic<int> g_panic_handler_called{0};
    std::atomic<int> g_trap_handler_called{0};
    dosbox_error_code g_last_panic_code{DOSBOX_OK};
    dosbox_error_code g_last_trap_code{DOSBOX_OK};

    void test_panic_handler(const dosbox_error* err, void* userdata) {
        g_panic_handler_called++;
        if (err) {
            g_last_panic_code = err->code;
        }
        (void)userdata;
    }

    void test_trap_handler(const dosbox_error* err, void* userdata) {
        g_trap_handler_called++;
        if (err) {
            g_last_trap_code = err->code;
        }
        (void)userdata;
    }
}

class DosboxHandlerTest : public ::testing::Test {
protected:
    void SetUp() override {
        g_panic_handler_called = 0;
        g_trap_handler_called = 0;
        g_last_panic_code = DOSBOX_OK;
        g_last_trap_code = DOSBOX_OK;
        dosbox_clear_last_error();
        // Reset handlers
        dosbox_set_panic_handler(nullptr, nullptr);
        dosbox_set_trap_handler(nullptr, nullptr);
    }

    void TearDown() override {
        // Clean up handlers
        dosbox_set_panic_handler(nullptr, nullptr);
        dosbox_set_trap_handler(nullptr, nullptr);
        dosbox_clear_last_error();
    }
};

TEST_F(DosboxHandlerTest, PanicHandlerGetsInvoked) {
    dosbox_set_panic_handler(test_panic_handler, nullptr);

    // Directly call panic_internal (simulates DOSBOX_PANIC usage)
    Error err = panic_internal("test panic");

    EXPECT_EQ(g_panic_handler_called, 1);
    EXPECT_EQ(g_last_panic_code, DOSBOX_ERR_PANIC);
    EXPECT_EQ(err.code(), ErrorCode::Panic);
}

TEST_F(DosboxHandlerTest, TrapHandlerGetsInvoked) {
    dosbox_set_trap_handler(test_trap_handler, nullptr);

    // Directly call trap_internal (simulates DOSBOX_TRAP usage)
    Error err = trap_internal("test trap");

    EXPECT_EQ(g_trap_handler_called, 1);
    EXPECT_EQ(g_last_trap_code, DOSBOX_ERR_TRAP);
    EXPECT_EQ(err.code(), ErrorCode::Trap);
}

TEST_F(DosboxHandlerTest, PanicSetsLastError) {
    panic_internal("panic message");

    const dosbox_error* err = dosbox_get_last_error();
    ASSERT_NE(err, nullptr);
    EXPECT_EQ(err->code, DOSBOX_ERR_PANIC);
    EXPECT_STREQ(err->message, "panic message");
}

TEST_F(DosboxHandlerTest, TrapSetsLastError) {
    trap_internal("trap message");

    const dosbox_error* err = dosbox_get_last_error();
    ASSERT_NE(err, nullptr);
    EXPECT_EQ(err->code, DOSBOX_ERR_TRAP);
    EXPECT_STREQ(err->message, "trap message");
}

// ═══════════════════════════════════════════════════════════════════════════════
// Context State Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(DosboxContextStateTest, PanicSetsFailedState) {
    // After panic, context should be in Failed state
    panic_internal("invariant violation");

    ContextState state = get_context_state(nullptr);
    EXPECT_EQ(state, ContextState::Failed);
}

TEST(DosboxContextStateTest, TrapSetsFailedState) {
    // After trap, context should be in Failed state
    trap_internal("memory corruption");

    ContextState state = get_context_state(nullptr);
    EXPECT_EQ(state, ContextState::Failed);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Thread Safety Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(DosboxThreadSafetyTest, LastErrorIsThreadLocal) {
    dosbox_clear_last_error();

    std::atomic<bool> thread_started{false};
    std::atomic<bool> main_can_check{false};

    std::thread other_thread([&]() {
        // Set error in other thread
        set_last_error(Error{ErrorCode::CpuError, "thread error"});
        thread_started = true;

        // Wait for main thread to check
        while (!main_can_check) {
            std::this_thread::yield();
        }
    });

    // Wait for other thread to set its error
    while (!thread_started) {
        std::this_thread::yield();
    }

    // Main thread should not see other thread's error
    const dosbox_error* err = dosbox_get_last_error();
    EXPECT_EQ(err, nullptr);

    main_can_check = true;
    other_thread.join();
}

// ═══════════════════════════════════════════════════════════════════════════════
// FAIL/PANIC/TRAP Macro Simulation Tests
// ═══════════════════════════════════════════════════════════════════════════════

namespace {

// Test functions that use the error macros
Result<int> test_fail_macro(int value) {
    if (value < 0) {
        DOSBOX_FAIL(InvalidArgument, "value must be non-negative");
    }
    return Ok(value * 2);
}

Result<int> test_check_macro(int value) {
    DOSBOX_CHECK(value >= 0, InvalidArgument, "value must be non-negative");
    return Ok(value * 2);
}

Result<void> test_panic_macro(bool should_panic) {
    if (should_panic) {
        DOSBOX_PANIC("internal invariant violated");
    }
    return Ok();
}

Result<void> test_trap_macro(bool should_trap) {
    if (should_trap) {
        DOSBOX_TRAP("memory corruption detected");
    }
    return Ok();
}

} // anonymous namespace

TEST(DosboxMacroTest, FailMacroReturnsError) {
    Result<int> result = test_fail_macro(-1);
    EXPECT_FALSE(result.has_value());
    EXPECT_EQ(result.error().code(), ErrorCode::InvalidArgument);
}

TEST(DosboxMacroTest, FailMacroAllowsSuccess) {
    Result<int> result = test_fail_macro(5);
    EXPECT_TRUE(result.has_value());
    EXPECT_EQ(result.value(), 10);
}

TEST(DosboxMacroTest, CheckMacroReturnsErrorOnFailure) {
    Result<int> result = test_check_macro(-1);
    EXPECT_FALSE(result.has_value());
    EXPECT_EQ(result.error().code(), ErrorCode::InvalidArgument);
}

TEST(DosboxMacroTest, CheckMacroAllowsSuccess) {
    Result<int> result = test_check_macro(5);
    EXPECT_TRUE(result.has_value());
    EXPECT_EQ(result.value(), 10);
}

TEST(DosboxMacroTest, PanicMacroReturnsError) {
    Result<void> result = test_panic_macro(true);
    EXPECT_FALSE(result.has_value());
    EXPECT_EQ(result.error().code(), ErrorCode::Panic);
}

TEST(DosboxMacroTest, PanicMacroAllowsSuccess) {
    Result<void> result = test_panic_macro(false);
    EXPECT_TRUE(result.has_value());
}

TEST(DosboxMacroTest, TrapMacroReturnsError) {
    Result<void> result = test_trap_macro(true);
    EXPECT_FALSE(result.has_value());
    EXPECT_EQ(result.error().code(), ErrorCode::Trap);
}

TEST(DosboxMacroTest, TrapMacroAllowsSuccess) {
    Result<void> result = test_trap_macro(false);
    EXPECT_TRUE(result.has_value());
}
