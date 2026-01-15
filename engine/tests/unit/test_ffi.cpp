/**
 * @file test_ffi.cpp
 * @brief Unit tests for FFI boundary utilities.
 */

#include <gtest/gtest.h>
#include <aibox/ffi.h>
#include <string>
#include <thread>
#include <vector>

using namespace aibox;

// ─────────────────────────────────────────────────────────────────────────────
// Error Code Constants Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(FfiErrorCodesTest, OkIsZero) {
    EXPECT_EQ(AIBOX_OK, 0);
}

TEST(FfiErrorCodesTest, ErrorsAreNonZero) {
    // Error codes are now positive (unified aibox_error_t from ffi_core.h)
    EXPECT_NE(AIBOX_ERR_INVALID_PARAM, 0);
    EXPECT_NE(AIBOX_ERR_INVALID_HANDLE, 0);
    EXPECT_NE(AIBOX_ERR_NOT_INITIALIZED, 0);
    EXPECT_NE(AIBOX_ERR_ALREADY_INITIALIZED, 0);
    EXPECT_NE(AIBOX_ERR_CPU, 0);
    EXPECT_NE(AIBOX_ERR_DMA, 0);
    EXPECT_NE(AIBOX_ERR_MEMORY, 0);
    EXPECT_NE(AIBOX_ERR_CONFIG, 0);
    EXPECT_NE(AIBOX_ERR_IO_PORT, 0);
    EXPECT_NE(AIBOX_ERR_FATAL, 0);
    EXPECT_NE(AIBOX_ERR_INTERNAL, 0);
}

TEST(FfiErrorCodesTest, ErrorCodesAreDistinct) {
    std::vector<int> codes = {
        AIBOX_OK,
        AIBOX_ERR_INVALID_PARAM,
        AIBOX_ERR_INVALID_HANDLE,
        AIBOX_ERR_NOT_INITIALIZED,
        AIBOX_ERR_ALREADY_INITIALIZED,
        AIBOX_ERR_CPU,
        AIBOX_ERR_DMA,
        AIBOX_ERR_MEMORY,
        AIBOX_ERR_CONFIG,
        AIBOX_ERR_IO_PORT,
        AIBOX_ERR_FATAL,
        AIBOX_ERR_INTERNAL
    };

    for (size_t i = 0; i < codes.size(); ++i) {
        for (size_t j = i + 1; j < codes.size(); ++j) {
            EXPECT_NE(codes[i], codes[j])
                << "Codes at " << i << " and " << j << " are the same";
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Error Storage Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(FfiErrorStorageTest, ClearErrorWorks) {
    ffi::set_error("some error");
    ffi::clear_error();

    EXPECT_STREQ(ffi::get_error(), "");
}

TEST(FfiErrorStorageTest, SetErrorStoresMessage) {
    ffi::set_error("test error message");

    EXPECT_STREQ(ffi::get_error(), "test error message");
}

TEST(FfiErrorStorageTest, SetErrorOverwrites) {
    ffi::set_error("first error");
    ffi::set_error("second error");

    EXPECT_STREQ(ffi::get_error(), "second error");
}

TEST(FfiErrorStorageTest, EmptyMessageAllowed) {
    ffi::set_error("some error");
    ffi::set_error("");

    EXPECT_STREQ(ffi::get_error(), "");
}

TEST(FfiErrorStorageTest, SetErrorFmtWorks) {
    ffi::set_error_fmt("Value {} out of range [{}, {}]", 100, 0, 50);

    std::string msg = ffi::get_error();
    EXPECT_NE(msg.find("100"), std::string::npos);
    EXPECT_NE(msg.find("0"), std::string::npos);
    EXPECT_NE(msg.find("50"), std::string::npos);
}

TEST(FfiErrorStorageTest, TruncationWorks) {
    // Create a message larger than the buffer
    std::string long_msg(3000, 'x');
    ffi::set_error(long_msg.c_str());

    EXPECT_TRUE(ffi::error_truncated());

    std::string stored = ffi::get_error();
    EXPECT_LT(stored.length(), long_msg.length());
    EXPECT_EQ(stored.substr(stored.length() - 3), "...");
}

TEST(FfiErrorStorageTest, NoTruncationForShortMessage) {
    ffi::set_error("short message");

    EXPECT_FALSE(ffi::error_truncated());
}

TEST(FfiErrorStorageTest, ClearErrorResetsTruncation) {
    std::string long_msg(3000, 'x');
    ffi::set_error(long_msg.c_str());
    ffi::clear_error();

    EXPECT_FALSE(ffi::error_truncated());
}

// ─────────────────────────────────────────────────────────────────────────────
// Thread-Local Storage Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(FfiThreadLocalTest, ErrorsAreThreadLocal) {
    ffi::set_error("main thread error");

    std::string other_thread_saw;
    std::thread t([&]() {
        // Other thread should see empty error
        other_thread_saw = ffi::get_error();

        // Set error in other thread
        ffi::set_error("other thread error");
    });
    t.join();

    // Main thread error should be unchanged
    EXPECT_STREQ(ffi::get_error(), "main thread error");

    // Other thread started with empty error
    EXPECT_EQ(other_thread_saw, "");
}

TEST(FfiThreadLocalTest, TruncationIsThreadLocal) {
    std::string long_msg(3000, 'x');
    ffi::set_error(long_msg.c_str());

    bool other_thread_truncated = true;
    std::thread t([&]() {
        other_thread_truncated = ffi::error_truncated();
    });
    t.join();

    EXPECT_TRUE(ffi::error_truncated());
    EXPECT_FALSE(other_thread_truncated);
}

// ─────────────────────────────────────────────────────────────────────────────
// safe_call Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(FfiSafeCallTest, ReturnsOkOnSuccess) {
    int result = ffi::safe_call([]() {
        return AIBOX_OK;
    });

    EXPECT_EQ(result, AIBOX_OK);
    EXPECT_STREQ(ffi::get_error(), "");
}

TEST(FfiSafeCallTest, PassesThroughReturnCode) {
    int result = ffi::safe_call([]() {
        return AIBOX_ERR_INVALID_PARAM;
    });

    EXPECT_EQ(result, AIBOX_ERR_INVALID_PARAM);
}

TEST(FfiSafeCallTest, CatchesIllegalCpuStateException) {
    int result = ffi::safe_call([]() -> int {
        throw IllegalCpuStateException("invalid opcode", 0x1000, 0x08);
    });

    EXPECT_EQ(result, AIBOX_ERR_CPU);
    EXPECT_NE(std::string(ffi::get_error()).find("CPU error"), std::string::npos);
}

TEST(FfiSafeCallTest, CatchesDmaException) {
    int result = ffi::safe_call([]() -> int {
        throw DmaException("transfer failed", 3);
    });

    EXPECT_EQ(result, AIBOX_ERR_DMA);
    EXPECT_NE(std::string(ffi::get_error()).find("DMA error"), std::string::npos);
}

TEST(FfiSafeCallTest, CatchesMemoryAccessException) {
    int result = ffi::safe_call([]() -> int {
        throw MemoryAccessException(0xDEADBEEF, 4);
    });

    EXPECT_EQ(result, AIBOX_ERR_MEMORY);

    std::string error = ffi::get_error();
    EXPECT_NE(error.find("Memory error"), std::string::npos);
    EXPECT_NE(error.find("DEADBEEF"), std::string::npos);
}

TEST(FfiSafeCallTest, CatchesConfigException) {
    int result = ffi::safe_call([]() -> int {
        throw ConfigException("dosbox", "unknown key");
    });

    EXPECT_EQ(result, AIBOX_ERR_CONFIG);
    EXPECT_NE(std::string(ffi::get_error()).find("Config error"), std::string::npos);
}

TEST(FfiSafeCallTest, CatchesIoPortException) {
    int result = ffi::safe_call([]() -> int {
        throw IoPortException(0x3D4, "invalid write");
    });

    EXPECT_EQ(result, AIBOX_ERR_IO_PORT);

    std::string error = ffi::get_error();
    EXPECT_NE(error.find("I/O error"), std::string::npos);
    EXPECT_NE(error.find("03D4"), std::string::npos);
}

TEST(FfiSafeCallTest, CatchesFatalException) {
    int result = ffi::safe_call([]() -> int {
        throw FatalException("critical failure", "cpu.cpp", 123);
    });

    EXPECT_EQ(result, AIBOX_ERR_FATAL);
    EXPECT_NE(std::string(ffi::get_error()).find("Fatal"), std::string::npos);
}

TEST(FfiSafeCallTest, CatchesCallbackException) {
    int result = ffi::safe_call([]() -> int {
        throw CallbackException(42, "handler null");
    });

    EXPECT_EQ(result, AIBOX_ERR_INTERNAL);
    EXPECT_NE(std::string(ffi::get_error()).find("Callback error"), std::string::npos);
}

TEST(FfiSafeCallTest, CatchesEmulatorException) {
    int result = ffi::safe_call([]() -> int {
        throw EmulatorException("generic emulator error");
    });

    EXPECT_EQ(result, AIBOX_ERR_INTERNAL);
    EXPECT_NE(std::string(ffi::get_error()).find("Emulator error"), std::string::npos);
}

TEST(FfiSafeCallTest, CatchesBadAlloc) {
    int result = ffi::safe_call([]() -> int {
        throw std::bad_alloc();
    });

    EXPECT_EQ(result, AIBOX_ERR_MEMORY);
    EXPECT_NE(std::string(ffi::get_error()).find("memory"), std::string::npos);
}

TEST(FfiSafeCallTest, CatchesStdException) {
    int result = ffi::safe_call([]() -> int {
        throw std::runtime_error("unexpected error");
    });

    EXPECT_EQ(result, AIBOX_ERR_INTERNAL);
    EXPECT_NE(std::string(ffi::get_error()).find("Unexpected error"), std::string::npos);
}

TEST(FfiSafeCallTest, CatchesUnknownException) {
    int result = ffi::safe_call([]() -> int {
        throw 42;  // Non-standard exception
    });

    EXPECT_EQ(result, AIBOX_ERR_INTERNAL);
    EXPECT_NE(std::string(ffi::get_error()).find("Unknown"), std::string::npos);
}

TEST(FfiSafeCallTest, ClearsErrorBeforeCall) {
    ffi::set_error("previous error");

    int result = ffi::safe_call([]() {
        return AIBOX_OK;
    });

    EXPECT_EQ(result, AIBOX_OK);
    EXPECT_STREQ(ffi::get_error(), "");
}

// ─────────────────────────────────────────────────────────────────────────────
// error_code_string Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(FfiErrorCodeStringTest, OkReturnsOK) {
    EXPECT_STREQ(ffi::error_code_string(AIBOX_OK), "OK");
}

TEST(FfiErrorCodeStringTest, AllCodesHaveStrings) {
    EXPECT_STRNE(ffi::error_code_string(AIBOX_ERR_INVALID_PARAM), "Unknown error");
    EXPECT_STRNE(ffi::error_code_string(AIBOX_ERR_INVALID_HANDLE), "Unknown error");
    EXPECT_STRNE(ffi::error_code_string(AIBOX_ERR_NOT_INITIALIZED), "Unknown error");
    EXPECT_STRNE(ffi::error_code_string(AIBOX_ERR_ALREADY_INITIALIZED), "Unknown error");
    EXPECT_STRNE(ffi::error_code_string(AIBOX_ERR_CPU), "Unknown error");
    EXPECT_STRNE(ffi::error_code_string(AIBOX_ERR_DMA), "Unknown error");
    EXPECT_STRNE(ffi::error_code_string(AIBOX_ERR_MEMORY), "Unknown error");
    EXPECT_STRNE(ffi::error_code_string(AIBOX_ERR_CONFIG), "Unknown error");
    EXPECT_STRNE(ffi::error_code_string(AIBOX_ERR_IO_PORT), "Unknown error");
    EXPECT_STRNE(ffi::error_code_string(AIBOX_ERR_FATAL), "Unknown error");
    EXPECT_STRNE(ffi::error_code_string(AIBOX_ERR_INTERNAL), "Unknown error");
}

TEST(FfiErrorCodeStringTest, UnknownCodeReturnsUnknown) {
    EXPECT_STREQ(ffi::error_code_string(12345), "Unknown error");
    EXPECT_STREQ(ffi::error_code_string(-12345), "Unknown error");
}

// ─────────────────────────────────────────────────────────────────────────────
// C API Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(FfiCApiTest, AiboxLastErrorWorks) {
    ffi::set_error("C API test error");

    EXPECT_STREQ(aibox_ffi_last_error(), "C API test error");
}

TEST(FfiCApiTest, AiboxErrorTruncatedWorks) {
    ffi::clear_error();
    EXPECT_EQ(aibox_ffi_error_truncated(), 0);

    std::string long_msg(3000, 'x');
    ffi::set_error(long_msg.c_str());
    EXPECT_EQ(aibox_ffi_error_truncated(), 1);
}

TEST(FfiCApiTest, AiboxClearErrorWorks) {
    ffi::set_error("to be cleared");
    aibox_ffi_clear_error();

    EXPECT_STREQ(aibox_ffi_last_error(), "");
}

TEST(FfiCApiTest, AiboxErrorStringWorks) {
    EXPECT_STREQ(aibox_ffi_error_string(AIBOX_OK), "OK");
    EXPECT_STREQ(aibox_ffi_error_string(AIBOX_ERR_CPU), "CPU error");
    EXPECT_STREQ(aibox_ffi_error_string(99999), "Unknown error");
}

// ─────────────────────────────────────────────────────────────────────────────
// Integration Tests
// ─────────────────────────────────────────────────────────────────────────────

// Simulates an FFI function pattern
static int mock_ffi_function(int* out_value, int input) {
    return ffi::safe_call([&]() {
        if (!out_value) {
            ffi::set_error("Null output pointer");
            return AIBOX_ERR_INVALID_PARAM;
        }

        if (input < 0) {
            throw ConfigException("Invalid input value");
        }

        if (input > 1000) {
            throw MemoryAccessException(static_cast<uint32_t>(input), 4);
        }

        *out_value = input * 2;
        return AIBOX_OK;
    });
}

TEST(FfiIntegrationTest, MockFfiFunctionSuccess) {
    int value = 0;
    int result = mock_ffi_function(&value, 21);

    EXPECT_EQ(result, AIBOX_OK);
    EXPECT_EQ(value, 42);
}

TEST(FfiIntegrationTest, MockFfiFunctionNullPointer) {
    int result = mock_ffi_function(nullptr, 21);

    EXPECT_EQ(result, AIBOX_ERR_INVALID_PARAM);
    EXPECT_NE(std::string(ffi::get_error()).find("Null"), std::string::npos);
}

TEST(FfiIntegrationTest, MockFfiFunctionNegativeInput) {
    int value = 0;
    int result = mock_ffi_function(&value, -5);

    EXPECT_EQ(result, AIBOX_ERR_CONFIG);
    EXPECT_NE(std::string(ffi::get_error()).find("Config error"), std::string::npos);
}

TEST(FfiIntegrationTest, MockFfiFunctionLargeInput) {
    int value = 0;
    int result = mock_ffi_function(&value, 2000);

    EXPECT_EQ(result, AIBOX_ERR_MEMORY);
    EXPECT_NE(std::string(ffi::get_error()).find("Memory error"), std::string::npos);
}

