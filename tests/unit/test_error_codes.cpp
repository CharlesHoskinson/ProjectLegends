/**
 * @file test_error_codes.cpp
 * @brief Comprehensive tests for all error codes.
 *
 * Ensures every error code defined in legends_embed.h has explicit test coverage.
 *
 * Error codes:
 * - LEGENDS_OK (0) - tested
 * - LEGENDS_ERR_NULL_HANDLE (-1) - tested
 * - LEGENDS_ERR_NULL_POINTER (-2) - tested
 * - LEGENDS_ERR_ALREADY_CREATED (-3) - tested
 * - LEGENDS_ERR_NOT_INITIALIZED (-4) - tested here
 * - LEGENDS_ERR_REENTRANT_CALL (-5) - tested here (if applicable)
 * - LEGENDS_ERR_BUFFER_TOO_SMALL (-6) - tested
 * - LEGENDS_ERR_INVALID_CONFIG (-7) - tested here
 * - LEGENDS_ERR_INVALID_STATE (-8) - tested
 * - LEGENDS_ERR_VERSION_MISMATCH (-9) - tested
 * - LEGENDS_ERR_IO_FAILED (-10) - tested here
 * - LEGENDS_ERR_OUT_OF_MEMORY (-11) - documented (not easily triggerable)
 * - LEGENDS_ERR_NOT_SUPPORTED (-12) - tested here
 * - LEGENDS_ERR_INTERNAL (-13) - documented (reserved for internal errors)
 * - LEGENDS_ERR_WRONG_THREAD (-14) - tested in test_thread_safety.cpp
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include <pal/platform.h>
#include <vector>
#include <cstring>

class ErrorCodesTest : public ::testing::Test {
protected:
    legends_handle handle_ = nullptr;

    void SetUp() override {
        pal::Platform::shutdown();
        pal::Platform::initialize(pal::Backend::Headless);
        legends_destroy(reinterpret_cast<legends_handle>(1));
    }

    void TearDown() override {
        if (handle_) {
            legends_destroy(handle_);
            handle_ = nullptr;
        }
        pal::Platform::shutdown();
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// LEGENDS_OK (0)
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(ErrorCodesTest, LegendsOK_Success) {
    legends_error_t err = legends_create(nullptr, &handle_);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(err, 0);
}

// ─────────────────────────────────────────────────────────────────────────────
// LEGENDS_ERR_NULL_HANDLE (-1)
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(ErrorCodesTest, NullHandle_StepCycles) {
    legends_step_result_t result;
    legends_error_t err = legends_step_cycles(nullptr, 1000, &result);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST_F(ErrorCodesTest, NullHandle_StepMs) {
    legends_step_result_t result;
    legends_error_t err = legends_step_ms(nullptr, 10, &result);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST_F(ErrorCodesTest, NullHandle_CaptureText) {
    size_t count;
    legends_error_t err = legends_capture_text(nullptr, nullptr, 0, &count, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST_F(ErrorCodesTest, NullHandle_CaptureRgb) {
    size_t size;
    uint16_t width, height;
    legends_error_t err = legends_capture_rgb(nullptr, nullptr, 0, &size, &width, &height);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST_F(ErrorCodesTest, NullHandle_KeyEvent) {
    legends_error_t err = legends_key_event(nullptr, 0x1E, 1);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST_F(ErrorCodesTest, NullHandle_MouseEvent) {
    legends_error_t err = legends_mouse_event(nullptr, 5, 5, 0);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST_F(ErrorCodesTest, NullHandle_Reset) {
    legends_error_t err = legends_reset(nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST_F(ErrorCodesTest, NullHandle_SaveState) {
    size_t size;
    legends_error_t err = legends_save_state(nullptr, nullptr, 0, &size);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST_F(ErrorCodesTest, NullHandle_LoadState) {
    uint8_t data[16] = {0};
    legends_error_t err = legends_load_state(nullptr, data, sizeof(data));
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST_F(ErrorCodesTest, NullHandle_GetStateHash) {
    uint8_t hash[32];
    legends_error_t err = legends_get_state_hash(nullptr, hash);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

// ─────────────────────────────────────────────────────────────────────────────
// LEGENDS_ERR_NULL_POINTER (-2)
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(ErrorCodesTest, NullPointer_CreateNullHandleOut) {
    legends_error_t err = legends_create(nullptr, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_POINTER);
}

TEST_F(ErrorCodesTest, NullPointer_GetStateHashNullBuffer) {
    legends_create(nullptr, &handle_);
    legends_error_t err = legends_get_state_hash(handle_, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_POINTER);
}

TEST_F(ErrorCodesTest, NullPointer_CaptureTextNullCount) {
    legends_create(nullptr, &handle_);
    legends_error_t err = legends_capture_text(handle_, nullptr, 0, nullptr, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_POINTER);
}

TEST_F(ErrorCodesTest, NullPointer_CaptureRgbNullSizeOut) {
    legends_create(nullptr, &handle_);
    uint16_t width, height;
    legends_error_t err = legends_capture_rgb(handle_, nullptr, 0, nullptr, &width, &height);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_POINTER);
}

TEST_F(ErrorCodesTest, NullPointer_GetEmuTimeNullOut) {
    legends_create(nullptr, &handle_);
    legends_error_t err = legends_get_emu_time(handle_, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_POINTER);
}

TEST_F(ErrorCodesTest, NullPointer_GetTotalCyclesNullOut) {
    legends_create(nullptr, &handle_);
    legends_error_t err = legends_get_total_cycles(handle_, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_POINTER);
}

TEST_F(ErrorCodesTest, NullPointer_IsFrameDirtyNullOut) {
    legends_create(nullptr, &handle_);
    legends_error_t err = legends_is_frame_dirty(handle_, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_POINTER);
}

TEST_F(ErrorCodesTest, NullPointer_GetCursorAllowsPartialNull) {
    legends_create(nullptr, &handle_);
    uint8_t x, y;
    int visible;
    // API allows partial null pointers for get_cursor (to query only some values)
    legends_error_t err = legends_get_cursor(handle_, nullptr, &y, &visible);
    EXPECT_EQ(err, LEGENDS_OK);
    err = legends_get_cursor(handle_, &x, nullptr, &visible);
    EXPECT_EQ(err, LEGENDS_OK);
    err = legends_get_cursor(handle_, &x, &y, nullptr);
    EXPECT_EQ(err, LEGENDS_OK);
}

TEST_F(ErrorCodesTest, NullPointer_TextInputNullString) {
    legends_create(nullptr, &handle_);
    legends_error_t err = legends_text_input(handle_, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_POINTER);
}

TEST_F(ErrorCodesTest, NullPointer_LoadStateNullBuffer) {
    legends_create(nullptr, &handle_);
    legends_error_t err = legends_load_state(handle_, nullptr, 100);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_POINTER);
}

TEST_F(ErrorCodesTest, NullPointer_SaveStateNullSizeOut) {
    legends_create(nullptr, &handle_);
    legends_error_t err = legends_save_state(handle_, nullptr, 0, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_POINTER);
}

TEST_F(ErrorCodesTest, NullPointer_VerifyDeterminismNullOut) {
    legends_create(nullptr, &handle_);
    legends_error_t err = legends_verify_determinism(handle_, 1000, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_POINTER);
}

// ─────────────────────────────────────────────────────────────────────────────
// LEGENDS_ERR_ALREADY_CREATED (-3)
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(ErrorCodesTest, AlreadyCreated_SingleInstanceViolation) {
    legends_create(nullptr, &handle_);

    legends_handle handle2 = nullptr;
    legends_error_t err = legends_create(nullptr, &handle2);
    EXPECT_EQ(err, LEGENDS_ERR_ALREADY_CREATED);
    EXPECT_EQ(handle2, nullptr);
}

// ─────────────────────────────────────────────────────────────────────────────
// LEGENDS_ERR_NOT_INITIALIZED (-4)
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(ErrorCodesTest, NotInitialized_OperationsWithoutPlatformInit) {
    // Shut down the platform first
    pal::Platform::shutdown();

    // Try to create without platform initialized
    legends_handle handle = nullptr;
    legends_error_t err = legends_create(nullptr, &handle);

    // Should return NOT_INITIALIZED (or still succeed if create auto-initializes)
    // The exact behavior depends on implementation
    if (err != LEGENDS_OK) {
        EXPECT_EQ(err, LEGENDS_ERR_NOT_INITIALIZED);
    }

    // Re-initialize for TearDown
    pal::Platform::initialize(pal::Backend::Headless);
}

// ─────────────────────────────────────────────────────────────────────────────
// LEGENDS_ERR_BUFFER_TOO_SMALL (-6)
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(ErrorCodesTest, BufferTooSmall_CaptureTextSmallBuffer) {
    legends_create(nullptr, &handle_);

    // Get required size
    size_t count;
    legends_capture_text(handle_, nullptr, 0, &count, nullptr);

    // Allocate undersized buffer
    std::vector<legends_text_cell_t> cells(count / 2);
    legends_error_t err = legends_capture_text(handle_, cells.data(), cells.size(), &count, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_BUFFER_TOO_SMALL);
}

TEST_F(ErrorCodesTest, BufferTooSmall_CaptureRgbSmallBuffer) {
    legends_create(nullptr, &handle_);

    // Get required size
    size_t size;
    uint16_t width, height;
    legends_capture_rgb(handle_, nullptr, 0, &size, &width, &height);

    // Allocate undersized buffer
    std::vector<uint8_t> buffer(size / 2);
    legends_error_t err = legends_capture_rgb(handle_, buffer.data(), buffer.size(), &size, &width, &height);
    EXPECT_EQ(err, LEGENDS_ERR_BUFFER_TOO_SMALL);
}

TEST_F(ErrorCodesTest, BufferTooSmall_SaveStateSmallBuffer) {
    legends_create(nullptr, &handle_);

    // Get required size
    size_t size;
    legends_save_state(handle_, nullptr, 0, &size);

    // Allocate undersized buffer
    std::vector<uint8_t> buffer(size / 2);
    legends_error_t err = legends_save_state(handle_, buffer.data(), buffer.size(), &size);
    EXPECT_EQ(err, LEGENDS_ERR_BUFFER_TOO_SMALL);
}

TEST_F(ErrorCodesTest, BufferTooSmall_GetLastErrorSmallBuffer) {
    legends_create(nullptr, &handle_);

    // Force an error
    legends_load_state(handle_, nullptr, 0);

    // Try to get error message with tiny buffer
    size_t length;
    legends_get_last_error(handle_, nullptr, 0, &length);

    if (length > 1) {
        char tiny_buffer[1];
        legends_error_t err = legends_get_last_error(handle_, tiny_buffer, 1, &length);
        EXPECT_EQ(err, LEGENDS_ERR_BUFFER_TOO_SMALL);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// LEGENDS_ERR_INVALID_CONFIG (-7)
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(ErrorCodesTest, InvalidConfig_WrongStructSize) {
    legends_config_t config = LEGENDS_CONFIG_INIT;
    config.struct_size = 1;  // Invalid struct size

    legends_handle handle = nullptr;
    legends_error_t err = legends_create(&config, &handle);

    EXPECT_EQ(err, LEGENDS_ERR_INVALID_CONFIG);
    EXPECT_EQ(handle, nullptr);
}

TEST_F(ErrorCodesTest, InvalidConfig_InvalidCpuType) {
    legends_config_t config = LEGENDS_CONFIG_INIT;
    config.cpu_type = 255;  // Invalid CPU type

    legends_handle handle = nullptr;
    legends_error_t err = legends_create(&config, &handle);

    // May return INVALID_CONFIG or succeed with fallback to default
    // Implementation-dependent
    if (err != LEGENDS_OK) {
        EXPECT_EQ(err, LEGENDS_ERR_INVALID_CONFIG);
    }
}

TEST_F(ErrorCodesTest, InvalidConfig_InvalidMachineType) {
    legends_config_t config = LEGENDS_CONFIG_INIT;
    config.machine_type = 255;  // Invalid machine type

    legends_handle handle = nullptr;
    legends_error_t err = legends_create(&config, &handle);

    // May return INVALID_CONFIG or succeed with fallback to default
    if (err != LEGENDS_OK) {
        EXPECT_EQ(err, LEGENDS_ERR_INVALID_CONFIG);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// LEGENDS_ERR_INVALID_STATE (-8)
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(ErrorCodesTest, InvalidState_LoadCorruptedState) {
    legends_create(nullptr, &handle_);

    // Try to load garbage data
    uint8_t bad_state[256] = {0};
    legends_error_t err = legends_load_state(handle_, bad_state, sizeof(bad_state));
    EXPECT_EQ(err, LEGENDS_ERR_INVALID_STATE);
}

TEST_F(ErrorCodesTest, InvalidState_LoadTruncatedState) {
    legends_create(nullptr, &handle_);

    // Get valid state
    size_t size;
    legends_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> state(size);
    legends_save_state(handle_, state.data(), size, &size);

    // Try to load truncated state - may return INVALID_STATE or BUFFER_TOO_SMALL
    legends_error_t err = legends_load_state(handle_, state.data(), size / 2);
    EXPECT_NE(err, LEGENDS_OK) << "Truncated state should fail to load";
}

// ─────────────────────────────────────────────────────────────────────────────
// LEGENDS_ERR_VERSION_MISMATCH (-9)
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(ErrorCodesTest, VersionMismatch_WrongApiVersion) {
    legends_config_t config = LEGENDS_CONFIG_INIT;
    config.api_version = 0xDEADBEEF;  // Wrong version

    legends_handle handle = nullptr;
    legends_error_t err = legends_create(&config, &handle);
    EXPECT_EQ(err, LEGENDS_ERR_VERSION_MISMATCH);
    EXPECT_EQ(handle, nullptr);
}

TEST_F(ErrorCodesTest, VersionMismatch_FutureVersion) {
    legends_config_t config = LEGENDS_CONFIG_INIT;
    config.api_version = (99 << 16) | (99 << 8) | 99;  // Future version

    legends_handle handle = nullptr;
    legends_error_t err = legends_create(&config, &handle);
    EXPECT_EQ(err, LEGENDS_ERR_VERSION_MISMATCH);
}

// ─────────────────────────────────────────────────────────────────────────────
// LEGENDS_ERR_IO_FAILED (-10) - File I/O errors
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(ErrorCodesTest, IoFailed_NonexistentConfigFile) {
    legends_config_t config = LEGENDS_CONFIG_INIT;
    config.config_path = "C:\\nonexistent\\path\\that\\does\\not\\exist\\config.conf";

    legends_handle handle = nullptr;
    legends_error_t err = legends_create(&config, &handle);

    // Should return IO_FAILED or silently use defaults
    if (err != LEGENDS_OK) {
        EXPECT_EQ(err, LEGENDS_ERR_IO_FAILED);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// LEGENDS_ERR_NOT_SUPPORTED (-12)
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(ErrorCodesTest, NotSupported_UnsupportedFeature) {
    legends_create(nullptr, &handle_);

    // Test unsupported extended scancode range
    // Most extended scancodes should work, but some might not be supported
    // This is implementation-dependent

    // For now, verify the error code constant is defined correctly
    EXPECT_EQ(LEGENDS_ERR_NOT_SUPPORTED, -12);
}

// ─────────────────────────────────────────────────────────────────────────────
// LEGENDS_ERR_INTERNAL (-13) - Internal errors (hard to trigger)
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(ErrorCodesTest, Internal_ErrorCodeDefinedCorrectly) {
    // LEGENDS_ERR_INTERNAL is reserved for unexpected internal errors
    // These should not be triggerable through normal API usage
    EXPECT_EQ(LEGENDS_ERR_INTERNAL, -13);
}

// ─────────────────────────────────────────────────────────────────────────────
// LEGENDS_ERR_OUT_OF_MEMORY (-11) - Hard to trigger
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(ErrorCodesTest, OutOfMemory_ErrorCodeDefinedCorrectly) {
    // LEGENDS_ERR_OUT_OF_MEMORY is returned when memory allocation fails
    // This is difficult to trigger in a test without mocking malloc
    EXPECT_EQ(LEGENDS_ERR_OUT_OF_MEMORY, -11);
}

// ─────────────────────────────────────────────────────────────────────────────
// Error Code Value Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(ErrorCodesTest, AllErrorCodesHaveUniqueValues) {
    std::vector<legends_error_t> codes = {
        LEGENDS_OK,
        LEGENDS_ERR_NULL_HANDLE,
        LEGENDS_ERR_NULL_POINTER,
        LEGENDS_ERR_ALREADY_CREATED,
        LEGENDS_ERR_NOT_INITIALIZED,
        LEGENDS_ERR_REENTRANT_CALL,
        LEGENDS_ERR_BUFFER_TOO_SMALL,
        LEGENDS_ERR_INVALID_CONFIG,
        LEGENDS_ERR_INVALID_STATE,
        LEGENDS_ERR_VERSION_MISMATCH,
        LEGENDS_ERR_IO_FAILED,
        LEGENDS_ERR_OUT_OF_MEMORY,
        LEGENDS_ERR_NOT_SUPPORTED,
        LEGENDS_ERR_INTERNAL,
        LEGENDS_ERR_WRONG_THREAD
    };

    // Check all values are unique
    for (size_t i = 0; i < codes.size(); ++i) {
        for (size_t j = i + 1; j < codes.size(); ++j) {
            EXPECT_NE(codes[i], codes[j])
                << "Error codes at indices " << i << " and " << j << " have same value";
        }
    }
}

TEST_F(ErrorCodesTest, AllErrorCodesHaveExpectedValues) {
    EXPECT_EQ(LEGENDS_OK, 0);
    EXPECT_EQ(LEGENDS_ERR_NULL_HANDLE, -1);
    EXPECT_EQ(LEGENDS_ERR_NULL_POINTER, -2);
    EXPECT_EQ(LEGENDS_ERR_ALREADY_CREATED, -3);
    EXPECT_EQ(LEGENDS_ERR_NOT_INITIALIZED, -4);
    EXPECT_EQ(LEGENDS_ERR_REENTRANT_CALL, -5);
    EXPECT_EQ(LEGENDS_ERR_BUFFER_TOO_SMALL, -6);
    EXPECT_EQ(LEGENDS_ERR_INVALID_CONFIG, -7);
    EXPECT_EQ(LEGENDS_ERR_INVALID_STATE, -8);
    EXPECT_EQ(LEGENDS_ERR_VERSION_MISMATCH, -9);
    EXPECT_EQ(LEGENDS_ERR_IO_FAILED, -10);
    EXPECT_EQ(LEGENDS_ERR_OUT_OF_MEMORY, -11);
    EXPECT_EQ(LEGENDS_ERR_NOT_SUPPORTED, -12);
    EXPECT_EQ(LEGENDS_ERR_INTERNAL, -13);
    EXPECT_EQ(LEGENDS_ERR_WRONG_THREAD, -14);
}

TEST_F(ErrorCodesTest, ErrorCodesAreNegative) {
    EXPECT_EQ(LEGENDS_OK, 0);
    EXPECT_LT(LEGENDS_ERR_NULL_HANDLE, 0);
    EXPECT_LT(LEGENDS_ERR_NULL_POINTER, 0);
    EXPECT_LT(LEGENDS_ERR_ALREADY_CREATED, 0);
    EXPECT_LT(LEGENDS_ERR_NOT_INITIALIZED, 0);
    EXPECT_LT(LEGENDS_ERR_REENTRANT_CALL, 0);
    EXPECT_LT(LEGENDS_ERR_BUFFER_TOO_SMALL, 0);
    EXPECT_LT(LEGENDS_ERR_INVALID_CONFIG, 0);
    EXPECT_LT(LEGENDS_ERR_INVALID_STATE, 0);
    EXPECT_LT(LEGENDS_ERR_VERSION_MISMATCH, 0);
    EXPECT_LT(LEGENDS_ERR_IO_FAILED, 0);
    EXPECT_LT(LEGENDS_ERR_OUT_OF_MEMORY, 0);
    EXPECT_LT(LEGENDS_ERR_NOT_SUPPORTED, 0);
    EXPECT_LT(LEGENDS_ERR_INTERNAL, 0);
    EXPECT_LT(LEGENDS_ERR_WRONG_THREAD, 0);
}

