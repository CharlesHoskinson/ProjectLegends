/**
 * @file test_negative.cpp
 * @brief Negative tests - invalid operations and error handling.
 *
 * Tests that the API gracefully handles:
 * - Invalid handles
 * - Operations in wrong state
 * - Invalid parameters
 * - Double operations (create/destroy)
 * - Operations on destroyed handles
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include <pal/platform.h>
#include <vector>
#include <cstring>

class NegativeTest : public ::testing::Test {
protected:
    void SetUp() override {
        pal::Platform::shutdown();
        pal::Platform::initialize(pal::Backend::Headless);
        legends_destroy(reinterpret_cast<legends_handle>(1));
    }

    void TearDown() override {
        pal::Platform::shutdown();
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// Invalid Handle Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(NegativeTest, AllAPIsRejectNullHandle) {
    legends_step_result_t step_result;
    size_t size_out;
    uint64_t u64_out;
    uint16_t u16_out;
    uint8_t u8_out;
    int int_out;
    uint8_t hash[32];
    legends_config_t config;
    legends_text_info_t info;
    uint8_t data[16] = {0};

    EXPECT_EQ(legends_step_ms(nullptr, 10, &step_result), LEGENDS_ERR_NULL_HANDLE);
    EXPECT_EQ(legends_step_cycles(nullptr, 1000, &step_result), LEGENDS_ERR_NULL_HANDLE);
    EXPECT_EQ(legends_reset(nullptr), LEGENDS_ERR_NULL_HANDLE);
    EXPECT_EQ(legends_get_config(nullptr, &config), LEGENDS_ERR_NULL_HANDLE);
    EXPECT_EQ(legends_get_emu_time(nullptr, &u64_out), LEGENDS_ERR_NULL_HANDLE);
    EXPECT_EQ(legends_get_total_cycles(nullptr, &u64_out), LEGENDS_ERR_NULL_HANDLE);
    EXPECT_EQ(legends_capture_text(nullptr, nullptr, 0, &size_out, &info), LEGENDS_ERR_NULL_HANDLE);
    EXPECT_EQ(legends_capture_rgb(nullptr, nullptr, 0, &size_out, &u16_out, &u16_out), LEGENDS_ERR_NULL_HANDLE);
    EXPECT_EQ(legends_is_frame_dirty(nullptr, &int_out), LEGENDS_ERR_NULL_HANDLE);
    EXPECT_EQ(legends_get_cursor(nullptr, &u8_out, &u8_out, &int_out), LEGENDS_ERR_NULL_HANDLE);
    EXPECT_EQ(legends_key_event(nullptr, 0x1E, 1), LEGENDS_ERR_NULL_HANDLE);
    EXPECT_EQ(legends_key_event_ext(nullptr, 0x4D, 1), LEGENDS_ERR_NULL_HANDLE);
    EXPECT_EQ(legends_text_input(nullptr, "test"), LEGENDS_ERR_NULL_HANDLE);
    EXPECT_EQ(legends_mouse_event(nullptr, 0, 0, 0), LEGENDS_ERR_NULL_HANDLE);
    EXPECT_EQ(legends_save_state(nullptr, nullptr, 0, &size_out), LEGENDS_ERR_NULL_HANDLE);
    EXPECT_EQ(legends_load_state(nullptr, data, sizeof(data)), LEGENDS_ERR_NULL_HANDLE);
    EXPECT_EQ(legends_get_state_hash(nullptr, hash), LEGENDS_ERR_NULL_HANDLE);
    EXPECT_EQ(legends_verify_determinism(nullptr, 1000, &int_out), LEGENDS_ERR_NULL_HANDLE);
}

TEST_F(NegativeTest, DestroyNullHandleIsOk) {
    // Destroying null should be a no-op, not an error
    legends_error_t err = legends_destroy(nullptr);
    EXPECT_EQ(err, LEGENDS_OK);
}

TEST_F(NegativeTest, InvalidFakeHandle) {
    // Create a fake handle that was never returned by create
    legends_handle fake = reinterpret_cast<legends_handle>(static_cast<uintptr_t>(0xDEADBEEF));

    // Operations should fail gracefully (or succeed if implementation doesn't validate)
    // The key is no crash
    legends_step_result_t result;
    legends_error_t err = legends_step_cycles(fake, 1000, &result);
    // Implementation-dependent: might be NULL_HANDLE, INVALID_STATE, or even OK
    // The test passes if it doesn't crash
    (void)err;
}

// ─────────────────────────────────────────────────────────────────────────────
// Double Operation Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(NegativeTest, DoubleCreateReturnsError) {
    legends_handle handle1 = nullptr;
    legends_error_t err1 = legends_create(nullptr, &handle1);
    ASSERT_EQ(err1, LEGENDS_OK);

    // Second create should fail
    legends_handle handle2 = nullptr;
    legends_error_t err2 = legends_create(nullptr, &handle2);
    EXPECT_EQ(err2, LEGENDS_ERR_ALREADY_CREATED);
    EXPECT_EQ(handle2, nullptr);

    legends_destroy(handle1);
}

TEST_F(NegativeTest, DoubleDestroyIsSafe) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    legends_error_t err1 = legends_destroy(handle);
    EXPECT_EQ(err1, LEGENDS_OK);

    // Second destroy with same (now invalid) handle
    // This tests that implementation handles double-free gracefully
    // It might succeed (no-op) or return an error, but must not crash
    legends_error_t err2 = legends_destroy(handle);
    // err2 can be OK or an error, the key is no crash
    (void)err2;
}

// ─────────────────────────────────────────────────────────────────────────────
// Operations on Destroyed Handle
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(NegativeTest, OperationsOnDestroyedHandleDontCrash) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);
    legends_destroy(handle);

    // All these should fail gracefully without crashing
    // The actual error code is implementation-dependent

    legends_step_result_t result;
    legends_step_cycles(handle, 1000, &result);
    legends_step_ms(handle, 10, &result);

    size_t count;
    legends_capture_text(handle, nullptr, 0, &count, nullptr);

    legends_key_event(handle, 0x1E, 1);
    legends_mouse_event(handle, 0, 0, 0);
    legends_reset(handle);

    // If we reach here without crashing, the test passes
    SUCCEED() << "Operations on destroyed handle did not crash";
}

// ─────────────────────────────────────────────────────────────────────────────
// Invalid Parameter Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(NegativeTest, LoadStateWithZeroSize) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    uint8_t data[16] = {0};
    legends_error_t err = legends_load_state(handle, data, 0);
    EXPECT_NE(err, LEGENDS_OK);  // Should fail

    legends_destroy(handle);
}

TEST_F(NegativeTest, LoadStateWithCorruptData) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    // Random garbage data
    uint8_t garbage[1024];
    for (int i = 0; i < 1024; ++i) {
        garbage[i] = static_cast<uint8_t>(i * 17 + 31);
    }

    legends_error_t err = legends_load_state(handle, garbage, sizeof(garbage));
    EXPECT_EQ(err, LEGENDS_ERR_INVALID_STATE);

    legends_destroy(handle);
}

TEST_F(NegativeTest, LoadStateTruncated) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    // Save valid state
    size_t size;
    legends_save_state(handle, nullptr, 0, &size);
    std::vector<uint8_t> state(size);
    legends_save_state(handle, state.data(), size, &size);

    // Try to load truncated state
    // May return INVALID_STATE or BUFFER_TOO_SMALL depending on implementation
    legends_error_t err = legends_load_state(handle, state.data(), size / 2);
    EXPECT_NE(err, LEGENDS_OK) << "Truncated state should not load successfully";

    legends_destroy(handle);
}

TEST_F(NegativeTest, LoadStateModifiedMagic) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    // Save valid state
    size_t size;
    legends_save_state(handle, nullptr, 0, &size);
    std::vector<uint8_t> state(size);
    legends_save_state(handle, state.data(), size, &size);

    // Corrupt the magic/header bytes
    state[0] ^= 0xFF;
    state[1] ^= 0xFF;
    state[2] ^= 0xFF;
    state[3] ^= 0xFF;

    legends_error_t err = legends_load_state(handle, state.data(), size);
    EXPECT_EQ(err, LEGENDS_ERR_INVALID_STATE);

    legends_destroy(handle);
}

// ─────────────────────────────────────────────────────────────────────────────
// Version Mismatch Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(NegativeTest, CreateWithWrongVersion) {
    legends_config_t config = LEGENDS_CONFIG_INIT;
    config.api_version = 0x00000000;  // Version 0.0.0

    legends_handle handle = nullptr;
    legends_error_t err = legends_create(&config, &handle);

    EXPECT_EQ(err, LEGENDS_ERR_VERSION_MISMATCH);
    EXPECT_EQ(handle, nullptr);
}

TEST_F(NegativeTest, CreateWithFutureVersion) {
    legends_config_t config = LEGENDS_CONFIG_INIT;
    config.api_version = (255 << 16) | (255 << 8) | 255;  // Very future version

    legends_handle handle = nullptr;
    legends_error_t err = legends_create(&config, &handle);

    EXPECT_EQ(err, LEGENDS_ERR_VERSION_MISMATCH);
    EXPECT_EQ(handle, nullptr);
}

// ─────────────────────────────────────────────────────────────────────────────
// Buffer Underrun Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(NegativeTest, CaptureTextBufferTooSmall) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    size_t required;
    legends_capture_text(handle, nullptr, 0, &required, nullptr);

    // Allocate way too small buffer
    legends_text_cell_t single_cell;
    size_t actual;
    legends_error_t err = legends_capture_text(handle, &single_cell, 1, &actual, nullptr);

    EXPECT_EQ(err, LEGENDS_ERR_BUFFER_TOO_SMALL);
    EXPECT_EQ(actual, required);  // Should still report required size

    legends_destroy(handle);
}

TEST_F(NegativeTest, CaptureRgbBufferTooSmall) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    size_t required;
    uint16_t width, height;
    legends_capture_rgb(handle, nullptr, 0, &required, &width, &height);

    // Allocate way too small buffer
    uint8_t tiny[3];  // Only one pixel
    size_t actual;
    legends_error_t err = legends_capture_rgb(handle, tiny, sizeof(tiny), &actual, &width, &height);

    EXPECT_EQ(err, LEGENDS_ERR_BUFFER_TOO_SMALL);
    EXPECT_EQ(actual, required);

    legends_destroy(handle);
}

TEST_F(NegativeTest, SaveStateBufferTooSmall) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    size_t required;
    legends_save_state(handle, nullptr, 0, &required);

    // Allocate undersized buffer
    std::vector<uint8_t> small(required / 10);
    size_t actual;
    legends_error_t err = legends_save_state(handle, small.data(), small.size(), &actual);

    EXPECT_EQ(err, LEGENDS_ERR_BUFFER_TOO_SMALL);
    EXPECT_EQ(actual, required);

    legends_destroy(handle);
}

// ─────────────────────────────────────────────────────────────────────────────
// Recovery After Error
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(NegativeTest, RecoverAfterFailedOperation) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    // Cause an error (load invalid state)
    uint8_t garbage[16] = {0};
    legends_error_t err = legends_load_state(handle, garbage, sizeof(garbage));
    EXPECT_EQ(err, LEGENDS_ERR_INVALID_STATE);

    // Instance should still be usable
    legends_step_result_t result;
    err = legends_step_cycles(handle, 1000, &result);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(result.cycles_executed, 1000u);

    // Capture should work
    size_t count;
    err = legends_capture_text(handle, nullptr, 0, &count, nullptr);
    EXPECT_EQ(err, LEGENDS_OK);

    legends_destroy(handle);
}

TEST_F(NegativeTest, RecoverAfterMultipleErrors) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    // Cause multiple errors
    for (int i = 0; i < 10; ++i) {
        uint8_t garbage[16] = {0};
        legends_load_state(handle, garbage, sizeof(garbage));
        legends_capture_text(handle, nullptr, 0, nullptr, nullptr);  // Null pointer error
    }

    // Instance should still work
    legends_step_result_t result;
    legends_error_t err = legends_step_cycles(handle, 1000, &result);
    EXPECT_EQ(err, LEGENDS_OK);

    legends_destroy(handle);
}

// ─────────────────────────────────────────────────────────────────────────────
// Null Pointer Edge Cases
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(NegativeTest, CaptureTextNullCountOut) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    legends_error_t err = legends_capture_text(handle, nullptr, 0, nullptr, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_POINTER);

    legends_destroy(handle);
}

TEST_F(NegativeTest, CaptureRgbNullSizeOut) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    uint16_t width, height;
    legends_error_t err = legends_capture_rgb(handle, nullptr, 0, nullptr, &width, &height);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_POINTER);

    legends_destroy(handle);
}

TEST_F(NegativeTest, GetCursorPartialNullPointers) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    uint8_t x, y;
    int visible;

    // API allows partial null pointers for get_cursor (to query only some values)
    // So these should succeed
    EXPECT_EQ(legends_get_cursor(handle, nullptr, &y, &visible), LEGENDS_OK);
    EXPECT_EQ(legends_get_cursor(handle, &x, nullptr, &visible), LEGENDS_OK);
    EXPECT_EQ(legends_get_cursor(handle, &x, &y, nullptr), LEGENDS_OK);

    // Full query should also work
    EXPECT_EQ(legends_get_cursor(handle, &x, &y, &visible), LEGENDS_OK);

    legends_destroy(handle);
}

// ─────────────────────────────────────────────────────────────────────────────
// Config Validation Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(NegativeTest, CreateWithInvalidStructSize) {
    legends_config_t config = LEGENDS_CONFIG_INIT;
    config.struct_size = 1;  // Too small

    legends_handle handle = nullptr;
    legends_error_t err = legends_create(&config, &handle);

    EXPECT_EQ(err, LEGENDS_ERR_INVALID_CONFIG);
    EXPECT_EQ(handle, nullptr);
}

TEST_F(NegativeTest, CreateWithZeroStructSize) {
    legends_config_t config = LEGENDS_CONFIG_INIT;
    config.struct_size = 0;

    legends_handle handle = nullptr;
    legends_error_t err = legends_create(&config, &handle);

    EXPECT_EQ(err, LEGENDS_ERR_INVALID_CONFIG);
    EXPECT_EQ(handle, nullptr);
}

// ─────────────────────────────────────────────────────────────────────────────
// Verify Determinism Edge Cases
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(NegativeTest, VerifyDeterminismZeroCycles) {
    legends_handle handle = nullptr;
    legends_config_t config = LEGENDS_CONFIG_INIT;
    config.deterministic = 1;
    legends_create(&config, &handle);

    int is_det;
    legends_error_t err = legends_verify_determinism(handle, 0, &is_det);

    // Zero cycles should still work (trivially deterministic)
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(is_det, 1);

    legends_destroy(handle);
}

TEST_F(NegativeTest, VerifyDeterminismNonDeterministicMode) {
    legends_handle handle = nullptr;
    legends_config_t config = LEGENDS_CONFIG_INIT;
    config.deterministic = 0;  // Non-deterministic mode
    legends_create(&config, &handle);

    int is_det;
    legends_error_t err = legends_verify_determinism(handle, 10000, &is_det);

    // Should still succeed, but may or may not be deterministic
    EXPECT_EQ(err, LEGENDS_OK);

    legends_destroy(handle);
}

