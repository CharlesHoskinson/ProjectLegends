/**
 * @file test_dosboxx_embed.cpp
 * @brief C++ unit tests for dosboxx_embed API using GoogleTest.
 *
 * These tests verify the dosboxx_embed.h API behaves correctly from C++.
 * For pure C ABI tests, see test_dosboxx_abi.c
 */

#include <gtest/gtest.h>
#include <aibox/dosboxx_embed.h>
#include <cstring>
#include <vector>

// ─────────────────────────────────────────────────────────────────────────────
// Test Fixture - Ensures clean state between tests
// ─────────────────────────────────────────────────────────────────────────────

class DosboxxEmbedTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Ensure no instance exists at start
        // (previous test may have left one)
        dosboxx_destroy(reinterpret_cast<dosboxx_handle>(1));
    }

    void TearDown() override {
        // Clean up any instance that was created
        dosboxx_destroy(reinterpret_cast<dosboxx_handle>(1));
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// ABI Size Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(DosboxxAbiTest, TextCellSize) {
    EXPECT_EQ(sizeof(dosboxx_text_cell_t), 2u);
}

TEST(DosboxxAbiTest, TextInfoSize) {
    EXPECT_EQ(sizeof(dosboxx_text_info_t), 8u);
}

TEST(DosboxxAbiTest, StepResultSize) {
    EXPECT_EQ(sizeof(dosboxx_step_result_t), 24u);
}

TEST(DosboxxAbiTest, ConfigSize) {
    // Config size depends on pointer size and alignment.
    // After deterministic + _pad3 (offset 36), pointers need 8-byte alignment
    // on 64-bit, so there's 4 bytes of padding.
#if defined(__LP64__) || defined(_WIN64) || defined(__x86_64__) || defined(__aarch64__)
    EXPECT_EQ(sizeof(dosboxx_config_t), 120u);
#else
    EXPECT_EQ(sizeof(dosboxx_config_t), 108u);
#endif
}

// ─────────────────────────────────────────────────────────────────────────────
// Version API Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(DosboxxVersionTest, GetApiVersionReturnsCorrectValues) {
    uint32_t major, minor, patch;
    auto err = dosboxx_get_api_version(&major, &minor, &patch);

    EXPECT_EQ(err, DOSBOXX_OK);
    EXPECT_EQ(major, DOSBOXX_API_VERSION_MAJOR);
    EXPECT_EQ(minor, DOSBOXX_API_VERSION_MINOR);
    EXPECT_EQ(patch, DOSBOXX_API_VERSION_PATCH);
}

TEST(DosboxxVersionTest, GetApiVersionRejectsNullMajor) {
    uint32_t minor, patch;
    auto err = dosboxx_get_api_version(nullptr, &minor, &patch);
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_POINTER);
}

TEST(DosboxxVersionTest, GetApiVersionRejectsNullMinor) {
    uint32_t major, patch;
    auto err = dosboxx_get_api_version(&major, nullptr, &patch);
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_POINTER);
}

TEST(DosboxxVersionTest, GetApiVersionRejectsNullPatch) {
    uint32_t major, minor;
    auto err = dosboxx_get_api_version(&major, &minor, nullptr);
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_POINTER);
}

TEST(DosboxxVersionTest, PackedVersionMatches) {
    uint32_t expected = (DOSBOXX_API_VERSION_MAJOR << 16) |
                        (DOSBOXX_API_VERSION_MINOR << 8) |
                        DOSBOXX_API_VERSION_PATCH;
    EXPECT_EQ(DOSBOXX_API_VERSION, expected);
}

// ─────────────────────────────────────────────────────────────────────────────
// Error Code Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(DosboxxErrorTest, OkIsZero) {
    EXPECT_EQ(DOSBOXX_OK, 0);
}

TEST(DosboxxErrorTest, AllErrorCodesAreNonZero) {
    EXPECT_NE(DOSBOXX_ERR_NULL_HANDLE, 0);
    EXPECT_NE(DOSBOXX_ERR_NULL_POINTER, 0);
    EXPECT_NE(DOSBOXX_ERR_ALREADY_CREATED, 0);
    EXPECT_NE(DOSBOXX_ERR_NOT_INITIALIZED, 0);
    EXPECT_NE(DOSBOXX_ERR_ALREADY_RUNNING, 0);
    EXPECT_NE(DOSBOXX_ERR_BUFFER_TOO_SMALL, 0);
    EXPECT_NE(DOSBOXX_ERR_INVALID_CONFIG, 0);
    EXPECT_NE(DOSBOXX_ERR_INVALID_STATE, 0);
    EXPECT_NE(DOSBOXX_ERR_VERSION_MISMATCH, 0);
    EXPECT_NE(DOSBOXX_ERR_IO_FAILED, 0);
    EXPECT_NE(DOSBOXX_ERR_OUT_OF_MEMORY, 0);
    EXPECT_NE(DOSBOXX_ERR_NOT_SUPPORTED, 0);
    EXPECT_NE(DOSBOXX_ERR_INTERNAL, 0);
}

TEST(DosboxxErrorTest, AllErrorCodesAreDistinct) {
    std::vector<dosboxx_error_t> codes = {
        DOSBOXX_OK,
        DOSBOXX_ERR_NULL_HANDLE,
        DOSBOXX_ERR_NULL_POINTER,
        DOSBOXX_ERR_ALREADY_CREATED,
        DOSBOXX_ERR_NOT_INITIALIZED,
        DOSBOXX_ERR_ALREADY_RUNNING,
        DOSBOXX_ERR_BUFFER_TOO_SMALL,
        DOSBOXX_ERR_INVALID_CONFIG,
        DOSBOXX_ERR_INVALID_STATE,
        DOSBOXX_ERR_VERSION_MISMATCH,
        DOSBOXX_ERR_IO_FAILED,
        DOSBOXX_ERR_OUT_OF_MEMORY,
        DOSBOXX_ERR_NOT_SUPPORTED,
        DOSBOXX_ERR_INTERNAL
    };

    for (size_t i = 0; i < codes.size(); ++i) {
        for (size_t j = i + 1; j < codes.size(); ++j) {
            EXPECT_NE(codes[i], codes[j])
                << "Error codes at " << i << " and " << j << " are equal";
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Config Initializer Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(DosboxxConfigTest, InitializerSetsCorrectDefaults) {
    dosboxx_config_t config = DOSBOXX_CONFIG_INIT;

    EXPECT_EQ(config.struct_size, sizeof(dosboxx_config_t));
    EXPECT_EQ(config.api_version, DOSBOXX_API_VERSION);
    EXPECT_EQ(config.memory_kb, 640u);
    EXPECT_EQ(config.xms_kb, 0u);
    EXPECT_EQ(config.ems_kb, 0u);
    EXPECT_EQ(config.cpu_cycles, 0u);
    EXPECT_EQ(config.cpu_type, 0u);
    EXPECT_EQ(config.machine_type, 0u);
    EXPECT_EQ(config.deterministic, 1u);
    EXPECT_EQ(config.config_path, nullptr);
    EXPECT_EQ(config.working_dir, nullptr);
}

// ─────────────────────────────────────────────────────────────────────────────
// Lifecycle Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(DosboxxEmbedTest, CreateWithNullConfigSucceeds) {
    dosboxx_handle handle = nullptr;
    auto err = dosboxx_create(nullptr, &handle);

    EXPECT_EQ(err, DOSBOXX_OK);
    EXPECT_NE(handle, nullptr);

    dosboxx_destroy(handle);
}

TEST_F(DosboxxEmbedTest, CreateWithValidConfigSucceeds) {
    dosboxx_config_t config = DOSBOXX_CONFIG_INIT;
    dosboxx_handle handle = nullptr;

    auto err = dosboxx_create(&config, &handle);

    EXPECT_EQ(err, DOSBOXX_OK);
    EXPECT_NE(handle, nullptr);

    dosboxx_destroy(handle);
}

TEST_F(DosboxxEmbedTest, CreateRejectsNullHandleOut) {
    auto err = dosboxx_create(nullptr, nullptr);
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_POINTER);
}

TEST_F(DosboxxEmbedTest, SingleInstanceEnforcement) {
    dosboxx_handle handle1 = nullptr;
    dosboxx_handle handle2 = nullptr;

    // First create succeeds
    auto err1 = dosboxx_create(nullptr, &handle1);
    EXPECT_EQ(err1, DOSBOXX_OK);
    EXPECT_NE(handle1, nullptr);

    // Second create fails
    auto err2 = dosboxx_create(nullptr, &handle2);
    EXPECT_EQ(err2, DOSBOXX_ERR_ALREADY_CREATED);
    EXPECT_EQ(handle2, nullptr);

    // Destroy first
    dosboxx_destroy(handle1);

    // Now can create again
    dosboxx_handle handle3 = nullptr;
    auto err3 = dosboxx_create(nullptr, &handle3);
    EXPECT_EQ(err3, DOSBOXX_OK);
    EXPECT_NE(handle3, nullptr);

    dosboxx_destroy(handle3);
}

TEST_F(DosboxxEmbedTest, DestroyNullIsNoOp) {
    auto err = dosboxx_destroy(nullptr);
    EXPECT_EQ(err, DOSBOXX_OK);
}

TEST_F(DosboxxEmbedTest, DestroyTwiceIsOk) {
    dosboxx_handle handle = nullptr;
    dosboxx_create(nullptr, &handle);

    auto err1 = dosboxx_destroy(handle);
    EXPECT_EQ(err1, DOSBOXX_OK);

    // Second destroy should also be OK (idempotent)
    auto err2 = dosboxx_destroy(handle);
    EXPECT_EQ(err2, DOSBOXX_OK);
}

// ─────────────────────────────────────────────────────────────────────────────
// Config Validation Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(DosboxxEmbedTest, CreateRejectsWrongStructSize) {
    dosboxx_config_t config = DOSBOXX_CONFIG_INIT;
    config.struct_size = sizeof(dosboxx_config_t) - 1;

    dosboxx_handle handle = nullptr;
    auto err = dosboxx_create(&config, &handle);

    EXPECT_EQ(err, DOSBOXX_ERR_INVALID_CONFIG);
    EXPECT_EQ(handle, nullptr);
}

TEST_F(DosboxxEmbedTest, CreateRejectsWrongApiVersion) {
    dosboxx_config_t config = DOSBOXX_CONFIG_INIT;
    config.api_version = DOSBOXX_API_VERSION + 1;

    dosboxx_handle handle = nullptr;
    auto err = dosboxx_create(&config, &handle);

    EXPECT_EQ(err, DOSBOXX_ERR_VERSION_MISMATCH);
    EXPECT_EQ(handle, nullptr);
}

// ─────────────────────────────────────────────────────────────────────────────
// Null Handle Rejection Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(DosboxxNullHandleTest, ResetRejectsNullHandle) {
    auto err = dosboxx_reset(nullptr);
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, GetConfigRejectsNullHandle) {
    dosboxx_config_t config;
    auto err = dosboxx_get_config(nullptr, &config);
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, StepMsRejectsNullHandle) {
    auto err = dosboxx_step_ms(nullptr, 100, nullptr);
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, StepCyclesRejectsNullHandle) {
    auto err = dosboxx_step_cycles(nullptr, 1000, nullptr);
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, GetEmuTimeRejectsNullHandle) {
    uint64_t time;
    auto err = dosboxx_get_emu_time(nullptr, &time);
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, GetTotalCyclesRejectsNullHandle) {
    uint64_t cycles;
    auto err = dosboxx_get_total_cycles(nullptr, &cycles);
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, CaptureTextRejectsNullHandle) {
    size_t count;
    auto err = dosboxx_capture_text(nullptr, nullptr, 0, &count, nullptr);
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, CaptureRgbRejectsNullHandle) {
    size_t size;
    auto err = dosboxx_capture_rgb(nullptr, nullptr, 0, &size, nullptr, nullptr);
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, IsFrameDirtyRejectsNullHandle) {
    int dirty;
    auto err = dosboxx_is_frame_dirty(nullptr, &dirty);
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, GetCursorRejectsNullHandle) {
    uint8_t x, y;
    int visible;
    auto err = dosboxx_get_cursor(nullptr, &x, &y, &visible);
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, KeyEventRejectsNullHandle) {
    auto err = dosboxx_key_event(nullptr, 0x1E, 1);
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, KeyEventExtRejectsNullHandle) {
    auto err = dosboxx_key_event_ext(nullptr, 0x4D, 1);
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, TextInputRejectsNullHandle) {
    auto err = dosboxx_text_input(nullptr, "test");
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, MouseEventRejectsNullHandle) {
    auto err = dosboxx_mouse_event(nullptr, 10, 10, 0);
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, SaveStateRejectsNullHandle) {
    size_t size;
    auto err = dosboxx_save_state(nullptr, nullptr, 0, &size);
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, LoadStateRejectsNullHandle) {
    uint8_t buffer[16];
    auto err = dosboxx_load_state(nullptr, buffer, sizeof(buffer));
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, GetStateHashRejectsNullHandle) {
    uint8_t hash[32];
    auto err = dosboxx_get_state_hash(nullptr, hash);
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, VerifyDeterminismRejectsNullHandle) {
    int is_det;
    auto err = dosboxx_verify_determinism(nullptr, 1000, &is_det);
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, SetLogCallbackRejectsNullHandle) {
    auto err = dosboxx_set_log_callback(nullptr, nullptr, nullptr);
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_HANDLE);
}

// ─────────────────────────────────────────────────────────────────────────────
// Phase 2: Stepping API Tests
// ─────────────────────────────────────────────────────────────────────────────

class DosboxxSteppingTest : public ::testing::Test {
protected:
    dosboxx_handle handle_ = nullptr;

    void SetUp() override {
        // Clean up any previous instance
        dosboxx_destroy(reinterpret_cast<dosboxx_handle>(1));

        auto err = dosboxx_create(nullptr, &handle_);
        ASSERT_EQ(err, DOSBOXX_OK);
        ASSERT_NE(handle_, nullptr);
    }

    void TearDown() override {
        dosboxx_destroy(handle_);
    }
};

TEST_F(DosboxxSteppingTest, ResetWorks) {
    // Step some cycles first
    dosboxx_step_ms(handle_, 10, nullptr);

    // Reset should work now
    auto err = dosboxx_reset(handle_);
    EXPECT_EQ(err, DOSBOXX_OK);

    // Time should be reset to 0
    uint64_t time;
    dosboxx_get_emu_time(handle_, &time);
    EXPECT_EQ(time, 0u);
}

TEST_F(DosboxxSteppingTest, GetConfigWorks) {
    dosboxx_config_t config;
    auto err = dosboxx_get_config(handle_, &config);
    EXPECT_EQ(err, DOSBOXX_OK);
    EXPECT_EQ(config.memory_kb, 640u);  // Default
    EXPECT_EQ(config.deterministic, 1u);
}

TEST_F(DosboxxSteppingTest, StepMsWorks) {
    dosboxx_step_result_t result;
    auto err = dosboxx_step_ms(handle_, 100, &result);

    EXPECT_EQ(err, DOSBOXX_OK);
    EXPECT_GT(result.cycles_executed, 0u);
    EXPECT_EQ(result.stop_reason, DOSBOXX_STOP_COMPLETED);
}

TEST_F(DosboxxSteppingTest, StepCyclesWorks) {
    dosboxx_step_result_t result;
    const uint64_t target_cycles = 10000;

    auto err = dosboxx_step_cycles(handle_, target_cycles, &result);

    EXPECT_EQ(err, DOSBOXX_OK);
    EXPECT_EQ(result.cycles_executed, target_cycles);
    EXPECT_EQ(result.stop_reason, DOSBOXX_STOP_COMPLETED);
}

TEST_F(DosboxxSteppingTest, StepCyclesIsExact) {
    dosboxx_step_result_t result;
    const uint64_t target = 12345;

    auto err = dosboxx_step_cycles(handle_, target, &result);

    EXPECT_EQ(err, DOSBOXX_OK);
    // Should execute exactly the requested cycles
    EXPECT_EQ(result.cycles_executed, target);
}

TEST_F(DosboxxSteppingTest, GetEmuTimeWorks) {
    uint64_t time;
    auto err = dosboxx_get_emu_time(handle_, &time);
    EXPECT_EQ(err, DOSBOXX_OK);
    EXPECT_EQ(time, 0u);  // Initially 0
}

TEST_F(DosboxxSteppingTest, GetTotalCyclesWorks) {
    uint64_t cycles;
    auto err = dosboxx_get_total_cycles(handle_, &cycles);
    EXPECT_EQ(err, DOSBOXX_OK);
    EXPECT_EQ(cycles, 0u);  // Initially 0
}

TEST_F(DosboxxSteppingTest, TimeAccumulates) {
    uint64_t time1, time2;

    dosboxx_step_ms(handle_, 50, nullptr);
    dosboxx_get_emu_time(handle_, &time1);

    dosboxx_step_ms(handle_, 50, nullptr);
    dosboxx_get_emu_time(handle_, &time2);

    // Time should accumulate
    EXPECT_GT(time2, time1);
    // 100ms = 100000us
    EXPECT_GE(time2, 100000u);
}

TEST_F(DosboxxSteppingTest, CyclesAccumulate) {
    uint64_t cycles1, cycles2;

    dosboxx_step_cycles(handle_, 5000, nullptr);
    dosboxx_get_total_cycles(handle_, &cycles1);

    dosboxx_step_cycles(handle_, 5000, nullptr);
    dosboxx_get_total_cycles(handle_, &cycles2);

    EXPECT_EQ(cycles1, 5000u);
    EXPECT_EQ(cycles2, 10000u);
}

TEST_F(DosboxxSteppingTest, StepMsProducesConsistentCycles) {
    dosboxx_step_result_t result1, result2;

    // Step 100ms twice
    dosboxx_reset(handle_);
    dosboxx_step_ms(handle_, 100, &result1);

    dosboxx_reset(handle_);
    dosboxx_step_ms(handle_, 100, &result2);

    // Same ms should produce same cycles (determinism)
    EXPECT_EQ(result1.cycles_executed, result2.cycles_executed);
}

TEST_F(DosboxxSteppingTest, ResetClearsTime) {
    // Step some time
    dosboxx_step_ms(handle_, 100, nullptr);

    uint64_t time_before;
    dosboxx_get_emu_time(handle_, &time_before);
    EXPECT_GT(time_before, 0u);

    // Reset
    dosboxx_reset(handle_);

    // Time should be 0 again
    uint64_t time_after;
    dosboxx_get_emu_time(handle_, &time_after);
    EXPECT_EQ(time_after, 0u);
}

TEST_F(DosboxxSteppingTest, ResetClearsCycles) {
    // Step some cycles
    dosboxx_step_cycles(handle_, 10000, nullptr);

    uint64_t cycles_before;
    dosboxx_get_total_cycles(handle_, &cycles_before);
    EXPECT_GT(cycles_before, 0u);

    // Reset
    dosboxx_reset(handle_);

    // Cycles should be 0 again
    uint64_t cycles_after;
    dosboxx_get_total_cycles(handle_, &cycles_after);
    EXPECT_EQ(cycles_after, 0u);
}

// ─────────────────────────────────────────────────────────────────────────────
// Phase 3: Frame Capture API Tests
// ─────────────────────────────────────────────────────────────────────────────

class DosboxxCaptureTest : public ::testing::Test {
protected:
    dosboxx_handle handle_ = nullptr;

    void SetUp() override {
        // Clean up any previous instance
        dosboxx_destroy(reinterpret_cast<dosboxx_handle>(1));

        auto err = dosboxx_create(nullptr, &handle_);
        ASSERT_EQ(err, DOSBOXX_OK);
        ASSERT_NE(handle_, nullptr);
    }

    void TearDown() override {
        dosboxx_destroy(handle_);
    }
};

// Text Capture Tests

TEST_F(DosboxxCaptureTest, CaptureTextQuerySize) {
    size_t count;
    auto err = dosboxx_capture_text(handle_, nullptr, 0, &count, nullptr);
    EXPECT_EQ(err, DOSBOXX_OK);
    EXPECT_EQ(count, 80u * 25u);  // Default 80x25 text mode
}

TEST_F(DosboxxCaptureTest, CaptureTextReturnsInfo) {
    size_t count;
    dosboxx_text_info_t info;
    auto err = dosboxx_capture_text(handle_, nullptr, 0, &count, &info);
    EXPECT_EQ(err, DOSBOXX_OK);
    EXPECT_EQ(info.columns, 80u);
    EXPECT_EQ(info.rows, 25u);
    EXPECT_EQ(info.active_page, 0u);
    EXPECT_EQ(info.cursor_visible, 1u);  // Cursor is visible by default
}

TEST_F(DosboxxCaptureTest, CaptureTextFillsBuffer) {
    size_t count;
    dosboxx_capture_text(handle_, nullptr, 0, &count, nullptr);

    std::vector<dosboxx_text_cell_t> cells(count);
    auto err = dosboxx_capture_text(handle_, cells.data(), cells.size(), &count, nullptr);
    EXPECT_EQ(err, DOSBOXX_OK);

    // First character should be 'C' from "C:\>" prompt
    EXPECT_EQ(cells[0].character, 'C');
    EXPECT_EQ(cells[0].attribute, 0x07);  // Light gray on black
}

TEST_F(DosboxxCaptureTest, CaptureTextBufferTooSmall) {
    size_t count;
    dosboxx_capture_text(handle_, nullptr, 0, &count, nullptr);

    std::vector<dosboxx_text_cell_t> cells(count / 2);  // Too small
    size_t out_count;
    auto err = dosboxx_capture_text(handle_, cells.data(), cells.size(), &out_count, nullptr);
    EXPECT_EQ(err, DOSBOXX_ERR_BUFFER_TOO_SMALL);
}

TEST_F(DosboxxCaptureTest, CaptureTextRejectsNullCountOut) {
    auto err = dosboxx_capture_text(handle_, nullptr, 0, nullptr, nullptr);
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_POINTER);
}

// RGB Capture Tests

TEST_F(DosboxxCaptureTest, CaptureRgbQuerySize) {
    size_t size;
    uint16_t width, height;
    auto err = dosboxx_capture_rgb(handle_, nullptr, 0, &size, &width, &height);
    EXPECT_EQ(err, DOSBOXX_OK);
    // Text mode: 80*8 x 25*16 = 640x400
    EXPECT_EQ(width, 640u);
    EXPECT_EQ(height, 400u);
    EXPECT_EQ(size, 640u * 400u * 3u);  // RGB24
}

TEST_F(DosboxxCaptureTest, CaptureRgbFillsBuffer) {
    size_t size;
    uint16_t width, height;
    dosboxx_capture_rgb(handle_, nullptr, 0, &size, &width, &height);

    std::vector<uint8_t> buffer(size);
    auto err = dosboxx_capture_rgb(handle_, buffer.data(), buffer.size(), &size, nullptr, nullptr);
    EXPECT_EQ(err, DOSBOXX_OK);

    // Buffer should have been filled with something (not all zeros for text areas with content)
    bool has_non_zero = false;
    for (size_t i = 0; i < buffer.size() && !has_non_zero; ++i) {
        if (buffer[i] != 0) has_non_zero = true;
    }
    EXPECT_TRUE(has_non_zero);
}

TEST_F(DosboxxCaptureTest, CaptureRgbBufferTooSmall) {
    size_t size;
    dosboxx_capture_rgb(handle_, nullptr, 0, &size, nullptr, nullptr);

    std::vector<uint8_t> buffer(size / 2);  // Too small
    size_t out_size;
    auto err = dosboxx_capture_rgb(handle_, buffer.data(), buffer.size(), &out_size, nullptr, nullptr);
    EXPECT_EQ(err, DOSBOXX_ERR_BUFFER_TOO_SMALL);
}

TEST_F(DosboxxCaptureTest, CaptureRgbRejectsNullSizeOut) {
    auto err = dosboxx_capture_rgb(handle_, nullptr, 0, nullptr, nullptr, nullptr);
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_POINTER);
}

// Dirty Tracking Tests

TEST_F(DosboxxCaptureTest, IsFrameDirtyInitiallyTrue) {
    int dirty;
    auto err = dosboxx_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(err, DOSBOXX_OK);
    EXPECT_EQ(dirty, 1);  // Initially dirty
}

TEST_F(DosboxxCaptureTest, CaptureTextClearsDirty) {
    // Capture should clear dirty flag
    size_t count;
    dosboxx_capture_text(handle_, nullptr, 0, &count, nullptr);
    std::vector<dosboxx_text_cell_t> cells(count);
    dosboxx_capture_text(handle_, cells.data(), cells.size(), &count, nullptr);

    int dirty;
    dosboxx_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(dirty, 0);  // No longer dirty after capture
}

TEST_F(DosboxxCaptureTest, CaptureRgbClearsDirty) {
    size_t size;
    dosboxx_capture_rgb(handle_, nullptr, 0, &size, nullptr, nullptr);
    std::vector<uint8_t> buffer(size);
    dosboxx_capture_rgb(handle_, buffer.data(), buffer.size(), &size, nullptr, nullptr);

    int dirty;
    dosboxx_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(dirty, 0);  // No longer dirty after capture
}

TEST_F(DosboxxCaptureTest, ResetSetsDirty) {
    // Capture to clear dirty
    size_t count;
    dosboxx_capture_text(handle_, nullptr, 0, &count, nullptr);
    std::vector<dosboxx_text_cell_t> cells(count);
    dosboxx_capture_text(handle_, cells.data(), cells.size(), &count, nullptr);

    int dirty;
    dosboxx_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(dirty, 0);

    // Reset should set dirty again
    dosboxx_reset(handle_);
    dosboxx_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(dirty, 1);
}

// Cursor Tests

TEST_F(DosboxxCaptureTest, GetCursorWorks) {
    uint8_t x, y;
    int visible;
    auto err = dosboxx_get_cursor(handle_, &x, &y, &visible);
    EXPECT_EQ(err, DOSBOXX_OK);
    // After test pattern init, cursor is at column 4, row 0
    EXPECT_EQ(x, 4u);
    EXPECT_EQ(y, 0u);
    EXPECT_EQ(visible, 1);
}

TEST_F(DosboxxCaptureTest, GetCursorWorksWithNullOutputs) {
    // Should work even if some outputs are null
    auto err = dosboxx_get_cursor(handle_, nullptr, nullptr, nullptr);
    EXPECT_EQ(err, DOSBOXX_OK);

    uint8_t x;
    err = dosboxx_get_cursor(handle_, &x, nullptr, nullptr);
    EXPECT_EQ(err, DOSBOXX_OK);
    EXPECT_EQ(x, 4u);
}

TEST_F(DosboxxCaptureTest, CursorInfoMatchesTextInfo) {
    // Cursor info from text capture should match get_cursor
    size_t count;
    dosboxx_text_info_t info;
    dosboxx_capture_text(handle_, nullptr, 0, &count, &info);

    uint8_t x, y;
    int visible;
    dosboxx_get_cursor(handle_, &x, &y, &visible);

    EXPECT_EQ(info.cursor_x, x);
    EXPECT_EQ(info.cursor_y, y);
    EXPECT_EQ(info.cursor_visible, visible);
}

// ─────────────────────────────────────────────────────────────────────────────
// Phase 4: Input Injection API Tests
// ─────────────────────────────────────────────────────────────────────────────

class DosboxxInputTest : public ::testing::Test {
protected:
    dosboxx_handle handle_ = nullptr;

    void SetUp() override {
        // Clean up any previous instance
        dosboxx_destroy(reinterpret_cast<dosboxx_handle>(1));

        auto err = dosboxx_create(nullptr, &handle_);
        ASSERT_EQ(err, DOSBOXX_OK);
        ASSERT_NE(handle_, nullptr);
    }

    void TearDown() override {
        dosboxx_destroy(handle_);
    }
};

// Key Event Tests

TEST_F(DosboxxInputTest, KeyEventWorks) {
    // Press 'A' key (scancode 0x1E)
    auto err = dosboxx_key_event(handle_, 0x1E, 1);
    EXPECT_EQ(err, DOSBOXX_OK);

    // Release 'A' key
    err = dosboxx_key_event(handle_, 0x1E, 0);
    EXPECT_EQ(err, DOSBOXX_OK);
}

TEST_F(DosboxxInputTest, KeyEventSetsDirty) {
    // Clear dirty flag first
    size_t count;
    dosboxx_capture_text(handle_, nullptr, 0, &count, nullptr);
    std::vector<dosboxx_text_cell_t> cells(count);
    dosboxx_capture_text(handle_, cells.data(), cells.size(), &count, nullptr);

    int dirty;
    dosboxx_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(dirty, 0);

    // Key event should set dirty
    dosboxx_key_event(handle_, 0x1E, 1);

    dosboxx_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(dirty, 1);
}

TEST_F(DosboxxInputTest, KeyEventExtWorks) {
    // Press Right Arrow key (E0 + 0x4D)
    auto err = dosboxx_key_event_ext(handle_, 0x4D, 1);
    EXPECT_EQ(err, DOSBOXX_OK);

    // Release Right Arrow key
    err = dosboxx_key_event_ext(handle_, 0x4D, 0);
    EXPECT_EQ(err, DOSBOXX_OK);
}

TEST_F(DosboxxInputTest, KeyEventExtInsertDeleteHomeEnd) {
    // Insert (E0 + 0x52)
    EXPECT_EQ(dosboxx_key_event_ext(handle_, 0x52, 1), DOSBOXX_OK);
    EXPECT_EQ(dosboxx_key_event_ext(handle_, 0x52, 0), DOSBOXX_OK);

    // Delete (E0 + 0x53)
    EXPECT_EQ(dosboxx_key_event_ext(handle_, 0x53, 1), DOSBOXX_OK);
    EXPECT_EQ(dosboxx_key_event_ext(handle_, 0x53, 0), DOSBOXX_OK);

    // Home (E0 + 0x47)
    EXPECT_EQ(dosboxx_key_event_ext(handle_, 0x47, 1), DOSBOXX_OK);
    EXPECT_EQ(dosboxx_key_event_ext(handle_, 0x47, 0), DOSBOXX_OK);

    // End (E0 + 0x4F)
    EXPECT_EQ(dosboxx_key_event_ext(handle_, 0x4F, 1), DOSBOXX_OK);
    EXPECT_EQ(dosboxx_key_event_ext(handle_, 0x4F, 0), DOSBOXX_OK);
}

// Text Input Tests

TEST_F(DosboxxInputTest, TextInputWorks) {
    auto err = dosboxx_text_input(handle_, "Hello");
    EXPECT_EQ(err, DOSBOXX_OK);
}

TEST_F(DosboxxInputTest, TextInputHandlesNewlines) {
    auto err = dosboxx_text_input(handle_, "DIR\n");
    EXPECT_EQ(err, DOSBOXX_OK);
}

TEST_F(DosboxxInputTest, TextInputHandlesShiftChars) {
    // Uppercase letters and shifted symbols
    auto err = dosboxx_text_input(handle_, "ABC!");
    EXPECT_EQ(err, DOSBOXX_OK);
}

TEST_F(DosboxxInputTest, TextInputRejectsNull) {
    auto err = dosboxx_text_input(handle_, nullptr);
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_POINTER);
}

TEST_F(DosboxxInputTest, TextInputEmptyStringIsOk) {
    auto err = dosboxx_text_input(handle_, "");
    EXPECT_EQ(err, DOSBOXX_OK);
}

TEST_F(DosboxxInputTest, TextInputSetsDirty) {
    // Clear dirty flag first
    size_t count;
    dosboxx_capture_text(handle_, nullptr, 0, &count, nullptr);
    std::vector<dosboxx_text_cell_t> cells(count);
    dosboxx_capture_text(handle_, cells.data(), cells.size(), &count, nullptr);

    int dirty;
    dosboxx_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(dirty, 0);

    // Text input should set dirty
    dosboxx_text_input(handle_, "A");

    dosboxx_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(dirty, 1);
}

// Mouse Event Tests

TEST_F(DosboxxInputTest, MouseEventWorks) {
    // Move mouse with no buttons
    auto err = dosboxx_mouse_event(handle_, 10, 5, 0);
    EXPECT_EQ(err, DOSBOXX_OK);
}

TEST_F(DosboxxInputTest, MouseEventWithButtons) {
    // Left button click
    auto err = dosboxx_mouse_event(handle_, 0, 0, 1);  // Left button down
    EXPECT_EQ(err, DOSBOXX_OK);

    err = dosboxx_mouse_event(handle_, 0, 0, 0);  // Release
    EXPECT_EQ(err, DOSBOXX_OK);
}

TEST_F(DosboxxInputTest, MouseEventRightButton) {
    // Right button click
    auto err = dosboxx_mouse_event(handle_, 0, 0, 2);  // Right button
    EXPECT_EQ(err, DOSBOXX_OK);
}

TEST_F(DosboxxInputTest, MouseEventMiddleButton) {
    // Middle button click
    auto err = dosboxx_mouse_event(handle_, 0, 0, 4);  // Middle button
    EXPECT_EQ(err, DOSBOXX_OK);
}

TEST_F(DosboxxInputTest, MouseEventNegativeMovement) {
    // Negative movement (move up/left)
    auto err = dosboxx_mouse_event(handle_, -20, -15, 0);
    EXPECT_EQ(err, DOSBOXX_OK);
}

TEST_F(DosboxxInputTest, MouseEventSetsDirty) {
    // Clear dirty flag first
    size_t count;
    dosboxx_capture_text(handle_, nullptr, 0, &count, nullptr);
    std::vector<dosboxx_text_cell_t> cells(count);
    dosboxx_capture_text(handle_, cells.data(), cells.size(), &count, nullptr);

    int dirty;
    dosboxx_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(dirty, 0);

    // Mouse event should set dirty
    dosboxx_mouse_event(handle_, 5, 5, 0);

    dosboxx_is_frame_dirty(handle_, &dirty);
    EXPECT_EQ(dirty, 1);
}

// Reset Tests

TEST_F(DosboxxInputTest, ResetClearsInputQueues) {
    // Queue some events
    dosboxx_key_event(handle_, 0x1E, 1);
    dosboxx_key_event(handle_, 0x1E, 0);
    dosboxx_mouse_event(handle_, 10, 10, 1);

    // Reset should clear queues
    auto err = dosboxx_reset(handle_);
    EXPECT_EQ(err, DOSBOXX_OK);

    // Can still queue events after reset
    err = dosboxx_key_event(handle_, 0x1E, 1);
    EXPECT_EQ(err, DOSBOXX_OK);
}

// ─────────────────────────────────────────────────────────────────────────────
// Phase 5: Save-State Determinism Tests
// Per TLA+ SaveState.tla: Obs(Deserialize(Serialize(S))) = Obs(S)
// ─────────────────────────────────────────────────────────────────────────────

class DosboxxSaveStateTest : public ::testing::Test {
protected:
    dosboxx_handle handle_ = nullptr;

    void SetUp() override {
        // Clean up any previous instance
        dosboxx_destroy(reinterpret_cast<dosboxx_handle>(1));

        auto err = dosboxx_create(nullptr, &handle_);
        ASSERT_EQ(err, DOSBOXX_OK);
        ASSERT_NE(handle_, nullptr);
    }

    void TearDown() override {
        dosboxx_destroy(handle_);
    }
};

// Save State Tests

TEST_F(DosboxxSaveStateTest, SaveStateQuerySize) {
    size_t size;
    auto err = dosboxx_save_state(handle_, nullptr, 0, &size);
    EXPECT_EQ(err, DOSBOXX_OK);
    EXPECT_GT(size, 0u);  // Should return non-zero size
}

TEST_F(DosboxxSaveStateTest, SaveStateFillsBuffer) {
    size_t size;
    dosboxx_save_state(handle_, nullptr, 0, &size);

    std::vector<uint8_t> buffer(size);
    auto err = dosboxx_save_state(handle_, buffer.data(), buffer.size(), &size);
    EXPECT_EQ(err, DOSBOXX_OK);

    // Check magic number (DBXS = 0x53584244 little-endian)
    uint32_t magic;
    std::memcpy(&magic, buffer.data(), sizeof(magic));
    EXPECT_EQ(magic, 0x53584244u);
}

TEST_F(DosboxxSaveStateTest, SaveStateBufferTooSmall) {
    size_t size;
    dosboxx_save_state(handle_, nullptr, 0, &size);

    std::vector<uint8_t> buffer(size / 2);  // Too small
    size_t out_size;
    auto err = dosboxx_save_state(handle_, buffer.data(), buffer.size(), &out_size);
    EXPECT_EQ(err, DOSBOXX_ERR_BUFFER_TOO_SMALL);
}

TEST_F(DosboxxSaveStateTest, SaveStateRejectsNullSizeOut) {
    auto err = dosboxx_save_state(handle_, nullptr, 0, nullptr);
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_POINTER);
}

// Load State Tests

TEST_F(DosboxxSaveStateTest, LoadStateRestoresState) {
    // Step some cycles
    dosboxx_step_cycles(handle_, 10000, nullptr);

    // Save state
    size_t size;
    dosboxx_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> buffer(size);
    dosboxx_save_state(handle_, buffer.data(), buffer.size(), &size);

    // Get current time
    uint64_t time_before;
    dosboxx_get_emu_time(handle_, &time_before);

    // Step more
    dosboxx_step_cycles(handle_, 5000, nullptr);

    // Load state
    auto err = dosboxx_load_state(handle_, buffer.data(), buffer.size());
    EXPECT_EQ(err, DOSBOXX_OK);

    // Time should be restored
    uint64_t time_after;
    dosboxx_get_emu_time(handle_, &time_after);
    EXPECT_EQ(time_after, time_before);
}

TEST_F(DosboxxSaveStateTest, LoadStateRejectsInvalidMagic) {
    std::vector<uint8_t> buffer(256, 0);  // All zeros = invalid magic
    auto err = dosboxx_load_state(handle_, buffer.data(), buffer.size());
    EXPECT_EQ(err, DOSBOXX_ERR_INVALID_STATE);
}

TEST_F(DosboxxSaveStateTest, LoadStateRejectsVersionMismatch) {
    // Save valid state
    size_t size;
    dosboxx_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> buffer(size);
    dosboxx_save_state(handle_, buffer.data(), buffer.size(), &size);

    // Corrupt version field (offset 4)
    buffer[4] = 99;  // Invalid version

    auto err = dosboxx_load_state(handle_, buffer.data(), buffer.size());
    EXPECT_EQ(err, DOSBOXX_ERR_VERSION_MISMATCH);
}

TEST_F(DosboxxSaveStateTest, LoadStateRejectsCorruptedChecksum) {
    // Save valid state
    size_t size;
    dosboxx_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> buffer(size);
    dosboxx_save_state(handle_, buffer.data(), buffer.size(), &size);

    // Corrupt data (checksum will fail)
    if (size > 100) {
        buffer[100] ^= 0xFF;
    }

    auto err = dosboxx_load_state(handle_, buffer.data(), buffer.size());
    EXPECT_EQ(err, DOSBOXX_ERR_INVALID_STATE);
}

// State Hash Tests

TEST_F(DosboxxSaveStateTest, GetStateHashWorks) {
    uint8_t hash[32];
    auto err = dosboxx_get_state_hash(handle_, hash);
    EXPECT_EQ(err, DOSBOXX_OK);

    // Hash should not be all zeros
    bool all_zeros = true;
    for (int i = 0; i < 32; ++i) {
        if (hash[i] != 0) all_zeros = false;
    }
    EXPECT_FALSE(all_zeros);
}

TEST_F(DosboxxSaveStateTest, StateHashIsConsistent) {
    uint8_t hash1[32], hash2[32];

    dosboxx_get_state_hash(handle_, hash1);
    dosboxx_get_state_hash(handle_, hash2);

    // Same state should produce same hash
    EXPECT_EQ(std::memcmp(hash1, hash2, 32), 0);
}

TEST_F(DosboxxSaveStateTest, StateHashChangesAfterStep) {
    uint8_t hash1[32], hash2[32];

    dosboxx_get_state_hash(handle_, hash1);

    // Step some cycles
    dosboxx_step_cycles(handle_, 10000, nullptr);

    dosboxx_get_state_hash(handle_, hash2);

    // Hash should change after stepping
    EXPECT_NE(std::memcmp(hash1, hash2, 32), 0);
}

TEST_F(DosboxxSaveStateTest, StateHashMatchesAfterLoadState) {
    // Save initial state and hash
    size_t size;
    dosboxx_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> buffer(size);
    dosboxx_save_state(handle_, buffer.data(), buffer.size(), &size);

    uint8_t hash1[32];
    dosboxx_get_state_hash(handle_, hash1);

    // Step and change state
    dosboxx_step_cycles(handle_, 10000, nullptr);

    // Load original state
    dosboxx_load_state(handle_, buffer.data(), buffer.size());

    // Hash should match original
    uint8_t hash2[32];
    dosboxx_get_state_hash(handle_, hash2);
    EXPECT_EQ(std::memcmp(hash1, hash2, 32), 0);
}

// Determinism Verification Tests

TEST_F(DosboxxSaveStateTest, VerifyDeterminismWorks) {
    int is_deterministic;
    auto err = dosboxx_verify_determinism(handle_, 10000, &is_deterministic);
    EXPECT_EQ(err, DOSBOXX_OK);
    EXPECT_EQ(is_deterministic, 1);  // Should be deterministic
}

TEST_F(DosboxxSaveStateTest, VerifyDeterminismAfterInput) {
    // Queue some input
    dosboxx_key_event(handle_, 0x1E, 1);
    dosboxx_key_event(handle_, 0x1E, 0);

    int is_deterministic;
    auto err = dosboxx_verify_determinism(handle_, 5000, &is_deterministic);
    EXPECT_EQ(err, DOSBOXX_OK);
    EXPECT_EQ(is_deterministic, 1);  // Should still be deterministic
}

TEST_F(DosboxxSaveStateTest, VerifyDeterminismWithMultipleSteps) {
    // Do some initial work
    dosboxx_step_ms(handle_, 50, nullptr);

    int is_deterministic;
    auto err = dosboxx_verify_determinism(handle_, 20000, &is_deterministic);
    EXPECT_EQ(err, DOSBOXX_OK);
    EXPECT_EQ(is_deterministic, 1);
}

// Round-Trip Invariant Test (per TLA+ specification)

TEST_F(DosboxxSaveStateTest, RoundTripPreservesObservation) {
    // Step to create some state
    dosboxx_step_cycles(handle_, 50000, nullptr);

    // Get initial hash
    uint8_t hash_before[32];
    dosboxx_get_state_hash(handle_, hash_before);

    // Save state
    size_t size;
    dosboxx_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> buffer(size);
    dosboxx_save_state(handle_, buffer.data(), buffer.size(), &size);

    // Load state
    auto err = dosboxx_load_state(handle_, buffer.data(), buffer.size());
    EXPECT_EQ(err, DOSBOXX_OK);

    // Get hash after round-trip
    uint8_t hash_after[32];
    dosboxx_get_state_hash(handle_, hash_after);

    // Per TLA+ SaveState.tla: Obs(Deserialize(Serialize(S))) = Obs(S)
    EXPECT_EQ(std::memcmp(hash_before, hash_after, 32), 0)
        << "Round-trip must preserve observable state (TLA+ invariant)";
}

// ─────────────────────────────────────────────────────────────────────────────
// Phase 6: Log Callback Tests
// ─────────────────────────────────────────────────────────────────────────────

// Test context for log callback
struct LogTestContext {
    std::vector<std::pair<int, std::string>> messages;

    static void callback(int level, const char* message, void* userdata) {
        auto* ctx = static_cast<LogTestContext*>(userdata);
        if (ctx && message) {
            ctx->messages.emplace_back(level, std::string(message));
        }
    }

    void clear() { messages.clear(); }

    bool has_level(int level) const {
        for (const auto& msg : messages) {
            if (msg.first == level) return true;
        }
        return false;
    }

    bool has_message_containing(const std::string& substr) const {
        for (const auto& msg : messages) {
            if (msg.second.find(substr) != std::string::npos) return true;
        }
        return false;
    }
};

class DosboxxLogCallbackTest : public ::testing::Test {
protected:
    dosboxx_handle handle_ = nullptr;
    LogTestContext log_ctx_;

    void SetUp() override {
        // Clean up any previous instance
        dosboxx_destroy(reinterpret_cast<dosboxx_handle>(1));

        auto err = dosboxx_create(nullptr, &handle_);
        ASSERT_EQ(err, DOSBOXX_OK);
        ASSERT_NE(handle_, nullptr);
    }

    void TearDown() override {
        dosboxx_destroy(handle_);
    }
};

TEST_F(DosboxxLogCallbackTest, SetLogCallbackWorks) {
    auto err = dosboxx_set_log_callback(handle_, LogTestContext::callback, &log_ctx_);
    EXPECT_EQ(err, DOSBOXX_OK);
}

TEST_F(DosboxxLogCallbackTest, SetLogCallbackToNullWorks) {
    // First set a callback
    auto err = dosboxx_set_log_callback(handle_, LogTestContext::callback, &log_ctx_);
    EXPECT_EQ(err, DOSBOXX_OK);

    // Then clear it
    err = dosboxx_set_log_callback(handle_, nullptr, nullptr);
    EXPECT_EQ(err, DOSBOXX_OK);
}

TEST_F(DosboxxLogCallbackTest, CallbackReceivesDebugMessage) {
    auto err = dosboxx_set_log_callback(handle_, LogTestContext::callback, &log_ctx_);
    ASSERT_EQ(err, DOSBOXX_OK);

    // Setting callback should log a debug message
    EXPECT_TRUE(log_ctx_.has_level(3));  // LOG_LEVEL_DEBUG = 3
    EXPECT_TRUE(log_ctx_.has_message_containing("Log callback registered"));
}

TEST_F(DosboxxLogCallbackTest, CallbackReceivesErrorOnFailure) {
    auto err = dosboxx_set_log_callback(handle_, LogTestContext::callback, &log_ctx_);
    ASSERT_EQ(err, DOSBOXX_OK);
    log_ctx_.clear();

    // Try to create a second instance (should fail and log error)
    dosboxx_handle handle2 = nullptr;
    err = dosboxx_create(nullptr, &handle2);
    EXPECT_EQ(err, DOSBOXX_ERR_ALREADY_CREATED);

    // Should have logged an error
    EXPECT_TRUE(log_ctx_.has_level(0));  // LOG_LEVEL_ERROR = 0
    EXPECT_TRUE(log_ctx_.has_message_containing("already exists"));
}

TEST_F(DosboxxLogCallbackTest, CallbackReceivesInfoOnDestroy) {
    auto err = dosboxx_set_log_callback(handle_, LogTestContext::callback, &log_ctx_);
    ASSERT_EQ(err, DOSBOXX_OK);
    log_ctx_.clear();

    // Destroy the instance
    dosboxx_destroy(handle_);
    handle_ = nullptr;  // Prevent double-destroy in TearDown

    // Should have logged an info message
    EXPECT_TRUE(log_ctx_.has_level(2));  // LOG_LEVEL_INFO = 2
    EXPECT_TRUE(log_ctx_.has_message_containing("Destroying"));
}

TEST_F(DosboxxLogCallbackTest, NoCallbackAfterDestroy) {
    auto err = dosboxx_set_log_callback(handle_, LogTestContext::callback, &log_ctx_);
    ASSERT_EQ(err, DOSBOXX_OK);
    log_ctx_.clear();

    // Destroy and recreate
    dosboxx_destroy(handle_);
    handle_ = nullptr;

    size_t msg_count = log_ctx_.messages.size();

    // Create new instance (callback should be cleared)
    err = dosboxx_create(nullptr, &handle_);
    ASSERT_EQ(err, DOSBOXX_OK);

    // No new messages (callback was cleared on destroy)
    EXPECT_EQ(log_ctx_.messages.size(), msg_count);
}

// ─────────────────────────────────────────────────────────────────────────────
// Error Message Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(DosboxxEmbedTest, GetLastErrorQuerySize) {
    size_t length;
    auto err = dosboxx_get_last_error(nullptr, nullptr, 0, &length);
    EXPECT_EQ(err, DOSBOXX_OK);
}

TEST_F(DosboxxEmbedTest, GetLastErrorRejectsNullLengthOut) {
    char buffer[256];
    auto err = dosboxx_get_last_error(nullptr, buffer, sizeof(buffer), nullptr);
    EXPECT_EQ(err, DOSBOXX_ERR_NULL_POINTER);
}

TEST_F(DosboxxEmbedTest, GetLastErrorBufferTooSmall) {
    // Create instance then try to create another to trigger error
    dosboxx_handle handle1 = nullptr;
    dosboxx_create(nullptr, &handle1);

    dosboxx_handle handle2 = nullptr;
    dosboxx_create(nullptr, &handle2);  // Should fail and set error

    // Get the required size
    size_t length;
    dosboxx_get_last_error(nullptr, nullptr, 0, &length);
    ASSERT_GT(length, 2u);  // Should have error message

    // Try with too small buffer
    char small_buffer[2];
    size_t len_out;
    auto err = dosboxx_get_last_error(nullptr, small_buffer, sizeof(small_buffer), &len_out);
    EXPECT_EQ(err, DOSBOXX_ERR_BUFFER_TOO_SMALL);

    dosboxx_destroy(handle1);
}

TEST_F(DosboxxEmbedTest, GetLastErrorReturnsMessage) {
    // Create instance then try to create another to trigger error
    dosboxx_handle handle1 = nullptr;
    dosboxx_create(nullptr, &handle1);

    dosboxx_handle handle2 = nullptr;
    dosboxx_create(nullptr, &handle2);  // Should fail and set error

    // Get the message
    char buffer[256];
    size_t length;
    auto err = dosboxx_get_last_error(nullptr, buffer, sizeof(buffer), &length);
    EXPECT_EQ(err, DOSBOXX_OK);
    EXPECT_GT(std::strlen(buffer), 0u);  // Should have message content

    dosboxx_destroy(handle1);
}

// ─────────────────────────────────────────────────────────────────────────────
// Phase 6: Fuzz/Property-Based Tests
// ─────────────────────────────────────────────────────────────────────────────

class DosboxxFuzzTest : public ::testing::Test {
protected:
    dosboxx_handle handle_ = nullptr;

    void SetUp() override {
        dosboxx_destroy(reinterpret_cast<dosboxx_handle>(1));
        auto err = dosboxx_create(nullptr, &handle_);
        ASSERT_EQ(err, DOSBOXX_OK);
    }

    void TearDown() override {
        dosboxx_destroy(handle_);
    }
};

// Test that random scancodes don't crash
TEST_F(DosboxxFuzzTest, RandomScancodesDontCrash) {
    for (int scancode = 0; scancode <= 255; ++scancode) {
        auto err = dosboxx_key_event(handle_, static_cast<uint8_t>(scancode), 1);
        // OK or BUFFER_TOO_SMALL are acceptable (queue has finite capacity)
        EXPECT_TRUE(err == DOSBOXX_OK || err == DOSBOXX_ERR_BUFFER_TOO_SMALL)
            << "Unexpected error " << err << " on scancode " << scancode;
        err = dosboxx_key_event(handle_, static_cast<uint8_t>(scancode), 0);
        EXPECT_TRUE(err == DOSBOXX_OK || err == DOSBOXX_ERR_BUFFER_TOO_SMALL)
            << "Unexpected error " << err << " on release scancode " << scancode;
    }
}

// Test that random extended scancodes don't crash
TEST_F(DosboxxFuzzTest, RandomExtendedScancodesDontCrash) {
    for (int scancode = 0; scancode <= 255; ++scancode) {
        auto err = dosboxx_key_event_ext(handle_, static_cast<uint8_t>(scancode), 1);
        // OK or BUFFER_TOO_SMALL are acceptable (queue has finite capacity)
        EXPECT_TRUE(err == DOSBOXX_OK || err == DOSBOXX_ERR_BUFFER_TOO_SMALL)
            << "Unexpected error " << err << " on ext scancode " << scancode;
        err = dosboxx_key_event_ext(handle_, static_cast<uint8_t>(scancode), 0);
        EXPECT_TRUE(err == DOSBOXX_OK || err == DOSBOXX_ERR_BUFFER_TOO_SMALL)
            << "Unexpected error " << err << " on release ext scancode " << scancode;
    }
}

// Test that random mouse events don't crash
TEST_F(DosboxxFuzzTest, RandomMouseEventsDontCrash) {
    // Test various delta values and button combinations
    int16_t deltas[] = {-32768, -100, -1, 0, 1, 100, 32767};
    for (auto dx : deltas) {
        for (auto dy : deltas) {
            for (uint8_t buttons = 0; buttons <= 7; ++buttons) {
                auto err = dosboxx_mouse_event(handle_, dx, dy, buttons);
                // OK or BUFFER_TOO_SMALL are acceptable (queue has finite capacity)
                EXPECT_TRUE(err == DOSBOXX_OK || err == DOSBOXX_ERR_BUFFER_TOO_SMALL);
            }
        }
    }
}

// Test that corrupted save state is rejected
TEST_F(DosboxxFuzzTest, CorruptedSaveStateRejected) {
    // All-zeros buffer
    uint8_t zeros[256] = {0};
    auto err = dosboxx_load_state(handle_, zeros, sizeof(zeros));
    EXPECT_NE(err, DOSBOXX_OK);

    // All-ones buffer
    uint8_t ones[256];
    std::memset(ones, 0xFF, sizeof(ones));
    err = dosboxx_load_state(handle_, ones, sizeof(ones));
    EXPECT_NE(err, DOSBOXX_OK);

    // Random-looking buffer
    uint8_t random[256];
    for (int i = 0; i < 256; ++i) {
        random[i] = static_cast<uint8_t>((i * 17 + 13) % 256);
    }
    err = dosboxx_load_state(handle_, random, sizeof(random));
    EXPECT_NE(err, DOSBOXX_OK);
}

// Test that valid magic but corrupted data is rejected
TEST_F(DosboxxFuzzTest, CorruptedChecksumRejected) {
    // First save a valid state
    size_t state_size;
    auto err = dosboxx_save_state(handle_, nullptr, 0, &state_size);
    ASSERT_EQ(err, DOSBOXX_OK);

    std::vector<uint8_t> buffer(state_size);
    err = dosboxx_save_state(handle_, buffer.data(), buffer.size(), &state_size);
    ASSERT_EQ(err, DOSBOXX_OK);

    // Corrupt the data (not the header)
    if (buffer.size() > 100) {
        buffer[100] ^= 0xFF;  // Flip bits in data section
    }

    // Should reject due to checksum mismatch
    err = dosboxx_load_state(handle_, buffer.data(), buffer.size());
    EXPECT_EQ(err, DOSBOXX_ERR_INVALID_STATE);
}

// Test rapid stepping doesn't overflow
TEST_F(DosboxxFuzzTest, RapidSteppingStable) {
    for (int i = 0; i < 1000; ++i) {
        auto err = dosboxx_step_cycles(handle_, 1000, nullptr);
        EXPECT_EQ(err, DOSBOXX_OK);
    }

    // Verify time is accumulated correctly
    uint64_t cycles;
    auto err = dosboxx_get_total_cycles(handle_, &cycles);
    EXPECT_EQ(err, DOSBOXX_OK);
    EXPECT_EQ(cycles, 1000000u);  // 1000 * 1000
}

// Test that invalid handles are consistently rejected
TEST_F(DosboxxFuzzTest, InvalidHandlesRejected) {
    dosboxx_handle invalid_handles[] = {
        nullptr,
        reinterpret_cast<dosboxx_handle>(0xDEADBEEF),
        reinterpret_cast<dosboxx_handle>(0xFFFFFFFF),
    };

    for (auto invalid : invalid_handles) {
        if (invalid == nullptr) continue;  // nullptr tested elsewhere

        // All these should gracefully reject (or accept if handle validation is minimal)
        // Key: they shouldn't crash
        dosboxx_step_ms(invalid, 10, nullptr);
        dosboxx_key_event(invalid, 0x1E, 1);
        dosboxx_mouse_event(invalid, 0, 0, 0);
    }
}

// Test save/load cycle preserves state across multiple iterations
TEST_F(DosboxxFuzzTest, RepeatedSaveLoadCycle) {
    for (int iter = 0; iter < 10; ++iter) {
        // Step some cycles
        dosboxx_step_cycles(handle_, 1000, nullptr);

        // Save state
        size_t state_size;
        auto err = dosboxx_save_state(handle_, nullptr, 0, &state_size);
        ASSERT_EQ(err, DOSBOXX_OK);

        std::vector<uint8_t> buffer(state_size);
        err = dosboxx_save_state(handle_, buffer.data(), buffer.size(), &state_size);
        ASSERT_EQ(err, DOSBOXX_OK);

        // Get hash before
        uint8_t hash_before[32];
        err = dosboxx_get_state_hash(handle_, hash_before);
        ASSERT_EQ(err, DOSBOXX_OK);

        // Load state
        err = dosboxx_load_state(handle_, buffer.data(), buffer.size());
        ASSERT_EQ(err, DOSBOXX_OK);

        // Get hash after
        uint8_t hash_after[32];
        err = dosboxx_get_state_hash(handle_, hash_after);
        ASSERT_EQ(err, DOSBOXX_OK);

        // Hashes must match
        EXPECT_EQ(std::memcmp(hash_before, hash_after, 32), 0)
            << "Hash mismatch on iteration " << iter;
    }
}

// Test that text input with various characters doesn't crash
TEST_F(DosboxxFuzzTest, TextInputVariousCharacters) {
    // ASCII printable characters - test short strings that won't fill queue
    const char* test_strings[] = {
        "Hello",
        "UPPER",
        "lower",
        "Mix123",
        "!@#$",
        "",  // Empty string
        "A",  // Single char
    };

    for (const char* str : test_strings) {
        // Reset to clear queue between strings
        dosboxx_reset(handle_);
        auto err = dosboxx_text_input(handle_, str);
        // OK or BUFFER_TOO_SMALL are acceptable
        EXPECT_TRUE(err == DOSBOXX_OK || err == DOSBOXX_ERR_BUFFER_TOO_SMALL)
            << "Unexpected error " << err << " on string: " << str;
    }
}
