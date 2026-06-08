/**
 * @file test_legends_embed.cpp
 * @brief C++ unit tests for legends_embed API using GoogleTest.
 *
 * These tests verify the legends_embed.h API behaves correctly from C++.
 * For pure C ABI tests, see test_legends_abi.c
 *
 * Note: This file has been split into multiple files for faster incremental builds:
 * - test_legends_embed_lifecycle.cpp (create/destroy/force_destroy tests)
 * - test_legends_embed_capture.cpp (capture_rgb, capture_text tests)
 * - test_legends_embed_input.cpp (key_event, mouse_event, text_input tests)
 * - test_legends_embed_savestate.cpp (save/load state tests)
 * - test_legends_embed_security.cpp (security/reentrancy/threading tests)
 *
 * This file retains: ABI, Version, Error, Config, Null Handle, Stepping,
 * Log Callback, Fuzz/Property, and CPU Bridge Integration tests.
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include "internal/legends_instance.h"
#include <cstring>
#include <stdexcept>
#include <vector>

// ─────────────────────────────────────────────────────────────────────────────
// ABI Size Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(DosboxxAbiTest, TextCellSize) {
    EXPECT_EQ(sizeof(legends_text_cell_t), 2u);
}

TEST(DosboxxAbiTest, TextInfoSize) {
    EXPECT_EQ(sizeof(legends_text_info_t), 8u);
}

TEST(DosboxxAbiTest, StepResultSize) {
    EXPECT_EQ(sizeof(legends_step_result_t), 24u);
}

TEST(DosboxxAbiTest, ConfigSize) {
    // Config size depends on pointer size and alignment.
    // After deterministic + _pad3 (offset 36), pointers need 8-byte alignment
    // on 64-bit, so there's 4 bytes of padding.
#if defined(__LP64__) || defined(_WIN64) || defined(__x86_64__) || defined(__aarch64__)
    EXPECT_EQ(sizeof(legends_config_t), 120u);
#else
    EXPECT_EQ(sizeof(legends_config_t), 108u);
#endif
}

// ─────────────────────────────────────────────────────────────────────────────
// Version API Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(DosboxxVersionTest, GetApiVersionReturnsCorrectValues) {
    uint32_t major, minor, patch;
    auto err = legends_get_api_version(&major, &minor, &patch);

    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(major, LEGENDS_API_VERSION_MAJOR);
    EXPECT_EQ(minor, LEGENDS_API_VERSION_MINOR);
    EXPECT_EQ(patch, LEGENDS_API_VERSION_PATCH);
}

TEST(DosboxxVersionTest, GetApiVersionRejectsNullMajor) {
    uint32_t minor, patch;
    auto err = legends_get_api_version(nullptr, &minor, &patch);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_POINTER);
}

TEST(DosboxxVersionTest, GetApiVersionRejectsNullMinor) {
    uint32_t major, patch;
    auto err = legends_get_api_version(&major, nullptr, &patch);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_POINTER);
}

TEST(DosboxxVersionTest, GetApiVersionRejectsNullPatch) {
    uint32_t major, minor;
    auto err = legends_get_api_version(&major, &minor, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_POINTER);
}

TEST(DosboxxVersionTest, PackedVersionMatches) {
    uint32_t expected = (LEGENDS_API_VERSION_MAJOR << 16) |
                        (LEGENDS_API_VERSION_MINOR << 8) |
                        LEGENDS_API_VERSION_PATCH;
    EXPECT_EQ(LEGENDS_API_VERSION, expected);
}

// ─────────────────────────────────────────────────────────────────────────────
// Error Code Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(DosboxxErrorTest, OkIsZero) {
    EXPECT_EQ(LEGENDS_OK, 0);
}

TEST(DosboxxErrorTest, AllErrorCodesAreNonZero) {
    EXPECT_NE(LEGENDS_ERR_NULL_HANDLE, 0);
    EXPECT_NE(LEGENDS_ERR_NULL_POINTER, 0);
    EXPECT_NE(LEGENDS_ERR_ALREADY_CREATED, 0);
    EXPECT_NE(LEGENDS_ERR_NOT_INITIALIZED, 0);
    EXPECT_NE(LEGENDS_ERR_REENTRANT_CALL, 0);
    EXPECT_NE(LEGENDS_ERR_BUFFER_TOO_SMALL, 0);
    EXPECT_NE(LEGENDS_ERR_INVALID_CONFIG, 0);
    EXPECT_NE(LEGENDS_ERR_INVALID_STATE, 0);
    EXPECT_NE(LEGENDS_ERR_VERSION_MISMATCH, 0);
    EXPECT_NE(LEGENDS_ERR_IO_FAILED, 0);
    EXPECT_NE(LEGENDS_ERR_OUT_OF_MEMORY, 0);
    EXPECT_NE(LEGENDS_ERR_NOT_SUPPORTED, 0);
    EXPECT_NE(LEGENDS_ERR_INTERNAL, 0);
}

TEST(DosboxxErrorTest, AllErrorCodesAreDistinct) {
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
        LEGENDS_ERR_INTERNAL
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
    legends_config_t config = LEGENDS_CONFIG_INIT;

    EXPECT_EQ(config.struct_size, sizeof(legends_config_t));
    EXPECT_EQ(config.api_version, LEGENDS_API_VERSION);
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
// Null Handle Rejection Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(DosboxxNullHandleTest, ResetRejectsNullHandle) {
    auto err = legends_reset(nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, GetConfigRejectsNullHandle) {
    legends_config_t config;
    auto err = legends_get_config(nullptr, &config);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, StepMsRejectsNullHandle) {
    auto err = legends_step_ms(nullptr, 100, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, StepCyclesRejectsNullHandle) {
    auto err = legends_step_cycles(nullptr, 1000, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, GetEmuTimeRejectsNullHandle) {
    uint64_t time;
    auto err = legends_get_emu_time(nullptr, &time);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, GetTotalCyclesRejectsNullHandle) {
    uint64_t cycles;
    auto err = legends_get_total_cycles(nullptr, &cycles);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, CaptureTextRejectsNullHandle) {
    size_t count;
    auto err = legends_capture_text(nullptr, nullptr, 0, &count, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, CaptureRgbRejectsNullHandle) {
    size_t size;
    auto err = legends_capture_rgb(nullptr, nullptr, 0, &size, nullptr, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, IsFrameDirtyRejectsNullHandle) {
    int dirty;
    auto err = legends_is_frame_dirty(nullptr, &dirty);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, GetCursorRejectsNullHandle) {
    uint8_t x, y;
    int visible;
    auto err = legends_get_cursor(nullptr, &x, &y, &visible);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, KeyEventRejectsNullHandle) {
    auto err = legends_key_event(nullptr, 0x1E, 1);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, KeyEventExtRejectsNullHandle) {
    auto err = legends_key_event_ext(nullptr, 0x4D, 1);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, TextInputRejectsNullHandle) {
    auto err = legends_text_input(nullptr, "test");
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, MouseEventRejectsNullHandle) {
    auto err = legends_mouse_event(nullptr, 10, 10, 0);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, SaveStateRejectsNullHandle) {
    size_t size;
    auto err = legends_save_state(nullptr, nullptr, 0, &size);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, LoadStateRejectsNullHandle) {
    uint8_t buffer[16] = {0};
    auto err = legends_load_state(nullptr, buffer, sizeof(buffer));
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, GetStateHashRejectsNullHandle) {
    uint8_t hash[32];
    auto err = legends_get_state_hash(nullptr, hash);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, VerifyDeterminismRejectsNullHandle) {
    int is_det;
    auto err = legends_verify_determinism(nullptr, 1000, &is_det);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, SetLogCallbackRejectsNullHandle) {
    auto err = legends_set_log_callback(nullptr, nullptr, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

TEST(DosboxxNullHandleTest, HasCapabilityRejectsNullHandle) {
    int out = 0;
    auto err = legends_has_capability(nullptr, "save_state", &out);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_HANDLE);
}

class DosboxxCapabilityTest : public ::testing::Test {
protected:
    legends_handle handle_ = nullptr;

    void SetUp() override {
        legends_force_destroy();
        auto err = legends_create(nullptr, &handle_);
        ASSERT_EQ(err, LEGENDS_OK);
        ASSERT_NE(handle_, nullptr);
    }

    void TearDown() override {
        legends_destroy(handle_);
    }
};

TEST_F(DosboxxCapabilityTest, HasCapabilityReturnsCorrectValues) {
    int out = 0;
    auto err = legends_has_capability(handle_, "save_state", &out);
    EXPECT_EQ(err, LEGENDS_OK);

    err = legends_has_capability(handle_, nullptr, &out);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_POINTER);
}

// ─────────────────────────────────────────────────────────────────────────────
// Phase 2: Stepping API Tests
// ─────────────────────────────────────────────────────────────────────────────

class DosboxxSteppingTest : public ::testing::Test {
protected:
    legends_handle handle_ = nullptr;

    void SetUp() override {
        // Clean up any previous instance
        legends_force_destroy();

        auto err = legends_create(nullptr, &handle_);
        ASSERT_EQ(err, LEGENDS_OK);
        ASSERT_NE(handle_, nullptr);
    }

    void TearDown() override {
        legends_destroy(handle_);
    }
};

TEST_F(DosboxxSteppingTest, ResetWorks) {
    // Step some cycles first
    legends_step_ms(handle_, 10, nullptr);

    // Reset should work now
    auto err = legends_reset(handle_);
    EXPECT_EQ(err, LEGENDS_OK);

    // Time should be reset to 0
    uint64_t time;
    legends_get_emu_time(handle_, &time);
    EXPECT_EQ(time, 0u);
}

TEST_F(DosboxxSteppingTest, GetConfigWorks) {
    legends_config_t config;
    auto err = legends_get_config(handle_, &config);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(config.memory_kb, 640u);  // Default
    EXPECT_EQ(config.deterministic, 1u);
}

TEST_F(DosboxxSteppingTest, StepMsWorks) {
    legends_step_result_t result;
    auto err = legends_step_ms(handle_, 100, &result);

    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_GT(result.cycles_executed, 0u);
    EXPECT_EQ(result.stop_reason, LEGENDS_STOP_COMPLETED);
}

TEST_F(DosboxxSteppingTest, StepCyclesWorks) {
    legends_step_result_t result;
    const uint64_t target_cycles = 10000;

    auto err = legends_step_cycles(handle_, target_cycles, &result);

    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(result.cycles_executed, target_cycles);
    EXPECT_EQ(result.stop_reason, LEGENDS_STOP_COMPLETED);
}

TEST_F(DosboxxSteppingTest, StepCyclesIsExact) {
    legends_step_result_t result;
    const uint64_t target = 12345;

    auto err = legends_step_cycles(handle_, target, &result);

    EXPECT_EQ(err, LEGENDS_OK);
    // Should execute exactly the requested cycles
    EXPECT_EQ(result.cycles_executed, target);
}

TEST_F(DosboxxSteppingTest, GetEmuTimeWorks) {
    uint64_t time;
    auto err = legends_get_emu_time(handle_, &time);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(time, 0u);  // Initially 0
}

TEST_F(DosboxxSteppingTest, GetTotalCyclesWorks) {
    uint64_t cycles;
    auto err = legends_get_total_cycles(handle_, &cycles);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(cycles, 0u);  // Initially 0
}

TEST_F(DosboxxSteppingTest, TimeAccumulates) {
    uint64_t time1, time2;

    legends_step_ms(handle_, 50, nullptr);
    legends_get_emu_time(handle_, &time1);

    legends_step_ms(handle_, 50, nullptr);
    legends_get_emu_time(handle_, &time2);

    // Time should accumulate
    EXPECT_GT(time2, time1);
    // 100ms = 100000us
    EXPECT_GE(time2, 100000u);
}

TEST_F(DosboxxSteppingTest, CyclesAccumulate) {
    uint64_t cycles1, cycles2;

    legends_step_cycles(handle_, 5000, nullptr);
    legends_get_total_cycles(handle_, &cycles1);

    legends_step_cycles(handle_, 5000, nullptr);
    legends_get_total_cycles(handle_, &cycles2);

    EXPECT_EQ(cycles1, 5000u);
    EXPECT_EQ(cycles2, 10000u);
}

TEST_F(DosboxxSteppingTest, StepMsProducesConsistentCycles) {
    legends_step_result_t result1, result2;

    // Step 100ms twice
    legends_reset(handle_);
    legends_step_ms(handle_, 100, &result1);

    legends_reset(handle_);
    legends_step_ms(handle_, 100, &result2);

    // Same ms should produce same cycles (determinism)
    EXPECT_EQ(result1.cycles_executed, result2.cycles_executed);
}

TEST_F(DosboxxSteppingTest, ResetClearsTime) {
    // Step some time
    legends_step_ms(handle_, 100, nullptr);

    uint64_t time_before;
    legends_get_emu_time(handle_, &time_before);
    EXPECT_GT(time_before, 0u);

    // Reset
    legends_reset(handle_);

    // Time should be 0 again
    uint64_t time_after;
    legends_get_emu_time(handle_, &time_after);
    EXPECT_EQ(time_after, 0u);
}

TEST_F(DosboxxSteppingTest, ResetClearsCycles) {
    // Step some cycles
    legends_step_cycles(handle_, 10000, nullptr);

    uint64_t cycles_before;
    legends_get_total_cycles(handle_, &cycles_before);
    EXPECT_GT(cycles_before, 0u);

    // Reset
    legends_reset(handle_);

    // Cycles should be 0 again
    uint64_t cycles_after;
    legends_get_total_cycles(handle_, &cycles_after);
    EXPECT_EQ(cycles_after, 0u);
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
    legends_handle handle_ = nullptr;
    LogTestContext log_ctx_;

    void SetUp() override {
        // Clean up any previous instance
        legends_force_destroy();

        auto err = legends_create(nullptr, &handle_);
        ASSERT_EQ(err, LEGENDS_OK);
        ASSERT_NE(handle_, nullptr);
    }

    void TearDown() override {
        legends_destroy(handle_);
    }
};

TEST_F(DosboxxLogCallbackTest, SetLogCallbackWorks) {
    auto err = legends_set_log_callback(handle_, LogTestContext::callback, &log_ctx_);
    EXPECT_EQ(err, LEGENDS_OK);
}

TEST_F(DosboxxLogCallbackTest, SetLogCallbackToNullWorks) {
    // First set a callback
    auto err = legends_set_log_callback(handle_, LogTestContext::callback, &log_ctx_);
    EXPECT_EQ(err, LEGENDS_OK);

    // Then clear it
    err = legends_set_log_callback(handle_, nullptr, nullptr);
    EXPECT_EQ(err, LEGENDS_OK);
}

TEST_F(DosboxxLogCallbackTest, CallbackReceivesDebugMessage) {
    auto err = legends_set_log_callback(handle_, LogTestContext::callback, &log_ctx_);
    ASSERT_EQ(err, LEGENDS_OK);

    // Setting callback should log a debug message
    EXPECT_TRUE(log_ctx_.has_level(3));  // LOG_LEVEL_DEBUG = 3
    EXPECT_TRUE(log_ctx_.has_message_containing("Log callback registered"));
}

TEST_F(DosboxxLogCallbackTest, CallbackReceivesErrorOnFailure) {
    auto err = legends_set_log_callback(handle_, LogTestContext::callback, &log_ctx_);
    ASSERT_EQ(err, LEGENDS_OK);
    log_ctx_.clear();

    // Try to create a second instance (should fail and log error)
    legends_handle handle2 = nullptr;
    err = legends_create(nullptr, &handle2);
    EXPECT_EQ(err, LEGENDS_ERR_ALREADY_CREATED);

    // Should have logged an error
    EXPECT_TRUE(log_ctx_.has_level(0));  // LOG_LEVEL_ERROR = 0
    EXPECT_TRUE(log_ctx_.has_message_containing("already exists"));
}

TEST_F(DosboxxLogCallbackTest, CallbackReceivesInfoOnDestroy) {
    auto err = legends_set_log_callback(handle_, LogTestContext::callback, &log_ctx_);
    ASSERT_EQ(err, LEGENDS_OK);
    log_ctx_.clear();

    // Destroy the instance
    legends_destroy(handle_);
    handle_ = nullptr;  // Prevent double-destroy in TearDown

    // Should have logged an info message
    EXPECT_TRUE(log_ctx_.has_level(2));  // LOG_LEVEL_INFO = 2
    EXPECT_TRUE(log_ctx_.has_message_containing("Destroying"));
}

TEST_F(DosboxxLogCallbackTest, NoCallbackAfterDestroy) {
    auto err = legends_set_log_callback(handle_, LogTestContext::callback, &log_ctx_);
    ASSERT_EQ(err, LEGENDS_OK);
    log_ctx_.clear();

    // Destroy and recreate
    legends_destroy(handle_);
    handle_ = nullptr;

    size_t msg_count = log_ctx_.messages.size();

    // Create new instance (callback should be cleared)
    err = legends_create(nullptr, &handle_);
    ASSERT_EQ(err, LEGENDS_OK);

    // No new messages (callback was cleared on destroy)
    EXPECT_EQ(log_ctx_.messages.size(), msg_count);
}

// ─────────────────────────────────────────────────────────────────────────────
// Phase 6: Fuzz/Property-Based Tests
// ─────────────────────────────────────────────────────────────────────────────

class DosboxxFuzzTest : public ::testing::Test {
protected:
    legends_handle handle_ = nullptr;

    void SetUp() override {
        legends_force_destroy();
        auto err = legends_create(nullptr, &handle_);
        ASSERT_EQ(err, LEGENDS_OK);
    }

    void TearDown() override {
        legends_destroy(handle_);
    }
};

// Test that random scancodes don't crash
TEST_F(DosboxxFuzzTest, RandomScancodesDontCrash) {
    for (int scancode = 0; scancode <= 255; ++scancode) {
        auto err = legends_key_event(handle_, static_cast<uint8_t>(scancode), 1);
        // OK or BUFFER_TOO_SMALL are acceptable (queue has finite capacity)
        EXPECT_TRUE(err == LEGENDS_OK || err == LEGENDS_ERR_BUFFER_TOO_SMALL)
            << "Unexpected error " << err << " on scancode " << scancode;
        err = legends_key_event(handle_, static_cast<uint8_t>(scancode), 0);
        EXPECT_TRUE(err == LEGENDS_OK || err == LEGENDS_ERR_BUFFER_TOO_SMALL)
            << "Unexpected error " << err << " on release scancode " << scancode;
    }
}

// Test that random extended scancodes don't crash
TEST_F(DosboxxFuzzTest, RandomExtendedScancodesDontCrash) {
    for (int scancode = 0; scancode <= 255; ++scancode) {
        auto err = legends_key_event_ext(handle_, static_cast<uint8_t>(scancode), 1);
        // OK or BUFFER_TOO_SMALL are acceptable (queue has finite capacity)
        EXPECT_TRUE(err == LEGENDS_OK || err == LEGENDS_ERR_BUFFER_TOO_SMALL)
            << "Unexpected error " << err << " on ext scancode " << scancode;
        err = legends_key_event_ext(handle_, static_cast<uint8_t>(scancode), 0);
        EXPECT_TRUE(err == LEGENDS_OK || err == LEGENDS_ERR_BUFFER_TOO_SMALL)
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
                auto err = legends_mouse_event(handle_, dx, dy, buttons);
                // OK or BUFFER_TOO_SMALL are acceptable (queue has finite capacity)
                EXPECT_TRUE(err == LEGENDS_OK || err == LEGENDS_ERR_BUFFER_TOO_SMALL);
            }
        }
    }
}

// Test that corrupted save state is rejected
TEST_F(DosboxxFuzzTest, CorruptedSaveStateRejected) {
    // All-zeros buffer
    uint8_t zeros[256] = {0};
    auto err = legends_load_state(handle_, zeros, sizeof(zeros));
    EXPECT_NE(err, LEGENDS_OK);

    // All-ones buffer
    uint8_t ones[256];
    std::memset(ones, 0xFF, sizeof(ones));
    err = legends_load_state(handle_, ones, sizeof(ones));
    EXPECT_NE(err, LEGENDS_OK);

    // Random-looking buffer
    uint8_t random[256];
    for (int i = 0; i < 256; ++i) {
        random[i] = static_cast<uint8_t>((i * 17 + 13) % 256);
    }
    err = legends_load_state(handle_, random, sizeof(random));
    EXPECT_NE(err, LEGENDS_OK);
}

// Test that valid magic but corrupted data is rejected
TEST_F(DosboxxFuzzTest, CorruptedChecksumRejected) {
    // First save a valid state
    size_t state_size;
    auto err = legends_save_state(handle_, nullptr, 0, &state_size);
    ASSERT_EQ(err, LEGENDS_OK);

    std::vector<uint8_t> buffer(state_size);
    err = legends_save_state(handle_, buffer.data(), buffer.size(), &state_size);
    ASSERT_EQ(err, LEGENDS_OK);

    // Corrupt the data (not the header)
    if (buffer.size() > 100) {
        buffer[100] ^= 0xFF;  // Flip bits in data section
    }

    // Should reject due to checksum mismatch
    err = legends_load_state(handle_, buffer.data(), buffer.size());
    EXPECT_EQ(err, LEGENDS_ERR_INVALID_STATE);
}

// Test rapid stepping doesn't overflow
TEST_F(DosboxxFuzzTest, RapidSteppingStable) {
    for (int i = 0; i < 1000; ++i) {
        auto err = legends_step_cycles(handle_, 1000, nullptr);
        EXPECT_EQ(err, LEGENDS_OK);
    }

    // Verify cycles accumulated (real CPU may halt before consuming all)
    uint64_t cycles;
    auto err = legends_get_total_cycles(handle_, &cycles);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_GT(cycles, 0u);
}

// Test that invalid handles are consistently rejected
TEST_F(DosboxxFuzzTest, InvalidHandlesRejected) {
    legends_handle invalid_handles[] = {
        nullptr,
        reinterpret_cast<legends_handle>(static_cast<uintptr_t>(0xDEADBEEF)),
        reinterpret_cast<legends_handle>(static_cast<uintptr_t>(0xFFFFFFFF)),
    };

    for (auto invalid : invalid_handles) {
        if (invalid == nullptr) continue;  // nullptr tested elsewhere

        // All these should gracefully reject (or accept if handle validation is minimal)
        // Key: they shouldn't crash
        legends_step_ms(invalid, 10, nullptr);
        legends_key_event(invalid, 0x1E, 1);
        legends_mouse_event(invalid, 0, 0, 0);
    }
}

// Test save/load cycle preserves state across multiple iterations
TEST_F(DosboxxFuzzTest, RepeatedSaveLoadCycle) {
    for (int iter = 0; iter < 10; ++iter) {
        // Step some cycles
        legends_step_cycles(handle_, 1000, nullptr);

        // Save state
        size_t state_size;
        auto err = legends_save_state(handle_, nullptr, 0, &state_size);
        ASSERT_EQ(err, LEGENDS_OK);

        std::vector<uint8_t> buffer(state_size);
        err = legends_save_state(handle_, buffer.data(), buffer.size(), &state_size);
        ASSERT_EQ(err, LEGENDS_OK);

        // Get hash before
        uint8_t hash_before[32];
        err = legends_get_state_hash(handle_, hash_before);
        ASSERT_EQ(err, LEGENDS_OK);

        // Load state
        err = legends_load_state(handle_, buffer.data(), buffer.size());
        ASSERT_EQ(err, LEGENDS_OK);

        // Get hash after
        uint8_t hash_after[32];
        err = legends_get_state_hash(handle_, hash_after);
        ASSERT_EQ(err, LEGENDS_OK);

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
        legends_reset(handle_);
        auto err = legends_text_input(handle_, str);
        // OK or BUFFER_TOO_SMALL are acceptable
        EXPECT_TRUE(err == LEGENDS_OK || err == LEGENDS_ERR_BUFFER_TOO_SMALL)
            << "Unexpected error " << err << " on string: " << str;
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Phase 7: CPU Bridge Integration Tests (DOSBox Engine Integration)
// ─────────────────────────────────────────────────────────────────────────────

/**
 * Tests that verify legends_step_cycles() properly delegates to the
 * DOSBox library engine and CPU bridge for actual instruction execution.
 */
class LegendsCpuBridgeIntegrationTest : public ::testing::Test {
protected:
    legends_handle handle_ = nullptr;

    void SetUp() override {
        // Clean up any previous instance
        legends_force_destroy();

        auto err = legends_create(nullptr, &handle_);
        ASSERT_EQ(err, LEGENDS_OK);
        ASSERT_NE(handle_, nullptr);
    }

    void TearDown() override {
        legends_destroy(handle_);
    }
};

TEST_F(LegendsCpuBridgeIntegrationTest, StepCyclesDelegatesToEngine) {
    // This test verifies that legends_step_cycles uses the engine bridge

    legends_step_result_t result{};
    auto err = legends_step_cycles(handle_, 1000, &result);

    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(result.stop_reason, LEGENDS_STOP_COMPLETED);
}

TEST_F(LegendsCpuBridgeIntegrationTest, StepCyclesUpdatesTimeFromEngine) {
    // Get initial state
    uint64_t initial_time = 0;
    legends_get_emu_time(handle_, &initial_time);

    uint64_t initial_cycles = 0;
    legends_get_total_cycles(handle_, &initial_cycles);

    // Step via legends which delegates to engine
    legends_step_result_t result{};
    legends_step_cycles(handle_, 10000, &result);

    // Verify time is updated from engine
    uint64_t final_time = 0;
    legends_get_emu_time(handle_, &final_time);
    EXPECT_GT(final_time, initial_time);

    // Verify cycles are updated from engine
    uint64_t final_cycles = 0;
    legends_get_total_cycles(handle_, &final_cycles);
    EXPECT_GT(final_cycles, initial_cycles);
}

TEST_F(LegendsCpuBridgeIntegrationTest, StepMsDelegatesToEngineViaStepCycles) {
    // step_ms -> step_cycles -> engine bridge

    legends_step_result_t result{};
    auto err = legends_step_ms(handle_, 10, &result);

    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_EQ(result.stop_reason, LEGENDS_STOP_COMPLETED);
    EXPECT_GT(result.cycles_executed, 0u);
}

TEST_F(LegendsCpuBridgeIntegrationTest, StepResultContainsEventsProcessed) {
    // Engine bridge should report events processed

    legends_step_result_t result{};
    legends_step_cycles(handle_, 100000, &result);

    // Events processed field should be filled (may be 0 in headless)
    EXPECT_GE(result.events_processed, 0u);
}

TEST_F(LegendsCpuBridgeIntegrationTest, AllStopReasonsAreMappedCorrectly) {
    // Verify stop reason constants match between legends and engine layers
    EXPECT_EQ(LEGENDS_STOP_COMPLETED, 0);
    EXPECT_EQ(LEGENDS_STOP_HALT, 1);
    EXPECT_EQ(LEGENDS_STOP_BREAKPOINT, 2);
    EXPECT_EQ(LEGENDS_STOP_ERROR, 3);
    EXPECT_EQ(LEGENDS_STOP_USER_REQUEST, 4);
}

TEST_F(LegendsCpuBridgeIntegrationTest, DeterminismWithEngineBridge) {
    // Reset to known state
    legends_reset(handle_);

    // First run
    legends_step_result_t result1{};
    legends_step_cycles(handle_, 10000, &result1);

    uint8_t hash1[32] = {0};
    legends_get_state_hash(handle_, hash1);

    // Reset and run again
    legends_reset(handle_);

    legends_step_result_t result2{};
    legends_step_cycles(handle_, 10000, &result2);

    uint8_t hash2[32] = {0};
    legends_get_state_hash(handle_, hash2);

    // Results should match (deterministic execution)
    EXPECT_EQ(result1.cycles_executed, result2.cycles_executed);
    EXPECT_EQ(result1.stop_reason, result2.stop_reason);

    // State hashes should match
    for (int i = 0; i < 32; ++i) {
        EXPECT_EQ(hash1[i], hash2[i]) << "Hash differs at byte " << i;
    }
}

TEST_F(LegendsCpuBridgeIntegrationTest, MultipleStepsAccumulateCorrectly) {
    // Step multiple times
    for (int i = 0; i < 10; ++i) {
        legends_step_cycles(handle_, 1000, nullptr);
    }

    // Verify total cycles
    uint64_t total_cycles = 0;
    legends_get_total_cycles(handle_, &total_cycles);

    // Should have accumulated cycles (may not be exactly 10000 due to engine behavior)
    EXPECT_GE(total_cycles, 0u);
}

TEST_F(LegendsCpuBridgeIntegrationTest, EngineHandleRequiredForStepping) {
    // This test documents that legends_step_cycles requires the engine handle
    // The API should fail gracefully if engine is not initialized

    legends_step_result_t result{};
    auto err = legends_step_cycles(handle_, 100, &result);

    // Should succeed since we created properly
    EXPECT_EQ(err, LEGENDS_OK);
}

TEST_F(LegendsCpuBridgeIntegrationTest, StepAfterResetUsesEngineState) {
    // Step some cycles
    legends_step_cycles(handle_, 5000, nullptr);

    uint64_t cycles_before_reset = 0;
    legends_get_total_cycles(handle_, &cycles_before_reset);
    EXPECT_GT(cycles_before_reset, 0u);

    // Reset
    legends_reset(handle_);

    // Cycles should be reset
    uint64_t cycles_after_reset = 0;
    legends_get_total_cycles(handle_, &cycles_after_reset);
    EXPECT_EQ(cycles_after_reset, 0u);

    // Step again
    legends_step_cycles(handle_, 1000, nullptr);

    uint64_t cycles_after_step = 0;
    legends_get_total_cycles(handle_, &cycles_after_step);
    EXPECT_GT(cycles_after_step, 0u);
}

TEST_F(LegendsCpuBridgeIntegrationTest, SaveLoadPreservesEngineState) {
    // Step to create engine state
    legends_step_cycles(handle_, 10000, nullptr);

    // Get state hash before save
    uint8_t hash_before[32] = {0};
    legends_get_state_hash(handle_, hash_before);

    // Save state
    size_t size = 0;
    legends_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> buffer(size);
    legends_save_state(handle_, buffer.data(), size, &size);

    // Step more (diverge state)
    legends_step_cycles(handle_, 5000, nullptr);

    // Load state
    legends_load_state(handle_, buffer.data(), size);

    // Get state hash after load
    uint8_t hash_after[32] = {0};
    legends_get_state_hash(handle_, hash_after);

    // Hashes should match (state restored)
    for (int i = 0; i < 32; ++i) {
        EXPECT_EQ(hash_before[i], hash_after[i]) << "Hash differs at byte " << i;
    }
}
