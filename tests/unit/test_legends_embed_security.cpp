/**
 * @file test_legends_embed_security.cpp
 * @brief Security, reentrancy, and callback safety tests for legends_embed API.
 *
 * Split from test_legends_embed.cpp for faster incremental builds.
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include "internal/legends_instance.h"
#include <cstring>
#include <stdexcept>
#include <vector>

// ─────────────────────────────────────────────────────────────────────────────
// Test Hardening: Security and Robustness Tests
// ─────────────────────────────────────────────────────────────────────────────

class SecurityHardeningTest : public ::testing::Test {
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

    // Helper to create a valid save state buffer
    std::vector<uint8_t> createValidSaveState() {
        size_t size = 0;
        legends_save_state(handle_, nullptr, 0, &size);
        std::vector<uint8_t> buffer(size);
        legends_save_state(handle_, buffer.data(), size, &size);
        return buffer;
    }
};

// Test: Save/load rejects total_size < sizeof(header)
TEST_F(SecurityHardeningTest, LoadRejectsTotalSizeSmallerThanHeader) {
    auto buffer = createValidSaveState();

    // Corrupt: set total_size smaller than header
    // SaveStateHeader is at offset 0, total_size is at offset 8
    uint32_t* total_size_ptr = reinterpret_cast<uint32_t*>(buffer.data() + 8);
    *total_size_ptr = 10;  // Way smaller than header (96 bytes)

    auto err = legends_load_state(handle_, buffer.data(), buffer.size());
    EXPECT_EQ(err, LEGENDS_ERR_INVALID_STATE)
        << "Should reject total_size < sizeof(header)";
}

// Test: Save/load rejects total_size > buffer_size
TEST_F(SecurityHardeningTest, LoadRejectsTotalSizeLargerThanBuffer) {
    auto buffer = createValidSaveState();

    // Corrupt: set total_size larger than actual buffer
    uint32_t* total_size_ptr = reinterpret_cast<uint32_t*>(buffer.data() + 8);
    *total_size_ptr = static_cast<uint32_t>(buffer.size() * 2);

    auto err = legends_load_state(handle_, buffer.data(), buffer.size());
    // May return INVALID_STATE or BUFFER_TOO_SMALL depending on check order
    EXPECT_TRUE(err == LEGENDS_ERR_INVALID_STATE || err == LEGENDS_ERR_BUFFER_TOO_SMALL)
        << "Should reject total_size > buffer_size, got error " << err;
}

// Test: Validates all offsets against total_size
TEST_F(SecurityHardeningTest, LoadRejectsOffsetsExceedingTotalSize) {
    auto buffer = createValidSaveState();

    // Corrupt: set time_offset beyond total_size
    // time_offset is at offset 16 in SaveStateHeader
    uint32_t* time_offset_ptr = reinterpret_cast<uint32_t*>(buffer.data() + 16);
    uint32_t total_size = *reinterpret_cast<uint32_t*>(buffer.data() + 8);
    *time_offset_ptr = total_size + 1000;  // Beyond total_size

    auto err = legends_load_state(handle_, buffer.data(), buffer.size());
    EXPECT_EQ(err, LEGENDS_ERR_INVALID_STATE)
        << "Should reject offset exceeding total_size";
}

// Test: Frame bounds validation (columns/rows)
TEST_F(SecurityHardeningTest, LoadRejectsInvalidFrameGeometry) {
    auto buffer = createValidSaveState();

    // Find frame section and corrupt dimensions
    // frame_offset is at offset 48 in SaveStateHeader
    uint32_t frame_offset = *reinterpret_cast<uint32_t*>(buffer.data() + 48);
    if (frame_offset > 0 && frame_offset < buffer.size()) {
        // Frame header: columns (uint8_t), rows (uint8_t) at start
        buffer[frame_offset] = 255;      // columns > 80
        buffer[frame_offset + 1] = 255;  // rows > 50
    }

    auto err = legends_load_state(handle_, buffer.data(), buffer.size());
    EXPECT_EQ(err, LEGENDS_ERR_INVALID_STATE)
        << "Should reject invalid frame dimensions";
}

// Test: Fuzz with randomized offsets
TEST_F(SecurityHardeningTest, FuzzRandomizedOffsets) {
    auto buffer = createValidSaveState();
    const size_t header_size = 64;  // SaveStateHeader size

    // Test various corrupted offset patterns
    for (int seed = 0; seed < 50; ++seed) {
        auto corrupted = buffer;

        // Randomize an offset field (offsets start at byte 16)
        size_t offset_field = 16 + (seed % 8) * 4;  // 8 offset fields
        if (offset_field + 4 <= header_size) {
            uint32_t bad_value = static_cast<uint32_t>(seed * 12345 + 0xDEAD0000);
            std::memcpy(corrupted.data() + offset_field, &bad_value, 4);
        }

        // Should either reject or not crash
        auto err = legends_load_state(handle_, corrupted.data(), corrupted.size());
        EXPECT_NE(err, LEGENDS_OK)
            << "Corrupted state should be rejected (seed=" << seed << ")";
    }
}

// Test: Fuzz with randomized sizes
TEST_F(SecurityHardeningTest, FuzzRandomizedSizes) {
    auto buffer = createValidSaveState();

    // Test various corrupted size patterns
    size_t sizes_to_test[] = {0, 1, 10, 50, 95, 96, 97, 100, 200};
    for (size_t test_size : sizes_to_test) {
        if (test_size > buffer.size()) continue;

        auto err = legends_load_state(handle_, buffer.data(), test_size);
        // Small sizes should be rejected
        if (test_size < 96) {
            EXPECT_NE(err, LEGENDS_OK)
                << "Should reject buffer_size=" << test_size;
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Reentrancy Guard Tests (Item 8 / M1)
// ─────────────────────────────────────────────────────────────────────────────

class ReentrancyGuardTest : public ::testing::Test {
protected:
    legends_handle handle_ = nullptr;

    void SetUp() override {
        legends_destroy(reinterpret_cast<legends_handle>(1));
        auto err = legends_create(nullptr, &handle_);
        ASSERT_EQ(err, LEGENDS_OK);
        ASSERT_NE(handle_, nullptr);

        // Simulate being inside a step call
        auto* inst = reinterpret_cast<legends_instance*>(handle_);
        inst->in_step = true;
    }

    void TearDown() override {
        // Must clear in_step before destroy
        auto* inst = reinterpret_cast<legends_instance*>(handle_);
        if (inst) inst->in_step = false;
        legends_destroy(handle_);
    }
};

TEST_F(ReentrancyGuardTest, KeyEventRejectsReentrantCall) {
    EXPECT_EQ(legends_key_event(handle_, 0x1C, 1), LEGENDS_ERR_REENTRANT_CALL);
}

TEST_F(ReentrancyGuardTest, KeyEventExtRejectsReentrantCall) {
    EXPECT_EQ(legends_key_event_ext(handle_, 0x1C, 1), LEGENDS_ERR_REENTRANT_CALL);
}

TEST_F(ReentrancyGuardTest, TextInputRejectsReentrantCall) {
    EXPECT_EQ(legends_text_input(handle_, "hello"), LEGENDS_ERR_REENTRANT_CALL);
}

TEST_F(ReentrancyGuardTest, MouseEventRejectsReentrantCall) {
    EXPECT_EQ(legends_mouse_event(handle_, 10, 20, 0), LEGENDS_ERR_REENTRANT_CALL);
}

TEST_F(ReentrancyGuardTest, SaveStateRejectsReentrantCall) {
    size_t size = 0;
    EXPECT_EQ(legends_save_state(handle_, nullptr, 0, &size), LEGENDS_ERR_REENTRANT_CALL);
}

TEST_F(ReentrancyGuardTest, LoadStateRejectsReentrantCall) {
    uint8_t dummy[64] = {};
    EXPECT_EQ(legends_load_state(handle_, dummy, sizeof(dummy)), LEGENDS_ERR_REENTRANT_CALL);
}

TEST_F(ReentrancyGuardTest, ResetRejectsReentrantCall) {
    EXPECT_EQ(legends_reset(handle_), LEGENDS_ERR_REENTRANT_CALL);
}

TEST_F(ReentrancyGuardTest, StepCyclesRejectsReentrantCall) {
    EXPECT_EQ(legends_step_cycles(handle_, 100, nullptr), LEGENDS_ERR_REENTRANT_CALL);
}

// ─────────────────────────────────────────────────────────────────────────────
// Exception-Safe Callback Tests (Item 12 / M6)
// ─────────────────────────────────────────────────────────────────────────────

static void throwing_log_callback(int /*level*/, const char* /*msg*/, void* /*ud*/) {
    throw std::runtime_error("callback threw");
}

class CallbackSafetyTest : public ::testing::Test {
protected:
    legends_handle handle_ = nullptr;

    void SetUp() override {
        legends_destroy(reinterpret_cast<legends_handle>(1));
        auto err = legends_create(nullptr, &handle_);
        ASSERT_EQ(err, LEGENDS_OK);
    }

    void TearDown() override {
        legends_destroy(handle_);
    }
};

TEST_F(CallbackSafetyTest, ThrowingLogCallbackDoesNotCrash) {
    legends_set_log_callback(handle_, throwing_log_callback, nullptr);

    // This should not crash — the callback exception is swallowed
    auto err = legends_step_cycles(handle_, 100, nullptr);
    // We don't assert the specific error; just that we didn't crash
    (void)err;
}
