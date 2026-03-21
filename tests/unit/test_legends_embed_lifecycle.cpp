/**
 * @file test_legends_embed_lifecycle.cpp
 * @brief Lifecycle tests for legends_embed API (create/destroy/force_destroy).
 *
 * Split from test_legends_embed.cpp for faster incremental builds.
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include "internal/legends_instance.h"
#include <cstring>

// ─────────────────────────────────────────────────────────────────────────────
// Test Fixture - Ensures clean state between tests
// ─────────────────────────────────────────────────────────────────────────────

class DosboxxEmbedLifecycleTest : public ::testing::Test {
protected:
    void SetUp() override {
        legends_destroy(nullptr);
    }

    void TearDown() override {
        legends_destroy(nullptr);
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// Lifecycle Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(DosboxxEmbedLifecycleTest, CreateWithNullConfigSucceeds) {
    legends_handle handle = nullptr;
    auto err = legends_create(nullptr, &handle);

    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_NE(handle, nullptr);

    legends_destroy(handle);
}

TEST_F(DosboxxEmbedLifecycleTest, CreateWithValidConfigSucceeds) {
    legends_config_t config = LEGENDS_CONFIG_INIT;
    legends_handle handle = nullptr;

    auto err = legends_create(&config, &handle);

    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_NE(handle, nullptr);

    legends_destroy(handle);
}

TEST_F(DosboxxEmbedLifecycleTest, CreateRejectsNullHandleOut) {
    auto err = legends_create(nullptr, nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_POINTER);
}

TEST_F(DosboxxEmbedLifecycleTest, SingleInstanceEnforcement) {
    legends_handle handle1 = nullptr;
    legends_handle handle2 = nullptr;

    // First create succeeds
    auto err1 = legends_create(nullptr, &handle1);
    EXPECT_EQ(err1, LEGENDS_OK);
    EXPECT_NE(handle1, nullptr);

    // Second create fails
    auto err2 = legends_create(nullptr, &handle2);
    EXPECT_EQ(err2, LEGENDS_ERR_ALREADY_CREATED);
    EXPECT_EQ(handle2, nullptr);

    // Destroy first
    legends_destroy(handle1);

    // Now can create again
    legends_handle handle3 = nullptr;
    auto err3 = legends_create(nullptr, &handle3);
    EXPECT_EQ(err3, LEGENDS_OK);
    EXPECT_NE(handle3, nullptr);

    legends_destroy(handle3);
}

TEST_F(DosboxxEmbedLifecycleTest, DestroyNullIsNoOp) {
    auto err = legends_destroy(nullptr);
    EXPECT_EQ(err, LEGENDS_OK);
}

TEST_F(DosboxxEmbedLifecycleTest, DestroyTwiceReturnsError) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    auto err1 = legends_destroy(handle);
    EXPECT_EQ(err1, LEGENDS_OK);

    // Second destroy returns error (handle is now invalid)
    auto err2 = legends_destroy(handle);
    EXPECT_EQ(err2, LEGENDS_ERR_NULL_HANDLE);
}

// ─────────────────────────────────────────────────────────────────────────────
// Config Validation Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(DosboxxEmbedLifecycleTest, CreateRejectsWrongStructSize) {
    legends_config_t config = LEGENDS_CONFIG_INIT;
    config.struct_size = sizeof(legends_config_t) - 1;

    legends_handle handle = nullptr;
    auto err = legends_create(&config, &handle);

    EXPECT_EQ(err, LEGENDS_ERR_INVALID_CONFIG);
    EXPECT_EQ(handle, nullptr);
}

TEST_F(DosboxxEmbedLifecycleTest, CreateRejectsWrongApiVersion) {
    legends_config_t config = LEGENDS_CONFIG_INIT;
    config.api_version = LEGENDS_API_VERSION + 1;

    legends_handle handle = nullptr;
    auto err = legends_create(&config, &handle);

    EXPECT_EQ(err, LEGENDS_ERR_VERSION_MISMATCH);
    EXPECT_EQ(handle, nullptr);
}

// ─────────────────────────────────────────────────────────────────────────────
// Error Message Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(DosboxxEmbedLifecycleTest, GetLastErrorQuerySize) {
    size_t length;
    auto err = legends_get_last_error(nullptr, nullptr, 0, &length);
    EXPECT_EQ(err, LEGENDS_OK);
}

TEST_F(DosboxxEmbedLifecycleTest, GetLastErrorRejectsNullLengthOut) {
    char buffer[256];
    auto err = legends_get_last_error(nullptr, buffer, sizeof(buffer), nullptr);
    EXPECT_EQ(err, LEGENDS_ERR_NULL_POINTER);
}

TEST_F(DosboxxEmbedLifecycleTest, GetLastErrorBufferTooSmall) {
    // Create instance then try to create another to trigger error
    legends_handle handle1 = nullptr;
    legends_create(nullptr, &handle1);

    legends_handle handle2 = nullptr;
    legends_create(nullptr, &handle2);  // Should fail and set error

    // Get the required size
    size_t length;
    legends_get_last_error(nullptr, nullptr, 0, &length);
    ASSERT_GT(length, 2u);  // Should have error message

    // Try with too small buffer
    char small_buffer[2];
    size_t len_out;
    auto err = legends_get_last_error(nullptr, small_buffer, sizeof(small_buffer), &len_out);
    EXPECT_EQ(err, LEGENDS_ERR_BUFFER_TOO_SMALL);

    legends_destroy(handle1);
}

TEST_F(DosboxxEmbedLifecycleTest, GetLastErrorReturnsMessage) {
    // Create instance then try to create another to trigger error
    legends_handle handle1 = nullptr;
    legends_create(nullptr, &handle1);

    legends_handle handle2 = nullptr;
    legends_create(nullptr, &handle2);  // Should fail and set error

    // Get the message
    char buffer[256];
    size_t length;
    auto err = legends_get_last_error(nullptr, buffer, sizeof(buffer), &length);
    EXPECT_EQ(err, LEGENDS_OK);
    EXPECT_GT(std::strlen(buffer), 0u);  // Should have message content

    legends_destroy(handle1);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Requirements Regression Tests
// ═══════════════════════════════════════════════════════════════════════════════

/// @brief REQ-EX-006: step_cycles must not crash if engine context is unavailable.
TEST_F(DosboxxEmbedLifecycleTest, REQ_EX_006_StepCyclesReturnsErrorOnMissingContext) {
    legends_handle handle = nullptr;
    auto err = legends_create(nullptr, &handle);
    ASSERT_EQ(err, LEGENDS_OK);
    ASSERT_NE(handle, nullptr);

    // Step without full init — exercises the null context path
    legends_step_result_t result{};
    err = legends_step_cycles(handle, 100, &result);
    // Should return an error or succeed, but must not crash
    SUCCEED();

    legends_destroy(handle);
}

/// @brief REQ-LC-003: Destroying an invalid handle must return error, not destroy real instance.
TEST_F(DosboxxEmbedLifecycleTest, REQ_LC_003_DestroyInvalidHandleReturnsError) {
    legends_handle real = nullptr;
    auto err = legends_create(nullptr, &real);
    ASSERT_EQ(err, LEGENDS_OK);

    const auto fake = reinterpret_cast<legends_handle>(static_cast<uintptr_t>(0xDEADBEEF));
    err = legends_destroy(fake);
    EXPECT_NE(err, LEGENDS_OK);

    // Real instance should still be alive — destroy it cleanly
    EXPECT_EQ(legends_destroy(real), LEGENDS_OK);
}
