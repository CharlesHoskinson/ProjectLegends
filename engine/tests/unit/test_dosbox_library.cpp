/**
 * @file test_dosbox_library.cpp
 * @brief Unit tests for DOSBox-X embeddable library API (PR #22).
 *
 * Tests:
 * - Library lifecycle (create/init/destroy)
 * - Stepping API (step_ms, step_cycles)
 * - Error handling and mapping
 * - State API (get_emu_time, get_total_cycles)
 */

#include <gtest/gtest.h>
#include "dosbox/dosbox_library.h"
#include "dosbox/error_mapping.h"

// ═══════════════════════════════════════════════════════════════════════════════
// Version API Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(DOSBoxLibraryTest, GetVersionReturnsCorrectValues) {
    uint32_t major = 0, minor = 0, patch = 0;

    auto err = dosbox_lib_get_version(&major, &minor, &patch);

    EXPECT_EQ(err, DOSBOX_LIB_OK);
    EXPECT_EQ(major, DOSBOX_LIB_VERSION_MAJOR);
    EXPECT_EQ(minor, DOSBOX_LIB_VERSION_MINOR);
    EXPECT_EQ(patch, DOSBOX_LIB_VERSION_PATCH);
}

TEST(DOSBoxLibraryTest, GetVersionAcceptsNullPointers) {
    // Should not crash when any pointer is null
    EXPECT_EQ(dosbox_lib_get_version(nullptr, nullptr, nullptr), DOSBOX_LIB_OK);

    uint32_t major = 0;
    EXPECT_EQ(dosbox_lib_get_version(&major, nullptr, nullptr), DOSBOX_LIB_OK);
    EXPECT_EQ(major, DOSBOX_LIB_VERSION_MAJOR);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Lifecycle Tests
// ═══════════════════════════════════════════════════════════════════════════════

class DOSBoxLibraryLifecycleTest : public ::testing::Test {
protected:
    void TearDown() override {
        // Ensure cleanup after each test
        if (handle_) {
            dosbox_lib_destroy(handle_);
            handle_ = nullptr;
        }
    }

    dosbox_lib_handle_t handle_ = nullptr;
};

TEST_F(DOSBoxLibraryLifecycleTest, CreateWithNullConfigSucceeds) {
    auto err = dosbox_lib_create(nullptr, &handle_);

    EXPECT_EQ(err, DOSBOX_LIB_OK);
    EXPECT_NE(handle_, nullptr);
}

TEST_F(DOSBoxLibraryLifecycleTest, CreateWithValidConfigSucceeds) {
    dosbox_lib_config_t config = DOSBOX_LIB_CONFIG_INIT;

    auto err = dosbox_lib_create(&config, &handle_);

    EXPECT_EQ(err, DOSBOX_LIB_OK);
    EXPECT_NE(handle_, nullptr);
}

TEST_F(DOSBoxLibraryLifecycleTest, CreateFailsWithNullHandleOut) {
    auto err = dosbox_lib_create(nullptr, nullptr);

    EXPECT_EQ(err, DOSBOX_LIB_ERR_NULL_POINTER);
}

TEST_F(DOSBoxLibraryLifecycleTest, CreateFailsWithWrongStructSize) {
    dosbox_lib_config_t config = DOSBOX_LIB_CONFIG_INIT;
    config.struct_size = 1;  // Wrong size

    auto err = dosbox_lib_create(&config, &handle_);

    EXPECT_EQ(err, DOSBOX_LIB_ERR_INVALID_CONFIG);
}

TEST_F(DOSBoxLibraryLifecycleTest, CreateFailsWithVersionMismatch) {
    dosbox_lib_config_t config = DOSBOX_LIB_CONFIG_INIT;
    config.api_version = 0xFFFFFFFF;  // Wrong version

    auto err = dosbox_lib_create(&config, &handle_);

    EXPECT_EQ(err, DOSBOX_LIB_ERR_VERSION_MISMATCH);
}

TEST_F(DOSBoxLibraryLifecycleTest, DestroyNullHandleSucceeds) {
    auto err = dosbox_lib_destroy(nullptr);

    EXPECT_EQ(err, DOSBOX_LIB_OK);
}

TEST_F(DOSBoxLibraryLifecycleTest, InitAndDestroySucceeds) {
    ASSERT_EQ(dosbox_lib_create(nullptr, &handle_), DOSBOX_LIB_OK);

    auto err = dosbox_lib_init(handle_);
    EXPECT_EQ(err, DOSBOX_LIB_OK);

    err = dosbox_lib_destroy(handle_);
    EXPECT_EQ(err, DOSBOX_LIB_OK);
    handle_ = nullptr;  // Prevent double-destroy in TearDown
}

TEST_F(DOSBoxLibraryLifecycleTest, InitFailsWithNullHandle) {
    auto err = dosbox_lib_init(nullptr);

    EXPECT_EQ(err, DOSBOX_LIB_ERR_NULL_HANDLE);
}

TEST_F(DOSBoxLibraryLifecycleTest, ResetSucceeds) {
    ASSERT_EQ(dosbox_lib_create(nullptr, &handle_), DOSBOX_LIB_OK);
    ASSERT_EQ(dosbox_lib_init(handle_), DOSBOX_LIB_OK);

    auto err = dosbox_lib_reset(handle_);

    EXPECT_EQ(err, DOSBOX_LIB_OK);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Stepping API Tests
// ═══════════════════════════════════════════════════════════════════════════════

class DOSBoxLibraryStepTest : public ::testing::Test {
protected:
    void SetUp() override {
        ASSERT_EQ(dosbox_lib_create(nullptr, &handle_), DOSBOX_LIB_OK);
        ASSERT_EQ(dosbox_lib_init(handle_), DOSBOX_LIB_OK);
    }

    void TearDown() override {
        if (handle_) {
            dosbox_lib_destroy(handle_);
            handle_ = nullptr;
        }
    }

    dosbox_lib_handle_t handle_ = nullptr;
};

TEST_F(DOSBoxLibraryStepTest, StepMsSucceeds) {
    dosbox_lib_step_result_t result{};

    auto err = dosbox_lib_step_ms(handle_, 100, &result);

    EXPECT_EQ(err, DOSBOX_LIB_OK);
    EXPECT_GT(result.cycles_executed, 0u);
    EXPECT_GT(result.emu_time_us, 0u);
    EXPECT_EQ(result.stop_reason, DOSBOX_LIB_STOP_COMPLETED);
}

TEST_F(DOSBoxLibraryStepTest, StepCyclesSucceeds) {
    dosbox_lib_step_result_t result{};

    auto err = dosbox_lib_step_cycles(handle_, 10000, &result);

    EXPECT_EQ(err, DOSBOX_LIB_OK);
    EXPECT_EQ(result.cycles_executed, 10000u);
    EXPECT_EQ(result.stop_reason, DOSBOX_LIB_STOP_COMPLETED);
}

TEST_F(DOSBoxLibraryStepTest, StepMsAcceptsNullResult) {
    auto err = dosbox_lib_step_ms(handle_, 10, nullptr);

    EXPECT_EQ(err, DOSBOX_LIB_OK);
}

TEST_F(DOSBoxLibraryStepTest, StepFailsWithNullHandle) {
    dosbox_lib_step_result_t result{};

    auto err = dosbox_lib_step_ms(nullptr, 100, &result);

    EXPECT_EQ(err, DOSBOX_LIB_ERR_NULL_HANDLE);
}

TEST_F(DOSBoxLibraryStepTest, GetEmuTimeSucceeds) {
    // Step to accumulate time
    dosbox_lib_step_ms(handle_, 10, nullptr);

    uint64_t time_us = 0;
    auto err = dosbox_lib_get_emu_time(handle_, &time_us);

    EXPECT_EQ(err, DOSBOX_LIB_OK);
    EXPECT_GT(time_us, 0u);
}

TEST_F(DOSBoxLibraryStepTest, GetTotalCyclesSucceeds) {
    // Step to accumulate cycles
    dosbox_lib_step_cycles(handle_, 5000, nullptr);

    uint64_t cycles = 0;
    auto err = dosbox_lib_get_total_cycles(handle_, &cycles);

    EXPECT_EQ(err, DOSBOX_LIB_OK);
    EXPECT_EQ(cycles, 5000u);
}

TEST_F(DOSBoxLibraryStepTest, CyclesAccumulateAcrossSteps) {
    dosbox_lib_step_cycles(handle_, 1000, nullptr);
    dosbox_lib_step_cycles(handle_, 2000, nullptr);
    dosbox_lib_step_cycles(handle_, 3000, nullptr);

    uint64_t cycles = 0;
    dosbox_lib_get_total_cycles(handle_, &cycles);

    EXPECT_EQ(cycles, 6000u);
}

TEST_F(DOSBoxLibraryStepTest, ResetClearsCycles) {
    dosbox_lib_step_cycles(handle_, 10000, nullptr);
    dosbox_lib_reset(handle_);

    uint64_t cycles = 0;
    dosbox_lib_get_total_cycles(handle_, &cycles);

    EXPECT_EQ(cycles, 0u);
}

// ═══════════════════════════════════════════════════════════════════════════════
// State API Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(DOSBoxLibraryStepTest, GetStateHashSucceeds) {
    uint8_t hash[32] = {0};

    auto err = dosbox_lib_get_state_hash(handle_, hash);

    EXPECT_EQ(err, DOSBOX_LIB_OK);
    // Hash should be non-zero (at least some byte)
    bool all_zero = true;
    for (int i = 0; i < 32; ++i) {
        if (hash[i] != 0) {
            all_zero = false;
            break;
        }
    }
    EXPECT_FALSE(all_zero);
}

TEST_F(DOSBoxLibraryStepTest, SaveStateQuerySize) {
    size_t size = 0;

    auto err = dosbox_lib_save_state(handle_, nullptr, 0, &size);

    EXPECT_EQ(err, DOSBOX_LIB_OK);
    EXPECT_GT(size, 0u);
}

TEST_F(DOSBoxLibraryStepTest, SaveAndLoadState) {
    // Step to create state
    dosbox_lib_step_ms(handle_, 50, nullptr);

    // Get required size
    size_t size = 0;
    dosbox_lib_save_state(handle_, nullptr, 0, &size);

    // Save state
    std::vector<uint8_t> buffer(size);
    auto err = dosbox_lib_save_state(handle_, buffer.data(), size, &size);
    EXPECT_EQ(err, DOSBOX_LIB_OK);

    // Reset and verify time is zero
    dosbox_lib_reset(handle_);
    uint64_t time_us = 0;
    dosbox_lib_get_emu_time(handle_, &time_us);
    EXPECT_EQ(time_us, 0u);

    // Load state
    err = dosbox_lib_load_state(handle_, buffer.data(), size);
    EXPECT_EQ(err, DOSBOX_LIB_OK);

    // Verify time is restored
    dosbox_lib_get_emu_time(handle_, &time_us);
    EXPECT_GT(time_us, 0u);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Error Handling Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(DOSBoxLibraryStepTest, GetLastErrorSucceeds) {
    size_t length = 0;

    auto err = dosbox_lib_get_last_error(handle_, nullptr, 0, &length);

    EXPECT_EQ(err, DOSBOX_LIB_OK);
}

TEST_F(DOSBoxLibraryStepTest, SetLogCallbackSucceeds) {
    auto callback = [](int level, const char* message, void* userdata) {
        // Do nothing
    };

    auto err = dosbox_lib_set_log_callback(handle_, callback, nullptr);

    EXPECT_EQ(err, DOSBOX_LIB_OK);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Error Mapping Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(ErrorMappingTest, ErrorCodesAreCompatible) {
    // Verify that our error codes map correctly
    EXPECT_EQ(dosbox_to_legends_error(DOSBOX_LIB_OK), 0);
    EXPECT_EQ(dosbox_to_legends_error(DOSBOX_LIB_ERR_NULL_HANDLE), -1);
    EXPECT_EQ(dosbox_to_legends_error(DOSBOX_LIB_ERR_NULL_POINTER), -2);
    EXPECT_EQ(dosbox_to_legends_error(DOSBOX_LIB_ERR_INTERNAL), -13);
}

TEST(ErrorMappingTest, ErrorNamesAreMeaningful) {
    EXPECT_STREQ(dosbox_lib_error_name(DOSBOX_LIB_OK), "DOSBOX_LIB_OK");
    EXPECT_STREQ(dosbox_lib_error_name(DOSBOX_LIB_ERR_NULL_HANDLE), "DOSBOX_LIB_ERR_NULL_HANDLE");
    EXPECT_STREQ(dosbox_lib_error_name(DOSBOX_LIB_ERR_INTERNAL), "DOSBOX_LIB_ERR_INTERNAL");
}

TEST(ErrorMappingTest, CppWrapperWorks) {
    EXPECT_EQ(dosbox::ErrorMapping::to_legends(DOSBOX_LIB_OK), 0);
    EXPECT_EQ(dosbox::ErrorMapping::from_legends(-1), DOSBOX_LIB_ERR_NULL_HANDLE);
    EXPECT_STREQ(dosbox::ErrorMapping::name(DOSBOX_LIB_OK), "DOSBOX_LIB_OK");
}

// ═══════════════════════════════════════════════════════════════════════════════
// Single Instance Enforcement Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(DOSBoxLibrarySingleInstanceTest, SecondCreateFails) {
    dosbox_lib_handle_t handle1 = nullptr;
    dosbox_lib_handle_t handle2 = nullptr;

    // First create succeeds
    auto err = dosbox_lib_create(nullptr, &handle1);
    ASSERT_EQ(err, DOSBOX_LIB_OK);

    // Second create fails
    err = dosbox_lib_create(nullptr, &handle2);
    EXPECT_EQ(err, DOSBOX_LIB_ERR_ALREADY_CREATED);
    EXPECT_EQ(handle2, nullptr);

    // Cleanup
    dosbox_lib_destroy(handle1);
}

TEST(DOSBoxLibrarySingleInstanceTest, CanCreateAfterDestroy) {
    dosbox_lib_handle_t handle = nullptr;

    // Create and destroy
    ASSERT_EQ(dosbox_lib_create(nullptr, &handle), DOSBOX_LIB_OK);
    ASSERT_EQ(dosbox_lib_destroy(handle), DOSBOX_LIB_OK);

    // Create again should succeed
    handle = nullptr;
    auto err = dosbox_lib_create(nullptr, &handle);
    EXPECT_EQ(err, DOSBOX_LIB_OK);
    EXPECT_NE(handle, nullptr);

    // Cleanup
    dosbox_lib_destroy(handle);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Sprint 2 Phase 1: Context-Free Operation Tests
// ═══════════════════════════════════════════════════════════════════════════════

#include "dosbox/dosbox_context.h"
#include "dosbox/state_hash.h"

class Sprint2Phase1Test : public ::testing::Test {
protected:
    void SetUp() override {
        // Ensure no thread-local context leaks from previous tests
        dosbox::set_current_context(nullptr);

        auto err = dosbox_lib_create(nullptr, &handle_);
        ASSERT_EQ(err, DOSBOX_LIB_OK);
        err = dosbox_lib_init(handle_);
        ASSERT_EQ(err, DOSBOX_LIB_OK);
    }

    void TearDown() override {
        if (handle_) {
            dosbox_lib_destroy(handle_);
            handle_ = nullptr;
        }
        // Clean up thread-local context
        dosbox::set_current_context(nullptr);
    }

    dosbox_lib_handle_t handle_ = nullptr;
};

TEST_F(Sprint2Phase1Test, StepWithoutThreadLocalContext) {
    // Verify no thread-local context is set
    ASSERT_FALSE(dosbox::has_current_context());

    // Step should work without thread-local context
    dosbox_lib_step_result_t result = {};
    auto err = dosbox_lib_step_cycles(handle_, 1000, &result);

    EXPECT_EQ(err, DOSBOX_LIB_OK);
    EXPECT_GT(result.cycles_executed, 0u);

    // Thread-local context should still be empty after step
    EXPECT_FALSE(dosbox::has_current_context());
}

TEST_F(Sprint2Phase1Test, GetHashWithoutThreadLocalContext) {
    // Verify no thread-local context is set
    ASSERT_FALSE(dosbox::has_current_context());

    // Hash should work without thread-local context
    uint8_t hash[32] = {0};
    auto err = dosbox_lib_get_state_hash(handle_, hash);

    EXPECT_EQ(err, DOSBOX_LIB_OK);

    // Verify non-zero hash
    bool all_zero = true;
    for (int i = 0; i < 32; ++i) {
        if (hash[i] != 0) {
            all_zero = false;
            break;
        }
    }
    EXPECT_FALSE(all_zero);
}

TEST_F(Sprint2Phase1Test, StepThenHashWithoutThreadLocalContext) {
    ASSERT_FALSE(dosbox::has_current_context());

    // Get initial hash
    uint8_t hash1[32] = {0};
    dosbox_lib_get_state_hash(handle_, hash1);

    // Step
    dosbox_lib_step_cycles(handle_, 5000, nullptr);

    // Get hash after step
    uint8_t hash2[32] = {0};
    dosbox_lib_get_state_hash(handle_, hash2);

    // Hashes should differ (state changed)
    bool same = true;
    for (int i = 0; i < 32; ++i) {
        if (hash1[i] != hash2[i]) {
            same = false;
            break;
        }
    }
    EXPECT_FALSE(same);

    // Thread-local context should remain empty
    EXPECT_FALSE(dosbox::has_current_context());
}

TEST_F(Sprint2Phase1Test, MultipleStepsWithoutThreadLocalContext) {
    ASSERT_FALSE(dosbox::has_current_context());

    uint64_t total_cycles = 0;

    // Multiple steps should all work
    for (int i = 0; i < 10; ++i) {
        dosbox_lib_step_result_t result = {};
        auto err = dosbox_lib_step_cycles(handle_, 1000, &result);
        EXPECT_EQ(err, DOSBOX_LIB_OK);
        total_cycles += result.cycles_executed;
    }

    EXPECT_EQ(total_cycles, 10000u);

    // Thread-local context should remain empty throughout
    EXPECT_FALSE(dosbox::has_current_context());
}

TEST_F(Sprint2Phase1Test, DeterministicHashingWithoutThreadLocalContext) {
    ASSERT_FALSE(dosbox::has_current_context());

    // Get hash twice in a row without stepping
    uint8_t hash1[32] = {0};
    uint8_t hash2[32] = {0};

    dosbox_lib_get_state_hash(handle_, hash1);
    dosbox_lib_get_state_hash(handle_, hash2);

    // Should be identical (deterministic)
    for (int i = 0; i < 32; ++i) {
        EXPECT_EQ(hash1[i], hash2[i]);
    }
}

TEST_F(Sprint2Phase1Test, InitDestroyWithoutThreadLocalContextLeak) {
    // Destroy current handle
    dosbox_lib_destroy(handle_);
    handle_ = nullptr;

    // Thread-local context should not be set after destroy
    EXPECT_FALSE(dosbox::has_current_context());

    // Create new instance
    auto err = dosbox_lib_create(nullptr, &handle_);
    ASSERT_EQ(err, DOSBOX_LIB_OK);

    // Thread-local context should not be set after create
    EXPECT_FALSE(dosbox::has_current_context());

    err = dosbox_lib_init(handle_);
    ASSERT_EQ(err, DOSBOX_LIB_OK);

    // Thread-local context should not be set after init (Sprint 2 Phase 1)
    EXPECT_FALSE(dosbox::has_current_context());
}
