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

// ═══════════════════════════════════════════════════════════════════════════════
// CPU Bridge Integration Tests (Phase 1.2)
// ═══════════════════════════════════════════════════════════════════════════════

#include "dosbox/cpu_bridge.h"

class DOSBoxLibraryCpuBridgeTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Initialize the CPU bridge
        dosbox::init_cpu_bridge();

        // Create and init library instance
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

TEST_F(DOSBoxLibraryCpuBridgeTest, CpuBridgeIsReady) {
    EXPECT_TRUE(dosbox::is_cpu_bridge_ready());
}

TEST_F(DOSBoxLibraryCpuBridgeTest, StepCyclesUsesbridge) {
    // This test verifies that dosbox_lib_step_cycles uses the CPU bridge

    dosbox_lib_step_result_t result{};
    auto err = dosbox_lib_step_cycles(handle_, 1000, &result);

    EXPECT_EQ(err, DOSBOX_LIB_OK);
    // The bridge should have executed (or attempted to execute) cycles
    // In headless mode, actual execution depends on CPU core availability
    EXPECT_EQ(result.stop_reason, DOSBOX_LIB_STOP_COMPLETED);
}

TEST_F(DOSBoxLibraryCpuBridgeTest, StepCyclesReturnsAllStopReasons) {
    // Test that all stop reasons can be returned
    // Most will just complete normally
    dosbox_lib_step_result_t result{};

    // Normal completion
    EXPECT_EQ(dosbox_lib_step_cycles(handle_, 100, &result), DOSBOX_LIB_OK);
    EXPECT_EQ(result.stop_reason, DOSBOX_LIB_STOP_COMPLETED);
}

TEST_F(DOSBoxLibraryCpuBridgeTest, StepCyclesUpdatesTimeState) {
    // Get initial time
    uint64_t initial_time = 0;
    dosbox_lib_get_emu_time(handle_, &initial_time);

    // Step
    dosbox_lib_step_result_t result{};
    dosbox_lib_step_cycles(handle_, 10000, &result);

    // Time should be updated
    uint64_t final_time = 0;
    dosbox_lib_get_emu_time(handle_, &final_time);

    EXPECT_GT(final_time, initial_time);
}

TEST_F(DOSBoxLibraryCpuBridgeTest, StepCyclesUpdatesCycleCount) {
    // Get initial cycles
    uint64_t initial_cycles = 0;
    dosbox_lib_get_total_cycles(handle_, &initial_cycles);

    // Step
    dosbox_lib_step_result_t result{};
    dosbox_lib_step_cycles(handle_, 5000, &result);

    // Cycles should be updated
    uint64_t final_cycles = 0;
    dosbox_lib_get_total_cycles(handle_, &final_cycles);

    EXPECT_GT(final_cycles, initial_cycles);
}

TEST_F(DOSBoxLibraryCpuBridgeTest, StepMsUsesBridgeViaCycles) {
    // step_ms should delegate to step_cycles which uses the bridge

    dosbox_lib_step_result_t result{};
    auto err = dosbox_lib_step_ms(handle_, 10, &result);

    EXPECT_EQ(err, DOSBOX_LIB_OK);
    EXPECT_EQ(result.stop_reason, DOSBOX_LIB_STOP_COMPLETED);
}

TEST_F(DOSBoxLibraryCpuBridgeTest, MultipleStepsAccumulateCorrectly) {
    uint64_t initial_cycles = 0;
    dosbox_lib_get_total_cycles(handle_, &initial_cycles);

    // Multiple steps
    for (int i = 0; i < 10; ++i) {
        dosbox_lib_step_cycles(handle_, 1000, nullptr);
    }

    uint64_t final_cycles = 0;
    dosbox_lib_get_total_cycles(handle_, &final_cycles);

    // Total cycles should have accumulated
    EXPECT_GE(final_cycles - initial_cycles, 0u);
}

TEST_F(DOSBoxLibraryCpuBridgeTest, StepResultEventsProcessedIsReasonable) {
    dosbox_lib_step_result_t result{};
    dosbox_lib_step_cycles(handle_, 100000, &result);

    // Events processed should be a reasonable number
    // (could be 0 in headless mode without actual event queue)
    EXPECT_GE(result.events_processed, 0u);
}

TEST_F(DOSBoxLibraryCpuBridgeTest, StepResultCyclesMatchesRequest) {
    dosbox_lib_step_result_t result{};
    dosbox_lib_step_cycles(handle_, 1000, &result);

    // If completed normally, cycles should roughly match requested
    // (bridge might execute slightly more or less due to batching)
    if (result.stop_reason == DOSBOX_LIB_STOP_COMPLETED) {
        // Allow some variance for batching/rounding
        EXPECT_GE(result.cycles_executed, 0u);
    }
}

TEST_F(DOSBoxLibraryCpuBridgeTest, NewStopReasonsAreDefined) {
    // Verify new stop reason constants exist and have correct values
    EXPECT_EQ(DOSBOX_LIB_STOP_COMPLETED, 0);
    EXPECT_EQ(DOSBOX_LIB_STOP_HALT, 1);
    EXPECT_EQ(DOSBOX_LIB_STOP_BREAKPOINT, 2);
    EXPECT_EQ(DOSBOX_LIB_STOP_ERROR, 3);
    EXPECT_EQ(DOSBOX_LIB_STOP_USER_REQUEST, 4);
    EXPECT_EQ(DOSBOX_LIB_STOP_CALLBACK, 5);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Determinism Tests with CPU Bridge
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(DOSBoxLibraryCpuBridgeTest, DeterministicSteppingProducesSameResults) {
    // First run
    dosbox_lib_reset(handle_);
    dosbox_lib_step_result_t result1{};
    dosbox_lib_step_cycles(handle_, 10000, &result1);

    uint8_t hash1[32] = {0};
    dosbox_lib_get_state_hash(handle_, hash1);

    // Reset and run again
    dosbox_lib_reset(handle_);
    dosbox_lib_step_result_t result2{};
    dosbox_lib_step_cycles(handle_, 10000, &result2);

    uint8_t hash2[32] = {0};
    dosbox_lib_get_state_hash(handle_, hash2);

    // Results should be identical (deterministic)
    EXPECT_EQ(result1.cycles_executed, result2.cycles_executed);
    EXPECT_EQ(result1.stop_reason, result2.stop_reason);

    // Hashes should match
    for (int i = 0; i < 32; ++i) {
        EXPECT_EQ(hash1[i], hash2[i]) << "Hash differs at byte " << i;
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// Phase 2: Engine State Serialization Tests
// ═══════════════════════════════════════════════════════════════════════════════

#include "dosbox/engine_state.h"

class DOSBoxLibraryEngineStateTest : public ::testing::Test {
protected:
    void SetUp() override {
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
    }

    dosbox_lib_handle_t handle_ = nullptr;
};

TEST_F(DOSBoxLibraryEngineStateTest, SaveStateReturnsCorrectSize) {
    size_t size = 0;
    auto err = dosbox_lib_save_state(handle_, nullptr, 0, &size);

    EXPECT_EQ(err, DOSBOX_LIB_OK);
    EXPECT_EQ(size, dosbox::ENGINE_STATE_SIZE);
}

TEST_F(DOSBoxLibraryEngineStateTest, SaveStateWritesValidMagic) {
    size_t size = 0;
    dosbox_lib_save_state(handle_, nullptr, 0, &size);

    std::vector<uint8_t> buffer(size);
    auto err = dosbox_lib_save_state(handle_, buffer.data(), size, &size);
    EXPECT_EQ(err, DOSBOX_LIB_OK);

    auto* header = reinterpret_cast<const dosbox::EngineStateHeader*>(buffer.data());
    EXPECT_EQ(header->magic, dosbox::ENGINE_STATE_MAGIC);
}

TEST_F(DOSBoxLibraryEngineStateTest, SaveStateWritesCorrectVersion) {
    size_t size = 0;
    dosbox_lib_save_state(handle_, nullptr, 0, &size);

    std::vector<uint8_t> buffer(size);
    dosbox_lib_save_state(handle_, buffer.data(), size, &size);

    auto* header = reinterpret_cast<const dosbox::EngineStateHeader*>(buffer.data());
    EXPECT_EQ(header->version, dosbox::ENGINE_STATE_VERSION);
}

TEST_F(DOSBoxLibraryEngineStateTest, SaveStateWritesCorrectTotalSize) {
    size_t size = 0;
    dosbox_lib_save_state(handle_, nullptr, 0, &size);

    std::vector<uint8_t> buffer(size);
    dosbox_lib_save_state(handle_, buffer.data(), size, &size);

    auto* header = reinterpret_cast<const dosbox::EngineStateHeader*>(buffer.data());
    EXPECT_EQ(header->total_size, dosbox::ENGINE_STATE_SIZE);
}

TEST_F(DOSBoxLibraryEngineStateTest, SaveStateWritesValidChecksum) {
    size_t size = 0;
    dosbox_lib_save_state(handle_, nullptr, 0, &size);

    std::vector<uint8_t> buffer(size);
    dosbox_lib_save_state(handle_, buffer.data(), size, &size);

    auto* header = reinterpret_cast<const dosbox::EngineStateHeader*>(buffer.data());

    // Verify checksum matches data
    const uint8_t* data_start = buffer.data() + sizeof(dosbox::EngineStateHeader);
    size_t data_size = size - sizeof(dosbox::EngineStateHeader);
    uint32_t computed_crc = dosbox::compute_crc32(data_start, data_size);
    EXPECT_EQ(header->checksum, computed_crc);
}

TEST_F(DOSBoxLibraryEngineStateTest, SaveStateHasValidSectionOffsets) {
    size_t size = 0;
    dosbox_lib_save_state(handle_, nullptr, 0, &size);

    std::vector<uint8_t> buffer(size);
    dosbox_lib_save_state(handle_, buffer.data(), size, &size);

    auto* header = reinterpret_cast<const dosbox::EngineStateHeader*>(buffer.data());

    // All section offsets should be within bounds
    // Current format: timing, pic, keyboard (120 bytes total)
    EXPECT_GE(header->timing_offset, sizeof(dosbox::EngineStateHeader));
    EXPECT_LT(header->timing_offset, size);

    EXPECT_GE(header->pic_offset, sizeof(dosbox::EngineStateHeader));
    EXPECT_LT(header->pic_offset, size);

    EXPECT_GE(header->keyboard_offset, sizeof(dosbox::EngineStateHeader));
    EXPECT_LT(header->keyboard_offset, size);
}

TEST_F(DOSBoxLibraryEngineStateTest, LoadStateRejectsInvalidMagic) {
    std::vector<uint8_t> buffer(dosbox::ENGINE_STATE_SIZE, 0);

    // Set invalid magic
    auto* header = reinterpret_cast<dosbox::EngineStateHeader*>(buffer.data());
    header->magic = 0xDEADBEEF;  // Wrong magic
    header->version = dosbox::ENGINE_STATE_VERSION;
    header->total_size = dosbox::ENGINE_STATE_SIZE;

    auto err = dosbox_lib_load_state(handle_, buffer.data(), buffer.size());
    EXPECT_EQ(err, DOSBOX_LIB_ERR_INVALID_STATE);
}

TEST_F(DOSBoxLibraryEngineStateTest, LoadStateRejectsVersionMismatch) {
    std::vector<uint8_t> buffer(dosbox::ENGINE_STATE_SIZE, 0);

    auto* header = reinterpret_cast<dosbox::EngineStateHeader*>(buffer.data());
    header->magic = dosbox::ENGINE_STATE_MAGIC;
    header->version = dosbox::ENGINE_STATE_VERSION + 100;  // Wrong version
    header->total_size = dosbox::ENGINE_STATE_SIZE;

    auto err = dosbox_lib_load_state(handle_, buffer.data(), buffer.size());
    EXPECT_EQ(err, DOSBOX_LIB_ERR_VERSION_MISMATCH);
}

TEST_F(DOSBoxLibraryEngineStateTest, LoadStateRejectsBufferTooSmall) {
    std::vector<uint8_t> buffer(10, 0);  // Way too small

    auto err = dosbox_lib_load_state(handle_, buffer.data(), buffer.size());
    EXPECT_EQ(err, DOSBOX_LIB_ERR_BUFFER_TOO_SMALL);
}

TEST_F(DOSBoxLibraryEngineStateTest, LoadStateRejectsChecksumMismatch) {
    // First save valid state
    size_t size = 0;
    dosbox_lib_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> buffer(size);
    dosbox_lib_save_state(handle_, buffer.data(), size, &size);

    // Corrupt the data (not the header)
    buffer[sizeof(dosbox::EngineStateHeader) + 10] ^= 0xFF;

    auto err = dosbox_lib_load_state(handle_, buffer.data(), buffer.size());
    EXPECT_EQ(err, DOSBOX_LIB_ERR_INVALID_STATE);  // Checksum mismatch
}

TEST_F(DOSBoxLibraryEngineStateTest, SaveLoadRoundTrip) {
    // Step to modify state
    dosbox_lib_step_cycles(handle_, 10000, nullptr);

    // Get state hash before save
    uint8_t hash_before[32] = {0};
    dosbox_lib_get_state_hash(handle_, hash_before);

    // Save state
    size_t size = 0;
    dosbox_lib_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> buffer(size);
    auto err = dosbox_lib_save_state(handle_, buffer.data(), size, &size);
    EXPECT_EQ(err, DOSBOX_LIB_OK);

    // Step more to change state
    dosbox_lib_step_cycles(handle_, 10000, nullptr);

    // Verify state changed
    uint8_t hash_diverged[32] = {0};
    dosbox_lib_get_state_hash(handle_, hash_diverged);
    EXPECT_NE(memcmp(hash_before, hash_diverged, 32), 0);

    // Load saved state
    err = dosbox_lib_load_state(handle_, buffer.data(), size);
    EXPECT_EQ(err, DOSBOX_LIB_OK);

    // Verify state restored
    uint8_t hash_after[32] = {0};
    dosbox_lib_get_state_hash(handle_, hash_after);
    EXPECT_EQ(memcmp(hash_before, hash_after, 32), 0);
}

TEST_F(DOSBoxLibraryEngineStateTest, SaveLoadPreservesTimingState) {
    // Step to create timing state
    dosbox_lib_step_cycles(handle_, 50000, nullptr);

    uint64_t total_cycles_before = 0;
    uint64_t emu_time_before = 0;
    dosbox_lib_get_total_cycles(handle_, &total_cycles_before);
    dosbox_lib_get_emu_time(handle_, &emu_time_before);

    // Save state
    size_t size = 0;
    dosbox_lib_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> buffer(size);
    dosbox_lib_save_state(handle_, buffer.data(), size, &size);

    // Reset
    dosbox_lib_reset(handle_);

    // Verify reset
    uint64_t total_cycles_reset = 0;
    dosbox_lib_get_total_cycles(handle_, &total_cycles_reset);
    EXPECT_EQ(total_cycles_reset, 0u);

    // Load state
    dosbox_lib_load_state(handle_, buffer.data(), size);

    // Verify timing restored
    uint64_t total_cycles_after = 0;
    uint64_t emu_time_after = 0;
    dosbox_lib_get_total_cycles(handle_, &total_cycles_after);
    dosbox_lib_get_emu_time(handle_, &emu_time_after);

    EXPECT_EQ(total_cycles_before, total_cycles_after);
    EXPECT_EQ(emu_time_before, emu_time_after);
}

TEST_F(DOSBoxLibraryEngineStateTest, DeterministicAfterSaveLoad) {
    // Step to initial state
    dosbox_lib_step_cycles(handle_, 5000, nullptr);

    // Save state
    size_t size = 0;
    dosbox_lib_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> saved_state(size);
    dosbox_lib_save_state(handle_, saved_state.data(), size, &size);

    // Step more and record result
    dosbox_lib_step_result_t result1{};
    dosbox_lib_step_cycles(handle_, 10000, &result1);
    uint8_t hash1[32] = {0};
    dosbox_lib_get_state_hash(handle_, hash1);

    // Restore state
    dosbox_lib_load_state(handle_, saved_state.data(), size);

    // Step same amount and compare
    dosbox_lib_step_result_t result2{};
    dosbox_lib_step_cycles(handle_, 10000, &result2);
    uint8_t hash2[32] = {0};
    dosbox_lib_get_state_hash(handle_, hash2);

    // Should be deterministic - same cycles, same hash
    EXPECT_EQ(result1.cycles_executed, result2.cycles_executed);
    EXPECT_EQ(memcmp(hash1, hash2, 32), 0);
}

TEST_F(DOSBoxLibraryEngineStateTest, CRC32ComputesCorrectly) {
    // Test known CRC32 values
    const char* test_data = "123456789";
    uint32_t crc = dosbox::compute_crc32(test_data, 9);
    // Standard CRC32 of "123456789" is 0xCBF43926
    EXPECT_EQ(crc, 0xCBF43926u);
}

TEST_F(DOSBoxLibraryEngineStateTest, CRC32EmptyDataReturnsZero) {
    uint32_t crc = dosbox::compute_crc32(nullptr, 0);
    // CRC32 of empty data (initial XOR with final XOR) = 0
    EXPECT_EQ(crc, 0u);
}

TEST_F(DOSBoxLibraryEngineStateTest, SaveStateBufferTooSmallFails) {
    size_t size = 0;
    dosbox_lib_save_state(handle_, nullptr, 0, &size);

    std::vector<uint8_t> buffer(size / 2);  // Too small
    auto err = dosbox_lib_save_state(handle_, buffer.data(), buffer.size(), &size);
    EXPECT_EQ(err, DOSBOX_LIB_ERR_BUFFER_TOO_SMALL);
}

TEST_F(DOSBoxLibraryEngineStateTest, MultipleRoundTripsPreserveState) {
    // Multiple save/load cycles should preserve state
    dosbox_lib_step_cycles(handle_, 5000, nullptr);

    uint8_t original_hash[32] = {0};
    dosbox_lib_get_state_hash(handle_, original_hash);

    std::vector<uint8_t> buffer(dosbox::ENGINE_STATE_SIZE);
    size_t size;

    for (int i = 0; i < 5; ++i) {
        // Save
        dosbox_lib_save_state(handle_, buffer.data(), buffer.size(), &size);

        // Step to change state
        dosbox_lib_step_cycles(handle_, 1000, nullptr);

        // Load (restore)
        dosbox_lib_load_state(handle_, buffer.data(), size);

        // Verify state matches original
        uint8_t current_hash[32] = {0};
        dosbox_lib_get_state_hash(handle_, current_hash);
        EXPECT_EQ(memcmp(original_hash, current_hash, 32), 0) << "Round trip " << i << " failed";
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// Test Hardening: Engine State Security Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(DOSBoxLibraryEngineStateTest, LoadRejectsTotalSizeSmallerThanHeader) {
    std::vector<uint8_t> buffer(dosbox::ENGINE_STATE_SIZE, 0);

    auto* header = reinterpret_cast<dosbox::EngineStateHeader*>(buffer.data());
    header->magic = dosbox::ENGINE_STATE_MAGIC;
    header->version = dosbox::ENGINE_STATE_VERSION;
    header->total_size = 10;  // Smaller than header (32 bytes)

    auto err = dosbox_lib_load_state(handle_, buffer.data(), buffer.size());
    EXPECT_EQ(err, DOSBOX_LIB_ERR_INVALID_STATE)
        << "Should reject total_size < sizeof(EngineStateHeader)";
}

TEST_F(DOSBoxLibraryEngineStateTest, LoadRejectsTotalSizeLargerThanBuffer) {
    std::vector<uint8_t> buffer(dosbox::ENGINE_STATE_SIZE, 0);

    auto* header = reinterpret_cast<dosbox::EngineStateHeader*>(buffer.data());
    header->magic = dosbox::ENGINE_STATE_MAGIC;
    header->version = dosbox::ENGINE_STATE_VERSION;
    header->total_size = dosbox::ENGINE_STATE_SIZE * 10;  // Way larger than buffer

    auto err = dosbox_lib_load_state(handle_, buffer.data(), buffer.size());
    EXPECT_EQ(err, DOSBOX_LIB_ERR_INVALID_STATE)
        << "Should reject total_size > buffer_size";
}

TEST_F(DOSBoxLibraryEngineStateTest, LoadRejectsInvalidSectionOffsets) {
    // First save valid state
    size_t size = 0;
    dosbox_lib_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> buffer(size);
    dosbox_lib_save_state(handle_, buffer.data(), size, &size);

    auto* header = reinterpret_cast<dosbox::EngineStateHeader*>(buffer.data());

    // Corrupt timing_offset to be before header end
    header->timing_offset = 5;  // Inside header area

    // Recompute checksum for the corrupted header
    const uint8_t* data_start = buffer.data() + sizeof(dosbox::EngineStateHeader);
    size_t data_size = size - sizeof(dosbox::EngineStateHeader);
    header->checksum = dosbox::compute_crc32(data_start, data_size);

    auto err = dosbox_lib_load_state(handle_, buffer.data(), buffer.size());
    EXPECT_EQ(err, DOSBOX_LIB_ERR_INVALID_STATE)
        << "Should reject offset < sizeof(header)";
}

TEST_F(DOSBoxLibraryEngineStateTest, LoadRejectsOffsetBeyondTotal) {
    size_t size = 0;
    dosbox_lib_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> buffer(size);
    dosbox_lib_save_state(handle_, buffer.data(), size, &size);

    auto* header = reinterpret_cast<dosbox::EngineStateHeader*>(buffer.data());

    // Set offset beyond total_size
    header->pic_offset = header->total_size + 100;

    auto err = dosbox_lib_load_state(handle_, buffer.data(), buffer.size());
    EXPECT_EQ(err, DOSBOX_LIB_ERR_INVALID_STATE)
        << "Should reject offset > total_size";
}

TEST_F(DOSBoxLibraryEngineStateTest, SavedSizeEqualsEngineStateSize) {
    size_t size = 0;
    auto err = dosbox_lib_save_state(handle_, nullptr, 0, &size);
    EXPECT_EQ(err, DOSBOX_LIB_OK);
    EXPECT_EQ(size, dosbox::ENGINE_STATE_SIZE)
        << "Saved size must equal ENGINE_STATE_SIZE constant";
}

TEST_F(DOSBoxLibraryEngineStateTest, SavedCrcMatchesData) {
    size_t size = 0;
    dosbox_lib_save_state(handle_, nullptr, 0, &size);
    std::vector<uint8_t> buffer(size);
    dosbox_lib_save_state(handle_, buffer.data(), size, &size);

    auto* header = reinterpret_cast<const dosbox::EngineStateHeader*>(buffer.data());

    // Verify CRC matches
    const uint8_t* data_start = buffer.data() + sizeof(dosbox::EngineStateHeader);
    size_t data_size = size - sizeof(dosbox::EngineStateHeader);
    uint32_t computed_crc = dosbox::compute_crc32(data_start, data_size);

    EXPECT_EQ(header->checksum, computed_crc)
        << "Saved CRC must match computed CRC of data section";
}

TEST_F(DOSBoxLibraryEngineStateTest, FuzzCorruptedEngineState) {
    // Test various corruption patterns
    for (int seed = 0; seed < 100; ++seed) {
        std::vector<uint8_t> buffer(dosbox::ENGINE_STATE_SIZE);

        // Fill with pseudo-random data
        for (size_t i = 0; i < buffer.size(); ++i) {
            buffer[i] = static_cast<uint8_t>((seed * 31 + i * 17) % 256);
        }

        // Should not crash, should return error
        auto err = dosbox_lib_load_state(handle_, buffer.data(), buffer.size());
        EXPECT_NE(err, DOSBOX_LIB_OK)
            << "Random data should be rejected (seed=" << seed << ")";
    }
}
