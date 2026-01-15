/**
 * @file test_dosbox_instance_handle.cpp
 * @brief Unit tests for DOSBox instance handle system.
 *
 * Tests PR #8 requirements:
 * - State machine: Created → Initialized → Running → Shutdown → Destroyed
 * - Return explicit errors for: null handle, double destroy, wrong state
 */

#include <gtest/gtest.h>
#include "dosbox/instance_handle.h"

#include <thread>
#include <vector>

using namespace dosbox;

// ═══════════════════════════════════════════════════════════════════════════════
// Instance Handle Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(InstanceHandleTest, CreateHandle) {
    auto handle = InstanceHandle::create(42, 7);

    EXPECT_EQ(handle.slot(), 42u);
    EXPECT_EQ(handle.generation(), 7u);
}

TEST(InstanceHandleTest, NullHandle) {
    InstanceHandle null{0};
    EXPECT_TRUE(null.is_null());

    auto non_null = InstanceHandle::create(1, 1);
    EXPECT_FALSE(non_null.is_null());
}

TEST(InstanceHandleTest, OpaqueRoundtrip) {
    auto original = InstanceHandle::create(12345, 678);

    void* opaque = original.to_opaque();
    auto recovered = InstanceHandle::from_opaque(opaque);

    EXPECT_EQ(original, recovered);
    EXPECT_EQ(recovered.slot(), 12345u);
    EXPECT_EQ(recovered.generation(), 678u);
}

// ═══════════════════════════════════════════════════════════════════════════════
// State Machine Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(InstanceStateTest, ValidTransitions) {
    // Created can go to Initialized or Failed
    EXPECT_TRUE(is_valid_transition(InstanceState::Created, InstanceState::Initialized));
    EXPECT_TRUE(is_valid_transition(InstanceState::Created, InstanceState::Failed));
    EXPECT_FALSE(is_valid_transition(InstanceState::Created, InstanceState::Running));

    // Initialized can go to Running, Shutdown, or Failed
    EXPECT_TRUE(is_valid_transition(InstanceState::Initialized, InstanceState::Running));
    EXPECT_TRUE(is_valid_transition(InstanceState::Initialized, InstanceState::Shutdown));
    EXPECT_TRUE(is_valid_transition(InstanceState::Initialized, InstanceState::Failed));

    // Running can go to Paused, Shutdown, or Failed
    EXPECT_TRUE(is_valid_transition(InstanceState::Running, InstanceState::Paused));
    EXPECT_TRUE(is_valid_transition(InstanceState::Running, InstanceState::Shutdown));
    EXPECT_TRUE(is_valid_transition(InstanceState::Running, InstanceState::Failed));
    EXPECT_FALSE(is_valid_transition(InstanceState::Running, InstanceState::Created));

    // Paused can go to Running, Shutdown, or Failed
    EXPECT_TRUE(is_valid_transition(InstanceState::Paused, InstanceState::Running));
    EXPECT_TRUE(is_valid_transition(InstanceState::Paused, InstanceState::Shutdown));
    EXPECT_TRUE(is_valid_transition(InstanceState::Paused, InstanceState::Failed));

    // Shutdown can only go to Invalid (destroy)
    EXPECT_TRUE(is_valid_transition(InstanceState::Shutdown, InstanceState::Invalid));
    EXPECT_FALSE(is_valid_transition(InstanceState::Shutdown, InstanceState::Running));

    // Failed can go to Shutdown or Invalid
    EXPECT_TRUE(is_valid_transition(InstanceState::Failed, InstanceState::Shutdown));
    EXPECT_TRUE(is_valid_transition(InstanceState::Failed, InstanceState::Invalid));

    // Invalid cannot transition to anything
    EXPECT_FALSE(is_valid_transition(InstanceState::Invalid, InstanceState::Created));
}

TEST(InstanceStateTest, ToString) {
    EXPECT_STREQ(to_string(InstanceState::Invalid), "Invalid");
    EXPECT_STREQ(to_string(InstanceState::Created), "Created");
    EXPECT_STREQ(to_string(InstanceState::Initialized), "Initialized");
    EXPECT_STREQ(to_string(InstanceState::Running), "Running");
    EXPECT_STREQ(to_string(InstanceState::Paused), "Paused");
    EXPECT_STREQ(to_string(InstanceState::Shutdown), "Shutdown");
    EXPECT_STREQ(to_string(InstanceState::Failed), "Failed");
}

// ═══════════════════════════════════════════════════════════════════════════════
// Handle Error Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(HandleErrorTest, ToString) {
    EXPECT_STREQ(to_string(HandleError::Ok), "Ok");
    EXPECT_STREQ(to_string(HandleError::Null), "Null");
    EXPECT_STREQ(to_string(HandleError::InvalidGeneration), "InvalidGeneration");
    EXPECT_STREQ(to_string(HandleError::Destroyed), "Destroyed");
    EXPECT_STREQ(to_string(HandleError::WrongState), "WrongState");
    EXPECT_STREQ(to_string(HandleError::DoubleDestroy), "DoubleDestroy");
}

// ═══════════════════════════════════════════════════════════════════════════════
// Instance Registry Tests
// ═══════════════════════════════════════════════════════════════════════════════

class InstanceRegistryTest : public ::testing::Test {
protected:
    InstanceRegistry registry;
    int test_context = 42;
};

TEST_F(InstanceRegistryTest, AllocateAndValidate) {
    auto result = registry.allocate(&test_context);
    ASSERT_TRUE(result.has_value());

    auto handle = result.value();
    EXPECT_FALSE(handle.is_null());
    EXPECT_EQ(registry.validate(handle), HandleError::Ok);
}

TEST_F(InstanceRegistryTest, InitialStateIsCreated) {
    auto result = registry.allocate();
    ASSERT_TRUE(result.has_value());

    auto state = registry.get_state(result.value());
    ASSERT_TRUE(state.has_value());
    EXPECT_EQ(state.value(), InstanceState::Created);
}

TEST_F(InstanceRegistryTest, ValidStateTransitions) {
    auto result = registry.allocate();
    ASSERT_TRUE(result.has_value());
    auto handle = result.value();

    // Created -> Initialized
    EXPECT_TRUE(registry.transition(handle, InstanceState::Initialized).has_value());
    EXPECT_EQ(registry.get_state(handle).value(), InstanceState::Initialized);

    // Initialized -> Running
    EXPECT_TRUE(registry.transition(handle, InstanceState::Running).has_value());
    EXPECT_EQ(registry.get_state(handle).value(), InstanceState::Running);

    // Running -> Paused
    EXPECT_TRUE(registry.transition(handle, InstanceState::Paused).has_value());
    EXPECT_EQ(registry.get_state(handle).value(), InstanceState::Paused);

    // Paused -> Running
    EXPECT_TRUE(registry.transition(handle, InstanceState::Running).has_value());
    EXPECT_EQ(registry.get_state(handle).value(), InstanceState::Running);

    // Running -> Shutdown
    EXPECT_TRUE(registry.transition(handle, InstanceState::Shutdown).has_value());
    EXPECT_EQ(registry.get_state(handle).value(), InstanceState::Shutdown);

    // Destroy (Shutdown -> Invalid)
    EXPECT_TRUE(registry.destroy(handle).has_value());
}

TEST_F(InstanceRegistryTest, InvalidStateTransition) {
    auto result = registry.allocate();
    ASSERT_TRUE(result.has_value());
    auto handle = result.value();

    // Created -> Running is invalid (must initialize first)
    auto transition_result = registry.transition(handle, InstanceState::Running);
    EXPECT_FALSE(transition_result.has_value());
}

TEST_F(InstanceRegistryTest, NullHandleRejected) {
    InstanceHandle null{0};

    EXPECT_EQ(registry.validate(null), HandleError::Null);
    EXPECT_FALSE(registry.get_state(null).has_value());
    EXPECT_FALSE(registry.destroy(null).has_value());
}

TEST_F(InstanceRegistryTest, DoubleDestroyDetected) {
    auto result = registry.allocate();
    ASSERT_TRUE(result.has_value());
    auto handle = result.value();

    // First destroy succeeds (Created state allows direct destroy)
    EXPECT_TRUE(registry.destroy(handle).has_value());

    // Second destroy fails
    auto destroy_result = registry.destroy(handle);
    EXPECT_FALSE(destroy_result.has_value());
}

TEST_F(InstanceRegistryTest, UseAfterFreeDetected) {
    auto result = registry.allocate();
    ASSERT_TRUE(result.has_value());
    auto handle = result.value();

    // Destroy the handle
    EXPECT_TRUE(registry.destroy(handle).has_value());

    // Old handle should be invalid
    auto error = registry.validate(handle);
    EXPECT_TRUE(error == HandleError::Destroyed || error == HandleError::InvalidGeneration);
}

TEST_F(InstanceRegistryTest, CannotDestroyWhileRunning) {
    auto result = registry.allocate();
    ASSERT_TRUE(result.has_value());
    auto handle = result.value();

    // Transition to Running
    registry.transition(handle, InstanceState::Initialized);
    registry.transition(handle, InstanceState::Running);

    // Cannot destroy while running
    auto destroy_result = registry.destroy(handle);
    EXPECT_FALSE(destroy_result.has_value());

    // Must shutdown first
    EXPECT_TRUE(registry.transition(handle, InstanceState::Shutdown).has_value());
    EXPECT_TRUE(registry.destroy(handle).has_value());
}

TEST_F(InstanceRegistryTest, RequireStateWorks) {
    auto result = registry.allocate();
    ASSERT_TRUE(result.has_value());
    auto handle = result.value();

    // Should be in Created state
    EXPECT_TRUE(registry.require_state(handle, InstanceState::Created).has_value());
    EXPECT_FALSE(registry.require_state(handle, InstanceState::Running).has_value());

    // Should accept multiple allowed states
    EXPECT_TRUE(registry.require_state(handle, InstanceState::Created, InstanceState::Initialized).has_value());
}

TEST_F(InstanceRegistryTest, ContextStorage) {
    auto result = registry.allocate(&test_context);
    ASSERT_TRUE(result.has_value());
    auto handle = result.value();

    // Get context
    auto ctx = registry.get_context(handle);
    ASSERT_TRUE(ctx.has_value());
    EXPECT_EQ(ctx.value(), &test_context);

    // Set different context
    int other_context = 99;
    EXPECT_TRUE(registry.set_context(handle, &other_context).has_value());

    ctx = registry.get_context(handle);
    EXPECT_EQ(ctx.value(), &other_context);

    // Cleanup
    registry.destroy(handle);
}

TEST_F(InstanceRegistryTest, ActiveCount) {
    EXPECT_EQ(registry.active_count(), 0u);

    auto h1 = registry.allocate();
    EXPECT_EQ(registry.active_count(), 1u);

    auto h2 = registry.allocate();
    EXPECT_EQ(registry.active_count(), 2u);

    registry.destroy(h1.value());
    EXPECT_EQ(registry.active_count(), 1u);

    registry.destroy(h2.value());
    EXPECT_EQ(registry.active_count(), 0u);
}

TEST_F(InstanceRegistryTest, SlotReuse) {
    auto h1 = registry.allocate();
    ASSERT_TRUE(h1.has_value());
    uint32_t first_slot = h1.value().slot();
    uint32_t first_gen = h1.value().generation();

    registry.destroy(h1.value());

    // Allocate again - may reuse same slot
    auto h2 = registry.allocate();
    ASSERT_TRUE(h2.has_value());

    if (h2.value().slot() == first_slot) {
        // If same slot, generation must be different
        EXPECT_NE(h2.value().generation(), first_gen);
    }

    registry.destroy(h2.value());
}

// ═══════════════════════════════════════════════════════════════════════════════
// Thread Safety Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(InstanceRegistryTest, ConcurrentAllocations) {
    std::vector<std::thread> threads;
    std::vector<InstanceHandle> handles;
    std::mutex handles_mutex;

    // Allocate from multiple threads
    for (int i = 0; i < 4; ++i) {
        threads.emplace_back([this, &handles, &handles_mutex]() {
            for (int j = 0; j < 20; ++j) {
                auto result = registry.allocate();
                if (result.has_value()) {
                    std::lock_guard lock(handles_mutex);
                    handles.push_back(result.value());
                }
            }
        });
    }

    for (auto& t : threads) {
        t.join();
    }

    // All handles should be valid
    for (const auto& h : handles) {
        EXPECT_EQ(registry.validate(h), HandleError::Ok);
    }

    // Count should match
    EXPECT_EQ(registry.active_count(), handles.size());

    // Clean up
    for (const auto& h : handles) {
        registry.destroy(h);
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// C API Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(InstanceHandleCApiTest, ErrorStrings) {
    EXPECT_STREQ(dosbox_handle_error_str(DOSBOX_HANDLE_OK), "Ok");
    EXPECT_STREQ(dosbox_handle_error_str(DOSBOX_HANDLE_NULL), "Handle is null");
    EXPECT_STREQ(dosbox_handle_error_str(DOSBOX_HANDLE_DOUBLE_DESTROY),
                 "Handle already destroyed");
}

TEST(InstanceHandleCApiTest, StateStrings) {
    EXPECT_STREQ(dosbox_instance_state_str(DOSBOX_STATE_INVALID), "Invalid");
    EXPECT_STREQ(dosbox_instance_state_str(DOSBOX_STATE_CREATED), "Created");
    EXPECT_STREQ(dosbox_instance_state_str(DOSBOX_STATE_RUNNING), "Running");
}

TEST(InstanceHandleCApiTest, ValidateNullHandle) {
    dosbox_handle_error error = dosbox_validate_handle(nullptr);
    EXPECT_EQ(error, DOSBOX_HANDLE_NULL);
}

TEST(InstanceHandleCApiTest, GetStateNullHandle) {
    dosbox_instance_state state = dosbox_get_state(nullptr);
    EXPECT_EQ(state, DOSBOX_STATE_INVALID);
}

TEST(InstanceHandleCApiTest, ValidTransitionCheck) {
    EXPECT_EQ(dosbox_is_valid_transition(DOSBOX_STATE_CREATED, DOSBOX_STATE_INITIALIZED), 1);
    EXPECT_EQ(dosbox_is_valid_transition(DOSBOX_STATE_CREATED, DOSBOX_STATE_RUNNING), 0);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Full Lifecycle Test
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(InstanceRegistryTest, FullLifecycle) {
    // Create
    auto create_result = registry.allocate();
    ASSERT_TRUE(create_result.has_value());
    auto handle = create_result.value();
    EXPECT_EQ(registry.get_state(handle).value(), InstanceState::Created);

    // Initialize
    EXPECT_TRUE(registry.transition(handle, InstanceState::Initialized).has_value());
    EXPECT_EQ(registry.get_state(handle).value(), InstanceState::Initialized);

    // Run
    EXPECT_TRUE(registry.transition(handle, InstanceState::Running).has_value());
    EXPECT_EQ(registry.get_state(handle).value(), InstanceState::Running);

    // Pause
    EXPECT_TRUE(registry.transition(handle, InstanceState::Paused).has_value());
    EXPECT_EQ(registry.get_state(handle).value(), InstanceState::Paused);

    // Resume
    EXPECT_TRUE(registry.transition(handle, InstanceState::Running).has_value());
    EXPECT_EQ(registry.get_state(handle).value(), InstanceState::Running);

    // Shutdown
    EXPECT_TRUE(registry.transition(handle, InstanceState::Shutdown).has_value());
    EXPECT_EQ(registry.get_state(handle).value(), InstanceState::Shutdown);

    // Destroy
    EXPECT_TRUE(registry.destroy(handle).has_value());
    EXPECT_EQ(registry.validate(handle), HandleError::Destroyed);
}

TEST_F(InstanceRegistryTest, FailedStateRecovery) {
    auto result = registry.allocate();
    ASSERT_TRUE(result.has_value());
    auto handle = result.value();

    // Initialize
    registry.transition(handle, InstanceState::Initialized);

    // Simulate failure
    EXPECT_TRUE(registry.transition(handle, InstanceState::Failed).has_value());
    EXPECT_EQ(registry.get_state(handle).value(), InstanceState::Failed);

    // Failed state can be destroyed directly
    EXPECT_TRUE(registry.destroy(handle).has_value());
}
