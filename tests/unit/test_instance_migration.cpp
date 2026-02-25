/**
 * @file test_instance_migration.cpp
 * @brief Sprint 2: Global-to-Instance Migration TDD Tests
 *
 * 33 tests across 8 groups verifying that all per-instance state
 * has been correctly migrated from file-scope globals into
 * struct legends_instance.
 */

#include <gtest/gtest.h>
#include "legends/legends_embed.h"
#include "internal/legends_instance.h"

#include <cstring>
#include <vector>

// ============================================================================
// Test Fixture: Manages instance lifecycle for each test
// ============================================================================

class InstanceMigrationTest : public ::testing::Test {
protected:
    legends_handle handle_ = nullptr;

    void SetUp() override {
        // Ensure clean state
        handle_ = nullptr;
    }

    void TearDown() override {
        if (handle_ != nullptr) {
            legends_destroy(handle_);
            handle_ = nullptr;
        }
    }

    legends_error_t create_default() {
        legends_config_t config{};
        config.struct_size = sizeof(legends_config_t);
        config.api_version = LEGENDS_API_VERSION;
        config.memory_kb = 640;
        config.cpu_cycles = 3000;
        config.deterministic = 1;
        return legends_create(&config, &handle_);
    }

    // Get the instance pointer from the handle (they're the same now)
    legends_instance* get_inst() const {
        return reinterpret_cast<legends_instance*>(handle_);
    }
};

// ============================================================================
// Group 0: Infrastructure — struct definitions and basic properties
// ============================================================================

TEST(LegendsInstanceStruct, DefaultConstructionZeroInitialized) {
    legends_instance inst;

    // Time state should be zero-initialized
    EXPECT_EQ(inst.time_state.total_cycles, 0u);
    EXPECT_EQ(inst.time_state.emu_time_us, 0u);
    EXPECT_EQ(inst.time_state.cycles_per_ms, 3000u);

    // Input state should be empty
    EXPECT_TRUE(inst.input_state.empty());
    EXPECT_EQ(inst.input_state.next_sequence, 0u);

    // Frame state defaults
    EXPECT_TRUE(inst.frame_state.is_text_mode);
    EXPECT_EQ(inst.frame_state.columns, 80);
    EXPECT_EQ(inst.frame_state.rows, 25);

    // Event queue should be empty
    EXPECT_EQ(inst.event_queue.event_count, 0u);

    // Engine handle should be null
    EXPECT_EQ(inst.engine_handle, nullptr);

    // Last error should be empty
    EXPECT_TRUE(inst.last_error.empty());

    // Log state should be null
    EXPECT_EQ(inst.log_state.callback, nullptr);
}

TEST(LegendsInstanceStruct, ResetClearsAllState) {
    legends_instance inst;

    // Dirty some state
    inst.time_state.total_cycles = 999999;
    inst.time_state.emu_time_us = 123456;
    inst.input_state.enqueue_key(0x1E, true, false);
    inst.frame_state.cursor_x = 42;
    inst.event_queue.event_count = 5;
    inst.last_error = "test error";
    inst.pics[0].irr = 0xFF;
    inst.dma[0].count = 1234;

    // Reset
    inst.reset_state();

    // Verify everything is clean
    EXPECT_EQ(inst.time_state.total_cycles, 0u);
    EXPECT_EQ(inst.time_state.emu_time_us, 0u);
    EXPECT_TRUE(inst.input_state.empty());
    EXPECT_EQ(inst.frame_state.cursor_x, 0);
    EXPECT_EQ(inst.event_queue.event_count, 0u);
    EXPECT_TRUE(inst.last_error.empty());
    EXPECT_EQ(inst.pics[0].irr, 0);
    EXPECT_EQ(inst.pics[0].imr, 255);  // Default IMR
    EXPECT_EQ(inst.dma[0].count, 0);
    EXPECT_EQ(inst.dma[0].masked, 1);  // Default masked
}

TEST(LegendsInstanceStruct, SizeOfIsReasonable) {
    // The struct should be larger than just a few pointers (it owns real state)
    // but shouldn't be absurdly large (no multi-MB embedded arrays beyond frame buffer)
    EXPECT_GT(sizeof(legends_instance), 1000u);

    // The FrameState has a 4000-element uint16_t array = 8KB
    // Plus InputState has a 320-element array
    // Total should be well under 100KB
    EXPECT_LT(sizeof(legends_instance), 100 * 1024u);
}

// ============================================================================
// Group 1: Lifecycle — handle is real pointer, create/destroy
// ============================================================================

TEST_F(InstanceMigrationTest, InstanceLifecycle_CreateReturnsRealPointer) {
    ASSERT_EQ(create_default(), LEGENDS_OK);

    // Handle should be non-null and NOT the old sentinel value (void*)1
    EXPECT_NE(handle_, nullptr);
    EXPECT_NE(reinterpret_cast<uintptr_t>(handle_), uintptr_t(1));

    // Handle should be a valid legends_instance*
    auto* inst = get_inst();
    EXPECT_NE(inst, nullptr);
}

TEST_F(InstanceMigrationTest, InstanceLifecycle_HandleStableAcrossCalls) {
    ASSERT_EQ(create_default(), LEGENDS_OK);
    legends_handle h1 = handle_;

    // Step and verify handle unchanged
    legends_step_result_t result{};
    ASSERT_EQ(legends_step_ms(handle_, 10, &result), LEGENDS_OK);
    EXPECT_EQ(handle_, h1);

    // Get config and verify handle unchanged
    legends_config_t config{};
    ASSERT_EQ(legends_get_config(handle_, &config), LEGENDS_OK);
    EXPECT_EQ(handle_, h1);
}

TEST_F(InstanceMigrationTest, InstanceLifecycle_DestroyNullsActiveInstance) {
    ASSERT_EQ(create_default(), LEGENDS_OK);
    legends_handle h = handle_;
    ASSERT_EQ(legends_destroy(h), LEGENDS_OK);
    handle_ = nullptr;  // Prevent TearDown from double-destroying

    // Creating a new instance should work (previous was fully cleaned up)
    ASSERT_EQ(create_default(), LEGENDS_OK);
    EXPECT_NE(handle_, nullptr);
}

TEST_F(InstanceMigrationTest, InstanceLifecycle_DoubleCreateReturnsAlreadyCreated) {
    ASSERT_EQ(create_default(), LEGENDS_OK);

    legends_handle second = nullptr;
    legends_config_t config{};
    config.struct_size = sizeof(legends_config_t);
    config.api_version = LEGENDS_API_VERSION;
    config.memory_kb = 640;
    config.cpu_cycles = 3000;
    config.deterministic = 1;

    EXPECT_EQ(legends_create(&config, &second), LEGENDS_ERR_ALREADY_CREATED);
    EXPECT_EQ(second, nullptr);
}

// ============================================================================
// Group 2: Operational State — config, error, logging per-instance
// ============================================================================

TEST_F(InstanceMigrationTest, InstanceConfig_StoredPerInstance) {
    legends_config_t config{};
    config.struct_size = sizeof(legends_config_t);
    config.api_version = LEGENDS_API_VERSION;
    config.memory_kb = 640;
    config.cpu_cycles = 5000;
    config.deterministic = 1;

    ASSERT_EQ(legends_create(&config, &handle_), LEGENDS_OK);

    legends_config_t retrieved{};
    ASSERT_EQ(legends_get_config(handle_, &retrieved), LEGENDS_OK);
    EXPECT_EQ(retrieved.cpu_cycles, 5000u);
    EXPECT_EQ(retrieved.memory_kb, 640u);
}

TEST_F(InstanceMigrationTest, InstanceError_PerInstanceStorage) {
    ASSERT_EQ(create_default(), LEGENDS_OK);

    // Trigger an error by passing a null pointer
    EXPECT_EQ(legends_get_emu_time(handle_, nullptr), LEGENDS_ERR_NULL_POINTER);

    // The error should be retrievable
    // (Note: LEGENDS_REQUIRE doesn't set last_error, so test with a different error)
    auto* inst = get_inst();
    inst->last_error = "test error message";

    char buf[256];
    size_t len = 0;
    ASSERT_EQ(legends_get_last_error(handle_, buf, sizeof(buf), &len), LEGENDS_OK);
    EXPECT_STREQ(buf, "test error message");
}

TEST_F(InstanceMigrationTest, InstanceLogging_CallbackPerInstance) {
    ASSERT_EQ(create_default(), LEGENDS_OK);

    static int log_count = 0;
    log_count = 0;

    auto callback = [](int level, const char* msg, void* userdata) {
        (void)level; (void)msg; (void)userdata;
        log_count++;
    };

    ASSERT_EQ(legends_set_log_callback(handle_, callback, nullptr), LEGENDS_OK);

    // Verify the callback is stored in the instance
    auto* inst = get_inst();
    EXPECT_NE(inst->log_state.callback, nullptr);
    EXPECT_GE(log_count, 1);  // Setting callback logs a message
}

TEST_F(InstanceMigrationTest, InstanceError_DoesNotLeakBetweenInstances) {
    // Create first instance and inject an error
    ASSERT_EQ(create_default(), LEGENDS_OK);
    auto* inst1 = get_inst();
    inst1->last_error = "error from instance 1";
    ASSERT_EQ(legends_destroy(handle_), LEGENDS_OK);
    handle_ = nullptr;

    // Create second instance
    ASSERT_EQ(create_default(), LEGENDS_OK);
    auto* inst2 = get_inst();

    // Second instance should have empty error
    EXPECT_TRUE(inst2->last_error.empty());
}

// ============================================================================
// Group 3: Engine Layer — MachineContext and engine handle per-instance
// ============================================================================

TEST_F(InstanceMigrationTest, InstanceEngine_MachineContextOwnedByInstance) {
    ASSERT_EQ(create_default(), LEGENDS_OK);
    auto* inst = get_inst();
    EXPECT_NE(inst->machine, nullptr);
}

TEST_F(InstanceMigrationTest, InstanceEngine_EngineHandleOwnedByInstance) {
    ASSERT_EQ(create_default(), LEGENDS_OK);
    auto* inst = get_inst();
    EXPECT_NE(inst->engine_handle, nullptr);
}

TEST_F(InstanceMigrationTest, InstanceEngine_DestroyReleasesEngine) {
    ASSERT_EQ(create_default(), LEGENDS_OK);
    ASSERT_EQ(legends_destroy(handle_), LEGENDS_OK);
    handle_ = nullptr;

    // If engine was leaked, creating a new instance would fail or crash
    ASSERT_EQ(create_default(), LEGENDS_OK);
    EXPECT_NE(get_inst()->engine_handle, nullptr);
}

TEST_F(InstanceMigrationTest, InstanceEngine_SteppingUsesInstanceEngine) {
    ASSERT_EQ(create_default(), LEGENDS_OK);

    legends_step_result_t result{};
    ASSERT_EQ(legends_step_cycles(handle_, 3000, &result), LEGENDS_OK);
    EXPECT_GT(result.cycles_executed, 0u);

    // Time state should be updated in the instance
    auto* inst = get_inst();
    EXPECT_GT(inst->time_state.total_cycles, 0u);
}

// ============================================================================
// Group 4: Timing — time state per-instance
// ============================================================================

TEST_F(InstanceMigrationTest, InstanceTime_IsolatedBetweenInstances) {
    // Create and step instance A
    ASSERT_EQ(create_default(), LEGENDS_OK);
    ASSERT_EQ(legends_step_ms(handle_, 100, nullptr), LEGENDS_OK);

    uint64_t time_a = 0;
    ASSERT_EQ(legends_get_emu_time(handle_, &time_a), LEGENDS_OK);
    EXPECT_GT(time_a, 0u);

    ASSERT_EQ(legends_destroy(handle_), LEGENDS_OK);
    handle_ = nullptr;

    // Create instance B — should start at 0
    ASSERT_EQ(create_default(), LEGENDS_OK);
    uint64_t time_b = 0;
    ASSERT_EQ(legends_get_emu_time(handle_, &time_b), LEGENDS_OK);
    EXPECT_EQ(time_b, 0u);
}

TEST_F(InstanceMigrationTest, InstanceTime_SaveLoadPreservesState) {
    ASSERT_EQ(create_default(), LEGENDS_OK);
    ASSERT_EQ(legends_step_ms(handle_, 50, nullptr), LEGENDS_OK);

    uint64_t time_before = 0;
    ASSERT_EQ(legends_get_emu_time(handle_, &time_before), LEGENDS_OK);

    // Save
    size_t save_size = 0;
    ASSERT_EQ(legends_save_state(handle_, nullptr, 0, &save_size), LEGENDS_OK);
    std::vector<uint8_t> buf(save_size);
    ASSERT_EQ(legends_save_state(handle_, buf.data(), buf.size(), &save_size), LEGENDS_OK);

    // Step more
    ASSERT_EQ(legends_step_ms(handle_, 50, nullptr), LEGENDS_OK);

    // Load
    ASSERT_EQ(legends_load_state(handle_, buf.data(), save_size), LEGENDS_OK);

    uint64_t time_after = 0;
    ASSERT_EQ(legends_get_emu_time(handle_, &time_after), LEGENDS_OK);
    EXPECT_EQ(time_after, time_before);
}

TEST_F(InstanceMigrationTest, InstanceTime_HashDeterministic) {
    ASSERT_EQ(create_default(), LEGENDS_OK);
    ASSERT_EQ(legends_step_ms(handle_, 10, nullptr), LEGENDS_OK);

    uint8_t hash1[32], hash2[32];
    ASSERT_EQ(legends_get_state_hash(handle_, hash1), LEGENDS_OK);
    ASSERT_EQ(legends_get_state_hash(handle_, hash2), LEGENDS_OK);

    EXPECT_EQ(std::memcmp(hash1, hash2, 32), 0);
}

// ============================================================================
// Group 5: Input — input queue per-instance
// ============================================================================

TEST_F(InstanceMigrationTest, InstanceInput_QueueIsolatedBetweenInstances) {
    // Create instance A and inject keys
    ASSERT_EQ(create_default(), LEGENDS_OK);
    ASSERT_EQ(legends_key_event(handle_, 0x1E, 1), LEGENDS_OK);  // 'a' down
    ASSERT_EQ(legends_key_event(handle_, 0x1E, 0), LEGENDS_OK);  // 'a' up

    auto* inst_a = get_inst();
    EXPECT_FALSE(inst_a->input_state.empty());

    ASSERT_EQ(legends_destroy(handle_), LEGENDS_OK);
    handle_ = nullptr;

    // Create instance B — queue should be empty
    ASSERT_EQ(create_default(), LEGENDS_OK);
    auto* inst_b = get_inst();
    EXPECT_TRUE(inst_b->input_state.empty());
}

TEST_F(InstanceMigrationTest, InstanceInput_SequenceCounterResets) {
    // Create instance A and inject events
    ASSERT_EQ(create_default(), LEGENDS_OK);
    for (int i = 0; i < 10; i++) {
        ASSERT_EQ(legends_key_event(handle_, 0x1E, 1), LEGENDS_OK);
        ASSERT_EQ(legends_key_event(handle_, 0x1E, 0), LEGENDS_OK);
    }
    auto* inst_a = get_inst();
    EXPECT_EQ(inst_a->input_state.next_sequence, 20u);

    ASSERT_EQ(legends_destroy(handle_), LEGENDS_OK);
    handle_ = nullptr;

    // Create instance B — sequence should restart
    ASSERT_EQ(create_default(), LEGENDS_OK);
    auto* inst_b = get_inst();
    EXPECT_EQ(inst_b->input_state.next_sequence, 0u);
}

TEST_F(InstanceMigrationTest, InstanceInput_SaveLoadPreservesQueue) {
    ASSERT_EQ(create_default(), LEGENDS_OK);

    // Inject some events
    ASSERT_EQ(legends_key_event(handle_, 0x1E, 1), LEGENDS_OK);
    ASSERT_EQ(legends_mouse_event(handle_, 10, -5, 1), LEGENDS_OK);

    auto* inst = get_inst();
    size_t queue_size_before = inst->input_state.size();

    // Save
    size_t save_size = 0;
    ASSERT_EQ(legends_save_state(handle_, nullptr, 0, &save_size), LEGENDS_OK);
    std::vector<uint8_t> buf(save_size);
    ASSERT_EQ(legends_save_state(handle_, buf.data(), buf.size(), &save_size), LEGENDS_OK);

    // Drain queue by stepping
    ASSERT_EQ(legends_step_ms(handle_, 10, nullptr), LEGENDS_OK);

    // Load
    ASSERT_EQ(legends_load_state(handle_, buf.data(), save_size), LEGENDS_OK);

    EXPECT_EQ(inst->input_state.size(), queue_size_before);
}

TEST_F(InstanceMigrationTest, InstanceInput_DrainUsesInstanceQueue) {
    ASSERT_EQ(create_default(), LEGENDS_OK);

    ASSERT_EQ(legends_key_event(handle_, 0x1E, 1), LEGENDS_OK);
    ASSERT_EQ(legends_key_event(handle_, 0x1E, 0), LEGENDS_OK);

    auto* inst = get_inst();
    EXPECT_EQ(inst->input_state.size(), 2u);

    // Step drains the queue
    ASSERT_EQ(legends_step_ms(handle_, 1, nullptr), LEGENDS_OK);
    EXPECT_EQ(inst->input_state.size(), 0u);
}

// ============================================================================
// Group 6: Hardware — PIC, DMA, event queue per-instance
// ============================================================================

TEST_F(InstanceMigrationTest, InstanceHardware_PICIsolatedBetweenInstances) {
    ASSERT_EQ(create_default(), LEGENDS_OK);
    auto* inst = get_inst();

    // Modify PIC state via stepping
    ASSERT_EQ(legends_step_ms(handle_, 10, nullptr), LEGENDS_OK);
    auto master_irr = inst->pics[0].irr;

    ASSERT_EQ(legends_destroy(handle_), LEGENDS_OK);
    handle_ = nullptr;

    // New instance should have default PIC state
    ASSERT_EQ(create_default(), LEGENDS_OK);
    inst = get_inst();
    EXPECT_EQ(inst->pics[0].imr, 255);  // Default: all masked
    EXPECT_EQ(inst->pics[0].vector_base, 8);
    EXPECT_EQ(inst->pics[1].vector_base, 112);
    (void)master_irr;
}

TEST_F(InstanceMigrationTest, InstanceHardware_DMAIsolatedBetweenInstances) {
    ASSERT_EQ(create_default(), LEGENDS_OK);
    auto* inst = get_inst();

    // Verify initial DMA state
    for (int i = 0; i < 8; i++) {
        EXPECT_EQ(inst->dma[i].count, 0);
        EXPECT_EQ(inst->dma[i].masked, 1);  // Default: masked
    }

    ASSERT_EQ(legends_destroy(handle_), LEGENDS_OK);
    handle_ = nullptr;

    ASSERT_EQ(create_default(), LEGENDS_OK);
    inst = get_inst();
    for (int i = 0; i < 8; i++) {
        EXPECT_EQ(inst->dma[i].masked, 1);
    }
}

TEST_F(InstanceMigrationTest, InstanceHardware_EventQueueIsolatedBetweenInstances) {
    ASSERT_EQ(create_default(), LEGENDS_OK);
    ASSERT_EQ(legends_step_ms(handle_, 10, nullptr), LEGENDS_OK);

    ASSERT_EQ(legends_destroy(handle_), LEGENDS_OK);
    handle_ = nullptr;

    ASSERT_EQ(create_default(), LEGENDS_OK);
    auto* inst = get_inst();
    EXPECT_EQ(inst->event_queue.event_count, 0u);
    EXPECT_EQ(inst->event_queue.next_event_id, 0u);
}

TEST_F(InstanceMigrationTest, InstanceHardware_SaveLoadPreservesState) {
    ASSERT_EQ(create_default(), LEGENDS_OK);
    ASSERT_EQ(legends_step_ms(handle_, 10, nullptr), LEGENDS_OK);

    auto* inst = get_inst();
    auto saved_pics = inst->pics;

    // Save
    size_t save_size = 0;
    ASSERT_EQ(legends_save_state(handle_, nullptr, 0, &save_size), LEGENDS_OK);
    std::vector<uint8_t> buf(save_size);
    ASSERT_EQ(legends_save_state(handle_, buf.data(), buf.size(), &save_size), LEGENDS_OK);

    // Step to change state
    ASSERT_EQ(legends_step_ms(handle_, 100, nullptr), LEGENDS_OK);

    // Load
    ASSERT_EQ(legends_load_state(handle_, buf.data(), save_size), LEGENDS_OK);

    // PIC state should match saved
    EXPECT_EQ(std::memcmp(&inst->pics, &saved_pics, sizeof(saved_pics)), 0);
}

TEST_F(InstanceMigrationTest, InstanceHardware_HashIncludesHardware) {
    ASSERT_EQ(create_default(), LEGENDS_OK);

    // Get hash at initial state
    uint8_t hash_initial[32];
    ASSERT_EQ(legends_get_state_hash(handle_, hash_initial), LEGENDS_OK);

    // Step to change hardware state
    ASSERT_EQ(legends_step_ms(handle_, 50, nullptr), LEGENDS_OK);

    uint8_t hash_after[32];
    ASSERT_EQ(legends_get_state_hash(handle_, hash_after), LEGENDS_OK);

    // Hashes should differ (state changed)
    EXPECT_NE(std::memcmp(hash_initial, hash_after, 32), 0);
}

// ============================================================================
// Group 7: Frame — video state per-instance
// ============================================================================

TEST_F(InstanceMigrationTest, InstanceFrame_IsolatedBetweenInstances) {
    ASSERT_EQ(create_default(), LEGENDS_OK);
    auto* inst = get_inst();

    // Modify frame state
    inst->frame_state.cursor_x = 42;
    inst->frame_state.cursor_y = 13;

    ASSERT_EQ(legends_destroy(handle_), LEGENDS_OK);
    handle_ = nullptr;

    // New instance should have default frame state (cursor at origin)
    ASSERT_EQ(create_default(), LEGENDS_OK);
    inst = get_inst();
    EXPECT_EQ(inst->frame_state.cursor_x, 0);
    EXPECT_EQ(inst->frame_state.cursor_y, 0);
}

TEST_F(InstanceMigrationTest, InstanceFrame_TextCaptureUsesInstance) {
    ASSERT_EQ(create_default(), LEGENDS_OK);

    size_t count = 0;
    legends_text_info_t info{};
    ASSERT_EQ(legends_capture_text(handle_, nullptr, 0, &count, &info), LEGENDS_OK);
    EXPECT_EQ(count, 80u * 25u);
    EXPECT_EQ(info.columns, 80);
    EXPECT_EQ(info.rows, 25);
}

TEST_F(InstanceMigrationTest, InstanceFrame_RGBCaptureUsesInstance) {
    ASSERT_EQ(create_default(), LEGENDS_OK);

    size_t size = 0;
    uint16_t width = 0, height = 0;
    ASSERT_EQ(legends_capture_rgb(handle_, nullptr, 0, &size, &width, &height), LEGENDS_OK);
    EXPECT_EQ(width, 80 * 8);    // Text mode: 8 pixels per char
    EXPECT_EQ(height, 25 * 16);  // Text mode: 16 pixels per char
}

TEST_F(InstanceMigrationTest, InstanceFrame_DirtyTrackingPerInstance) {
    ASSERT_EQ(create_default(), LEGENDS_OK);

    int dirty = 0;
    ASSERT_EQ(legends_is_frame_dirty(handle_, &dirty), LEGENDS_OK);
    EXPECT_EQ(dirty, 1);  // Dirty after creation

    // Capture clears dirty flag
    size_t count = 0;
    std::vector<legends_text_cell_t> cells(80 * 25);
    ASSERT_EQ(legends_capture_text(handle_, cells.data(), cells.size(), &count, nullptr), LEGENDS_OK);

    ASSERT_EQ(legends_is_frame_dirty(handle_, &dirty), LEGENDS_OK);
    EXPECT_EQ(dirty, 0);

    // Input makes it dirty again
    ASSERT_EQ(legends_key_event(handle_, 0x1E, 1), LEGENDS_OK);
    ASSERT_EQ(legends_is_frame_dirty(handle_, &dirty), LEGENDS_OK);
    EXPECT_EQ(dirty, 1);
}

TEST_F(InstanceMigrationTest, InstanceFrame_CursorPositionPerInstance) {
    ASSERT_EQ(create_default(), LEGENDS_OK);

    uint8_t x = 0, y = 0;
    int visible = 0;
    ASSERT_EQ(legends_get_cursor(handle_, &x, &y, &visible), LEGENDS_OK);

    // Default state: cursor at origin
    EXPECT_EQ(x, 0);
    EXPECT_EQ(y, 0);
}

TEST_F(InstanceMigrationTest, InstanceFrame_SaveLoadPreservesState) {
    ASSERT_EQ(create_default(), LEGENDS_OK);

    auto* inst = get_inst();
    inst->frame_state.cursor_x = 30;
    inst->frame_state.cursor_y = 10;

    // Save
    size_t save_size = 0;
    ASSERT_EQ(legends_save_state(handle_, nullptr, 0, &save_size), LEGENDS_OK);
    std::vector<uint8_t> buf(save_size);
    ASSERT_EQ(legends_save_state(handle_, buf.data(), buf.size(), &save_size), LEGENDS_OK);

    // Change state
    inst->frame_state.cursor_x = 0;
    inst->frame_state.cursor_y = 0;

    // Load
    ASSERT_EQ(legends_load_state(handle_, buf.data(), save_size), LEGENDS_OK);

    EXPECT_EQ(inst->frame_state.cursor_x, 30);
    EXPECT_EQ(inst->frame_state.cursor_y, 10);
}
