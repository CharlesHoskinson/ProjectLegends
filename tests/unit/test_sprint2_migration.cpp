/**
 * @file test_sprint2_migration.cpp
 * @brief Sprint 2 — Global-to-Context Migration Wiring Tests (TDD)
 *
 * These tests verify that the 17 remaining globals are properly wired
 * to DOSBoxContext subsystem structs. They test observable behavior
 * through the public legends API, ensuring:
 *
 * 1. Sequential instances have independent state (no global leaks)
 * 2. State hashing is deterministic after migration
 * 3. Save/load round-trips preserve migrated state
 * 4. Stepping produces consistent results across instances
 *
 * Written BEFORE implementation per TDD methodology.
 * Initial expectation: some tests may fail until migration is complete.
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include <cstring>
#include <vector>
#include <array>

// ═══════════════════════════════════════════════════════════════════════════════
// Test Fixture: Manages legends instance lifecycle
// ═══════════════════════════════════════════════════════════════════════════════

class Sprint2MigrationTest : public ::testing::Test {
protected:
    void SetUp() override {
        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.deterministic = 1;
        auto err = legends_create(&config, &handle_);
        ASSERT_EQ(err, LEGENDS_OK) << "Failed to create legends instance";
    }

    void TearDown() override {
        if (handle_) {
            legends_destroy(handle_);
            handle_ = nullptr;
        }
    }

    legends_handle handle_ = nullptr;
};

// ═══════════════════════════════════════════════════════════════════════════════
// Sequential Instance Independence (Core Multi-Instance Readiness)
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * TEST: Sequential instances with identical config produce identical state hash.
 *
 * If any global leaks between instances, the hashes will diverge.
 * This is the fundamental test for global-to-context migration correctness.
 */
TEST(Sprint2SequentialIndependence, IdenticalConfigIdenticalHash) {
    std::array<uint8_t, 32> hash_a{}, hash_b{};

    // Instance A: create, step, hash, destroy
    {
        legends_handle a = nullptr;
        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.deterministic = 1;
        ASSERT_EQ(legends_create(&config, &a), LEGENDS_OK);
        ASSERT_EQ(legends_step_cycles(a, 10000, nullptr), LEGENDS_OK);
        ASSERT_EQ(legends_get_state_hash(a, hash_a.data()), LEGENDS_OK);
        legends_destroy(a);
    }

    // Instance B: create, step same amount, hash, destroy
    {
        legends_handle b = nullptr;
        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.deterministic = 1;
        ASSERT_EQ(legends_create(&config, &b), LEGENDS_OK);
        ASSERT_EQ(legends_step_cycles(b, 10000, nullptr), LEGENDS_OK);
        ASSERT_EQ(legends_get_state_hash(b, hash_b.data()), LEGENDS_OK);
        legends_destroy(b);
    }

    EXPECT_EQ(hash_a, hash_b)
        << "Sequential instances with identical config/input must produce "
           "identical state hash. If this fails, a global is leaking state "
           "between instances.";
}

/**
 * TEST: Instance state doesn't leak after stepping different amounts.
 *
 * Step A for 50k cycles, destroy. Create B, step B for 10k cycles.
 * B's hash must match a fresh instance stepped 10k cycles.
 */
TEST(Sprint2SequentialIndependence, NoStateLeakAfterDifferentStepping) {
    std::array<uint8_t, 32> hash_fresh{}, hash_after_heavy{};

    // First: get fresh baseline hash (10k cycles)
    {
        legends_handle fresh = nullptr;
        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.deterministic = 1;
        ASSERT_EQ(legends_create(&config, &fresh), LEGENDS_OK);
        ASSERT_EQ(legends_step_cycles(fresh, 10000, nullptr), LEGENDS_OK);
        ASSERT_EQ(legends_get_state_hash(fresh, hash_fresh.data()), LEGENDS_OK);
        legends_destroy(fresh);
    }

    // Heavy usage: step for 50k cycles, do input, capture, save/load
    {
        legends_handle heavy = nullptr;
        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.deterministic = 1;
        ASSERT_EQ(legends_create(&config, &heavy), LEGENDS_OK);
        ASSERT_EQ(legends_step_cycles(heavy, 50000, nullptr), LEGENDS_OK);

        // Exercise input subsystem
        legends_key_event(heavy, 0x1C, 1);  // Enter press
        legends_key_event(heavy, 0x1C, 0);  // Enter release
        legends_step_cycles(heavy, 5000, nullptr);

        // Exercise save/load
        size_t state_size = 0;
        legends_save_state(heavy, nullptr, 0, &state_size);
        std::vector<uint8_t> state_buf(state_size);
        legends_save_state(heavy, state_buf.data(), state_buf.size(), &state_size);

        legends_destroy(heavy);
    }

    // After heavy: create new instance, step 10k, hash
    {
        legends_handle after = nullptr;
        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.deterministic = 1;
        ASSERT_EQ(legends_create(&config, &after), LEGENDS_OK);
        ASSERT_EQ(legends_step_cycles(after, 10000, nullptr), LEGENDS_OK);
        ASSERT_EQ(legends_get_state_hash(after, hash_after_heavy.data()), LEGENDS_OK);
        legends_destroy(after);
    }

    EXPECT_EQ(hash_fresh, hash_after_heavy)
        << "Instance created after heavy usage must produce same hash as "
           "fresh instance. A global is retaining state from previous instance.";
}

// ═══════════════════════════════════════════════════════════════════════════════
// Save/Load Round-Trip Preserves Migrated State
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * TEST: Save state, destroy, create new instance, load state, verify hash.
 *
 * This tests that ALL migrated state is properly serialized and deserialized,
 * including memory, DMA, DOS, PIC, VGA, keyboard, etc.
 */
TEST_F(Sprint2MigrationTest, SaveLoadRoundTripAcrossInstances) {
    // Step to build up state
    ASSERT_EQ(legends_step_cycles(handle_, 20000, nullptr), LEGENDS_OK);

    // Inject some input to exercise input state
    legends_key_event(handle_, 0x1E, 1);  // 'A' press
    legends_key_event(handle_, 0x1E, 0);  // 'A' release
    ASSERT_EQ(legends_step_cycles(handle_, 5000, nullptr), LEGENDS_OK);

    // Get hash before save
    std::array<uint8_t, 32> hash_before{};
    ASSERT_EQ(legends_get_state_hash(handle_, hash_before.data()), LEGENDS_OK);

    // Save state
    size_t state_size = 0;
    ASSERT_EQ(legends_save_state(handle_, nullptr, 0, &state_size), LEGENDS_OK);
    ASSERT_GT(state_size, 0u);

    std::vector<uint8_t> state_buf(state_size);
    ASSERT_EQ(legends_save_state(handle_, state_buf.data(), state_buf.size(), &state_size), LEGENDS_OK);

    // Destroy current instance
    legends_destroy(handle_);
    handle_ = nullptr;

    // Create brand new instance
    legends_config_t config = LEGENDS_CONFIG_INIT;
    config.deterministic = 1;
    ASSERT_EQ(legends_create(&config, &handle_), LEGENDS_OK);

    // Load saved state into new instance
    ASSERT_EQ(legends_load_state(handle_, state_buf.data(), state_buf.size()), LEGENDS_OK);

    // Get hash after load
    std::array<uint8_t, 32> hash_after{};
    ASSERT_EQ(legends_get_state_hash(handle_, hash_after.data()), LEGENDS_OK);

    EXPECT_EQ(hash_before, hash_after)
        << "State hash must be preserved across save/load on different instances. "
           "If this fails, some migrated state is not being serialized.";
}

/**
 * TEST: Save, load, continue stepping — verify determinism.
 *
 * Save at cycle N, continue to N+10000, get hash.
 * Load back to N, re-step to N+10000, get hash.
 * Hashes must match (determinism invariant).
 */
TEST_F(Sprint2MigrationTest, SaveLoadContinueDeterminism) {
    // Step to checkpoint
    ASSERT_EQ(legends_step_cycles(handle_, 15000, nullptr), LEGENDS_OK);

    // Save checkpoint
    size_t state_size = 0;
    legends_save_state(handle_, nullptr, 0, &state_size);
    std::vector<uint8_t> checkpoint(state_size);
    ASSERT_EQ(legends_save_state(handle_, checkpoint.data(), checkpoint.size(), &state_size), LEGENDS_OK);

    // Continue stepping and get hash
    ASSERT_EQ(legends_step_cycles(handle_, 10000, nullptr), LEGENDS_OK);
    std::array<uint8_t, 32> hash_first{};
    ASSERT_EQ(legends_get_state_hash(handle_, hash_first.data()), LEGENDS_OK);

    // Restore checkpoint
    ASSERT_EQ(legends_load_state(handle_, checkpoint.data(), checkpoint.size()), LEGENDS_OK);

    // Re-step same amount
    ASSERT_EQ(legends_step_cycles(handle_, 10000, nullptr), LEGENDS_OK);
    std::array<uint8_t, 32> hash_second{};
    ASSERT_EQ(legends_get_state_hash(handle_, hash_second.data()), LEGENDS_OK);

    EXPECT_EQ(hash_first, hash_second)
        << "Determinism invariant: save→step→hash must equal load→step→hash. "
           "If this fails, migrated state is affecting execution non-deterministically.";
}

// ═══════════════════════════════════════════════════════════════════════════════
// State Hash Stability After Migration
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * TEST: State hash is non-zero after stepping.
 * Ensures the hash function is actually reading migrated state.
 */
TEST_F(Sprint2MigrationTest, StateHashNonZeroAfterStepping) {
    ASSERT_EQ(legends_step_cycles(handle_, 5000, nullptr), LEGENDS_OK);

    std::array<uint8_t, 32> hash{};
    ASSERT_EQ(legends_get_state_hash(handle_, hash.data()), LEGENDS_OK);

    // Hash should not be all zeros
    std::array<uint8_t, 32> zero{};
    EXPECT_NE(hash, zero)
        << "State hash should be non-zero after stepping. "
           "Hash function may not be reading migrated state.";
}

/**
 * TEST: Different step counts produce different hashes.
 * Verifies state hash actually reflects execution progress.
 */
TEST(Sprint2StateHash, DifferentStepsDifferentHash) {
    std::array<uint8_t, 32> hash_5k{}, hash_10k{};

    {
        legends_handle h = nullptr;
        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.deterministic = 1;
        ASSERT_EQ(legends_create(&config, &h), LEGENDS_OK);
        ASSERT_EQ(legends_step_cycles(h, 5000, nullptr), LEGENDS_OK);
        ASSERT_EQ(legends_get_state_hash(h, hash_5k.data()), LEGENDS_OK);
        legends_destroy(h);
    }

    {
        legends_handle h = nullptr;
        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.deterministic = 1;
        ASSERT_EQ(legends_create(&config, &h), LEGENDS_OK);
        ASSERT_EQ(legends_step_cycles(h, 10000, nullptr), LEGENDS_OK);
        ASSERT_EQ(legends_get_state_hash(h, hash_10k.data()), LEGENDS_OK);
        legends_destroy(h);
    }

    EXPECT_NE(hash_5k, hash_10k)
        << "5000 cycles and 10000 cycles should produce different state hashes.";
}

// ═══════════════════════════════════════════════════════════════════════════════
// Cycle Counter Consistency (Timing State Migration)
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * TEST: Total cycles are tracked correctly and reset per instance.
 */
TEST(Sprint2TimingMigration, CycleCounterResetsPerInstance) {
    // Instance 1: step 20k cycles
    {
        legends_handle h = nullptr;
        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.deterministic = 1;
        ASSERT_EQ(legends_create(&config, &h), LEGENDS_OK);
        ASSERT_EQ(legends_step_cycles(h, 20000, nullptr), LEGENDS_OK);

        uint64_t cycles = 0;
        ASSERT_EQ(legends_get_total_cycles(h, &cycles), LEGENDS_OK);
        EXPECT_GE(cycles, 20000u) << "Should have executed at least 20000 cycles";

        legends_destroy(h);
    }

    // Instance 2: should start fresh at 0
    {
        legends_handle h = nullptr;
        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.deterministic = 1;
        ASSERT_EQ(legends_create(&config, &h), LEGENDS_OK);

        uint64_t cycles = 0;
        ASSERT_EQ(legends_get_total_cycles(h, &cycles), LEGENDS_OK);
        EXPECT_EQ(cycles, 0u)
            << "New instance should start with 0 cycles. "
               "Timing global is leaking from previous instance.";

        legends_destroy(h);
    }
}

/**
 * TEST: Emulated time resets per instance.
 */
TEST(Sprint2TimingMigration, EmulatedTimeResetsPerInstance) {
    // Instance 1: step to accumulate time
    {
        legends_handle h = nullptr;
        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.deterministic = 1;
        ASSERT_EQ(legends_create(&config, &h), LEGENDS_OK);
        ASSERT_EQ(legends_step_ms(h, 100, nullptr), LEGENDS_OK);

        uint64_t time_us = 0;
        ASSERT_EQ(legends_get_emu_time(h, &time_us), LEGENDS_OK);
        EXPECT_GE(time_us, 100000u) << "Should have at least 100ms of emulated time";

        legends_destroy(h);
    }

    // Instance 2: should start fresh at 0
    {
        legends_handle h = nullptr;
        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.deterministic = 1;
        ASSERT_EQ(legends_create(&config, &h), LEGENDS_OK);

        uint64_t time_us = 0;
        ASSERT_EQ(legends_get_emu_time(h, &time_us), LEGENDS_OK);
        EXPECT_EQ(time_us, 0u)
            << "New instance should start with 0 emulated time. "
               "Timing global is leaking from previous instance.";

        legends_destroy(h);
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// Input State Migration
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * TEST: Input state doesn't leak between instances.
 *
 * Inject keys into instance A, destroy, create B.
 * B should have no pending input.
 */
TEST(Sprint2InputMigration, InputStateResetsPerInstance) {
    // Instance 1: inject keys
    {
        legends_handle h = nullptr;
        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.deterministic = 1;
        ASSERT_EQ(legends_create(&config, &h), LEGENDS_OK);

        // Inject multiple key events without stepping
        for (int i = 0; i < 10; i++) {
            legends_key_event(h, 0x1E, 1);  // 'A' press
            legends_key_event(h, 0x1E, 0);  // 'A' release
        }

        legends_destroy(h);
    }

    // Instance 2: should be clean — step and verify deterministic hash
    {
        legends_handle h = nullptr;
        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.deterministic = 1;
        ASSERT_EQ(legends_create(&config, &h), LEGENDS_OK);

        // Step without any input
        ASSERT_EQ(legends_step_cycles(h, 5000, nullptr), LEGENDS_OK);

        std::array<uint8_t, 32> hash{};
        ASSERT_EQ(legends_get_state_hash(h, hash.data()), LEGENDS_OK);

        legends_destroy(h);

        // Verify against a completely fresh instance
        legends_handle fresh = nullptr;
        ASSERT_EQ(legends_create(&config, &fresh), LEGENDS_OK);
        ASSERT_EQ(legends_step_cycles(fresh, 5000, nullptr), LEGENDS_OK);

        std::array<uint8_t, 32> hash_fresh{};
        ASSERT_EQ(legends_get_state_hash(fresh, hash_fresh.data()), LEGENDS_OK);
        legends_destroy(fresh);

        EXPECT_EQ(hash, hash_fresh)
            << "Instance after input-heavy usage must match fresh instance. "
               "Input state global is leaking.";
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// Reset API — Migrated State Must Be Cleared
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * TEST: legends_reset() clears all migrated state back to initial.
 */
TEST_F(Sprint2MigrationTest, ResetClearsMigratedState) {
    // Get initial state hash
    std::array<uint8_t, 32> hash_initial{};
    ASSERT_EQ(legends_get_state_hash(handle_, hash_initial.data()), LEGENDS_OK);

    // Step and modify state
    ASSERT_EQ(legends_step_cycles(handle_, 30000, nullptr), LEGENDS_OK);
    legends_key_event(handle_, 0x39, 1);  // Space press
    legends_key_event(handle_, 0x39, 0);  // Space release
    ASSERT_EQ(legends_step_cycles(handle_, 5000, nullptr), LEGENDS_OK);

    // Verify state changed
    std::array<uint8_t, 32> hash_modified{};
    ASSERT_EQ(legends_get_state_hash(handle_, hash_modified.data()), LEGENDS_OK);
    EXPECT_NE(hash_initial, hash_modified) << "State should have changed after stepping";

    // Reset
    ASSERT_EQ(legends_reset(handle_), LEGENDS_OK);

    // Verify state matches initial
    std::array<uint8_t, 32> hash_after_reset{};
    ASSERT_EQ(legends_get_state_hash(handle_, hash_after_reset.data()), LEGENDS_OK);

    EXPECT_EQ(hash_initial, hash_after_reset)
        << "Reset must restore all migrated state to initial values. "
           "Some global state is not being properly reset.";
}

// ═══════════════════════════════════════════════════════════════════════════════
// PR 9: Header current_context() Cleanup Verification
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * TEST: MEM_GetBaseRef() works via out-of-line compat function.
 *
 * After PR 9, MEM_GetBaseRef() is declared in mem.h but defined
 * in memory_compat.cpp (no current_context() in headers).
 * Verifies the accessor still returns a valid memory base.
 */
TEST_F(Sprint2MigrationTest, MemBaseAccessorWorksViaCompat) {
    // After init, memory base should be non-null and usable
    // Step to ensure context is fully initialized
    ASSERT_EQ(legends_step_cycles(handle_, 1000, nullptr), LEGENDS_OK);

    // Verify state hash is computable (requires memory accessors to work)
    std::array<uint8_t, 32> hash{};
    ASSERT_EQ(legends_get_state_hash(handle_, hash.data()), LEGENDS_OK);

    // Hash should be non-zero (memory state contributes to hash)
    std::array<uint8_t, 32> zero{};
    EXPECT_NE(hash, zero)
        << "State hash should be non-zero. Memory accessor (MEM_GetBaseRef) "
           "may not be working correctly after moving to compat shim.";
}

/**
 * TEST: VSync accessor works via out-of-line compat function.
 *
 * After PR 9, the vsync macro in vga.h is replaced with a
 * function declaration; the body lives in vga_compat.cpp.
 * The VGA state hash (which includes vsync) must still work.
 */
TEST_F(Sprint2MigrationTest, VsyncAccessorWorksViaCompat) {
    // Step to ensure VGA state is initialized
    ASSERT_EQ(legends_step_cycles(handle_, 1000, nullptr), LEGENDS_OK);

    // Get two hashes from same state — must be identical
    // This exercises the vsync accessor path through the hash function
    std::array<uint8_t, 32> hash1{}, hash2{};
    ASSERT_EQ(legends_get_state_hash(handle_, hash1.data()), LEGENDS_OK);
    ASSERT_EQ(legends_get_state_hash(handle_, hash2.data()), LEGENDS_OK);

    EXPECT_EQ(hash1, hash2)
        << "Same state must produce same hash. VSync accessor "
           "may be returning inconsistent values after compat migration.";
}

/**
 * TEST: Save/load still works after header cleanup.
 *
 * This is a regression test to verify that moving memory and vsync
 * accessors from inline to out-of-line doesn't break serialization.
 */
TEST_F(Sprint2MigrationTest, SaveLoadAfterHeaderCleanup) {
    ASSERT_EQ(legends_step_cycles(handle_, 5000, nullptr), LEGENDS_OK);

    // Get hash before save
    std::array<uint8_t, 32> hash_before{};
    ASSERT_EQ(legends_get_state_hash(handle_, hash_before.data()), LEGENDS_OK);

    // Save
    size_t state_size = 0;
    legends_save_state(handle_, nullptr, 0, &state_size);
    std::vector<uint8_t> state(state_size);
    ASSERT_EQ(legends_save_state(handle_, state.data(), state.size(), &state_size), LEGENDS_OK);

    // Destroy and recreate
    legends_destroy(handle_);
    handle_ = nullptr;

    legends_config_t config = LEGENDS_CONFIG_INIT;
    config.deterministic = 1;
    ASSERT_EQ(legends_create(&config, &handle_), LEGENDS_OK);

    // Load
    ASSERT_EQ(legends_load_state(handle_, state.data(), state.size()), LEGENDS_OK);

    // Get hash after load — must match
    std::array<uint8_t, 32> hash_after{};
    ASSERT_EQ(legends_get_state_hash(handle_, hash_after.data()), LEGENDS_OK);

    EXPECT_EQ(hash_before, hash_after)
        << "Save/load round-trip failed after header cleanup. "
           "Memory or VSync compat shim may have broken serialization.";
}

// ═══════════════════════════════════════════════════════════════════════════════
// PR 10: Multi-Instance Smoke Tests
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * TEST: Second instance creation currently fails (single-instance constraint).
 *
 * While we still enforce single-instance-per-process, verify the error
 * is clean and no resources are leaked.
 */
TEST(MultiInstance, SecondCreateCurrentlyFails) {
    legends_handle a = nullptr, b = nullptr;
    legends_config_t config = LEGENDS_CONFIG_INIT;
    config.deterministic = 1;

    ASSERT_EQ(legends_create(&config, &a), LEGENDS_OK);
    EXPECT_EQ(legends_create(&config, &b), LEGENDS_ERR_ALREADY_CREATED);
    EXPECT_EQ(b, nullptr) << "Failed create should not set handle";

    legends_destroy(a);
}

/**
 * TEST: Sequential instances are fully independent.
 *
 * Create A, step 10k cycles, hash. Destroy A.
 * Create B, step 10k cycles, hash. Destroy B.
 * Hashes must match — proving no global state leaks between instances.
 */
TEST(MultiInstance, SequentialInstancesIndependent) {
    std::array<uint8_t, 32> hash_a{}, hash_b{};

    // Instance A
    {
        legends_handle a = nullptr;
        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.deterministic = 1;
        ASSERT_EQ(legends_create(&config, &a), LEGENDS_OK);
        ASSERT_EQ(legends_step_cycles(a, 10000, nullptr), LEGENDS_OK);
        ASSERT_EQ(legends_get_state_hash(a, hash_a.data()), LEGENDS_OK);
        legends_destroy(a);
    }

    // Instance B — same config, same steps
    {
        legends_handle b = nullptr;
        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.deterministic = 1;
        ASSERT_EQ(legends_create(&config, &b), LEGENDS_OK);
        ASSERT_EQ(legends_step_cycles(b, 10000, nullptr), LEGENDS_OK);
        ASSERT_EQ(legends_get_state_hash(b, hash_b.data()), LEGENDS_OK);
        legends_destroy(b);
    }

    EXPECT_EQ(hash_a, hash_b)
        << "Sequential instances with identical input must produce identical state. "
           "Global state is leaking between instance lifetimes.";
}

/**
 * TEST: Instance with input diverges from instance without input.
 *
 * Creates two sequential instances: one with key input, one without.
 * They should have different hashes, proving input state is properly
 * tracked and doesn't leak.
 */
TEST(MultiInstance, InputCausesDivergence) {
    std::array<uint8_t, 32> hash_with_input{}, hash_without_input{};

    // Instance with key input
    {
        legends_handle h = nullptr;
        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.deterministic = 1;
        ASSERT_EQ(legends_create(&config, &h), LEGENDS_OK);
        legends_key_event(h, 0x1E, 1);  // 'A' press
        legends_key_event(h, 0x1E, 0);  // 'A' release
        ASSERT_EQ(legends_step_cycles(h, 10000, nullptr), LEGENDS_OK);
        ASSERT_EQ(legends_get_state_hash(h, hash_with_input.data()), LEGENDS_OK);
        legends_destroy(h);
    }

    // Instance without input
    {
        legends_handle h = nullptr;
        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.deterministic = 1;
        ASSERT_EQ(legends_create(&config, &h), LEGENDS_OK);
        ASSERT_EQ(legends_step_cycles(h, 10000, nullptr), LEGENDS_OK);
        ASSERT_EQ(legends_get_state_hash(h, hash_without_input.data()), LEGENDS_OK);
        legends_destroy(h);
    }

    EXPECT_NE(hash_with_input, hash_without_input)
        << "Instance with key input must differ from instance without. "
           "Input state is not properly tracked in the hash.";
}

/**
 * TEST: Clean instance after dirty instance matches fresh instance.
 *
 * Create instance A, do heavy stepping and key injection.
 * Destroy A. Create B with no input.
 * B must match a third fresh instance C with identical steps.
 */
TEST(MultiInstance, CleanAfterDirty) {
    // Dirty instance A — lots of stepping and input
    {
        legends_handle a = nullptr;
        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.deterministic = 1;
        ASSERT_EQ(legends_create(&config, &a), LEGENDS_OK);

        for (int i = 0; i < 20; i++) {
            legends_key_event(a, 0x1E + (i % 10), 1);
            legends_key_event(a, 0x1E + (i % 10), 0);
            ASSERT_EQ(legends_step_cycles(a, 5000, nullptr), LEGENDS_OK);
        }
        legends_destroy(a);
    }

    std::array<uint8_t, 32> hash_b{}, hash_c{};

    // Clean instance B
    {
        legends_handle b = nullptr;
        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.deterministic = 1;
        ASSERT_EQ(legends_create(&config, &b), LEGENDS_OK);
        ASSERT_EQ(legends_step_cycles(b, 7500, nullptr), LEGENDS_OK);
        ASSERT_EQ(legends_get_state_hash(b, hash_b.data()), LEGENDS_OK);
        legends_destroy(b);
    }

    // Fresh instance C — must match B
    {
        legends_handle c = nullptr;
        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.deterministic = 1;
        ASSERT_EQ(legends_create(&config, &c), LEGENDS_OK);
        ASSERT_EQ(legends_step_cycles(c, 7500, nullptr), LEGENDS_OK);
        ASSERT_EQ(legends_get_state_hash(c, hash_c.data()), LEGENDS_OK);
        legends_destroy(c);
    }

    EXPECT_EQ(hash_b, hash_c)
        << "Clean instance after dirty usage must match fresh instance. "
           "Global state is contaminating new instances.";
}

// ═══════════════════════════════════════════════════════════════════════════════
// Rapid Create/Destroy Stability (Stress Test for Migration)
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * TEST: 50 rapid create/step/destroy cycles produce consistent hashes.
 *
 * Every iteration should produce the same hash, proving no global
 * state accumulates across instance lifetimes.
 */
TEST(Sprint2Stability, RapidCreateDestroyConsistentHash) {
    std::array<uint8_t, 32> reference_hash{};

    // Get reference hash from first instance
    {
        legends_handle h = nullptr;
        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.deterministic = 1;
        ASSERT_EQ(legends_create(&config, &h), LEGENDS_OK);
        ASSERT_EQ(legends_step_cycles(h, 8000, nullptr), LEGENDS_OK);
        ASSERT_EQ(legends_get_state_hash(h, reference_hash.data()), LEGENDS_OK);
        legends_destroy(h);
    }

    // Verify all subsequent instances produce the same hash
    for (int i = 0; i < 50; i++) {
        legends_handle h = nullptr;
        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.deterministic = 1;
        ASSERT_EQ(legends_create(&config, &h), LEGENDS_OK)
            << "Create failed on iteration " << i;
        ASSERT_EQ(legends_step_cycles(h, 8000, nullptr), LEGENDS_OK)
            << "Step failed on iteration " << i;

        std::array<uint8_t, 32> hash{};
        ASSERT_EQ(legends_get_state_hash(h, hash.data()), LEGENDS_OK)
            << "Hash failed on iteration " << i;

        EXPECT_EQ(hash, reference_hash)
            << "Hash diverged on iteration " << i
            << ". Global state accumulating across instances.";

        legends_destroy(h);
    }
}
