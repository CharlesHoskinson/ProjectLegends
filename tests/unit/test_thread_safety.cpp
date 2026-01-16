/**
 * @file test_thread_safety.cpp
 * @brief Thread safety and threading model tests.
 *
 * Verifies:
 * - LEGENDS_ERR_WRONG_THREAD is returned for cross-thread access
 * - Thread affinity checking works correctly
 * - Single-threaded access model is enforced
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include <pal/platform.h>
#include <thread>
#include <atomic>
#include <vector>
#include <chrono>

class ThreadSafetyTest : public ::testing::Test {
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

// Test that step_cycles from wrong thread returns LEGENDS_ERR_WRONG_THREAD
TEST_F(ThreadSafetyTest, StepCyclesFromWrongThreadReturnsError) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    std::atomic<legends_error_t> result{LEGENDS_OK};
    std::thread other([&]() {
        legends_step_result_t step_result;
        result = legends_step_cycles(handle, 1000, &step_result);
    });
    other.join();

    EXPECT_EQ(result.load(), LEGENDS_ERR_WRONG_THREAD);
    legends_destroy(handle);
}

// Test that step_ms from wrong thread returns LEGENDS_ERR_WRONG_THREAD
TEST_F(ThreadSafetyTest, StepMsFromWrongThreadReturnsError) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    std::atomic<legends_error_t> result{LEGENDS_OK};
    std::thread other([&]() {
        legends_step_result_t step_result;
        result = legends_step_ms(handle, 10, &step_result);
    });
    other.join();

    EXPECT_EQ(result.load(), LEGENDS_ERR_WRONG_THREAD);
    legends_destroy(handle);
}

// Test that capture_text from wrong thread returns LEGENDS_ERR_WRONG_THREAD
TEST_F(ThreadSafetyTest, CaptureTextFromWrongThreadReturnsError) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    std::atomic<legends_error_t> result{LEGENDS_OK};
    std::thread other([&]() {
        size_t count;
        result = legends_capture_text(handle, nullptr, 0, &count, nullptr);
    });
    other.join();

    EXPECT_EQ(result.load(), LEGENDS_ERR_WRONG_THREAD);
    legends_destroy(handle);
}

// Test that capture_rgb from wrong thread returns LEGENDS_ERR_WRONG_THREAD
TEST_F(ThreadSafetyTest, CaptureRgbFromWrongThreadReturnsError) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    std::atomic<legends_error_t> result{LEGENDS_OK};
    std::thread other([&]() {
        size_t size;
        uint16_t width, height;
        result = legends_capture_rgb(handle, nullptr, 0, &size, &width, &height);
    });
    other.join();

    EXPECT_EQ(result.load(), LEGENDS_ERR_WRONG_THREAD);
    legends_destroy(handle);
}

// Test that key_event from wrong thread returns LEGENDS_ERR_WRONG_THREAD
TEST_F(ThreadSafetyTest, KeyEventFromWrongThreadReturnsError) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    std::atomic<legends_error_t> result{LEGENDS_OK};
    std::thread other([&]() {
        result = legends_key_event(handle, 0x1E, 1);
    });
    other.join();

    EXPECT_EQ(result.load(), LEGENDS_ERR_WRONG_THREAD);
    legends_destroy(handle);
}

// Test that mouse_event from wrong thread returns LEGENDS_ERR_WRONG_THREAD
TEST_F(ThreadSafetyTest, MouseEventFromWrongThreadReturnsError) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    std::atomic<legends_error_t> result{LEGENDS_OK};
    std::thread other([&]() {
        result = legends_mouse_event(handle, 5, 5, 0);
    });
    other.join();

    EXPECT_EQ(result.load(), LEGENDS_ERR_WRONG_THREAD);
    legends_destroy(handle);
}

// Test that save_state from wrong thread returns LEGENDS_ERR_WRONG_THREAD
TEST_F(ThreadSafetyTest, SaveStateFromWrongThreadReturnsError) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    std::atomic<legends_error_t> result{LEGENDS_OK};
    std::thread other([&]() {
        size_t size;
        result = legends_save_state(handle, nullptr, 0, &size);
    });
    other.join();

    EXPECT_EQ(result.load(), LEGENDS_ERR_WRONG_THREAD);
    legends_destroy(handle);
}

// Test that load_state from wrong thread returns LEGENDS_ERR_WRONG_THREAD
TEST_F(ThreadSafetyTest, LoadStateFromWrongThreadReturnsError) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    // First save state from the correct thread
    size_t size;
    legends_save_state(handle, nullptr, 0, &size);
    std::vector<uint8_t> state(size);
    legends_save_state(handle, state.data(), size, &size);

    std::atomic<legends_error_t> result{LEGENDS_OK};
    std::thread other([&]() {
        result = legends_load_state(handle, state.data(), size);
    });
    other.join();

    EXPECT_EQ(result.load(), LEGENDS_ERR_WRONG_THREAD);
    legends_destroy(handle);
}

// Test that reset from wrong thread returns LEGENDS_ERR_WRONG_THREAD
TEST_F(ThreadSafetyTest, ResetFromWrongThreadReturnsError) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    std::atomic<legends_error_t> result{LEGENDS_OK};
    std::thread other([&]() {
        result = legends_reset(handle);
    });
    other.join();

    EXPECT_EQ(result.load(), LEGENDS_ERR_WRONG_THREAD);
    legends_destroy(handle);
}

// Test that get_state_hash from wrong thread returns LEGENDS_ERR_WRONG_THREAD
TEST_F(ThreadSafetyTest, GetStateHashFromWrongThreadReturnsError) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    std::atomic<legends_error_t> result{LEGENDS_OK};
    std::thread other([&]() {
        uint8_t hash[32];
        result = legends_get_state_hash(handle, hash);
    });
    other.join();

    EXPECT_EQ(result.load(), LEGENDS_ERR_WRONG_THREAD);
    legends_destroy(handle);
}

// Test that destroy may be allowed from any thread for cleanup purposes
// Note: Some implementations allow destroy from any thread to facilitate cleanup
TEST_F(ThreadSafetyTest, DestroyFromAnyThreadAllowed) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    std::atomic<legends_error_t> result{LEGENDS_OK};
    std::thread other([&]() {
        result = legends_destroy(handle);
    });
    other.join();

    // Implementation may allow destroy from any thread or restrict to owner
    // Either LEGENDS_OK or LEGENDS_ERR_WRONG_THREAD is acceptable
    bool is_ok = (result.load() == LEGENDS_OK) ||
                 (result.load() == LEGENDS_ERR_WRONG_THREAD);
    EXPECT_TRUE(is_ok) << "Destroy returned unexpected error: " << result.load();

    // If destroy from other thread failed, clean up from owner thread
    if (result.load() == LEGENDS_ERR_WRONG_THREAD) {
        legends_destroy(handle);
    }
}

// Test that multiple API calls from owner thread all succeed
TEST_F(ThreadSafetyTest, OwnerThreadCanCallAllAPIs) {
    legends_handle handle = nullptr;
    legends_error_t err;

    err = legends_create(nullptr, &handle);
    ASSERT_EQ(err, LEGENDS_OK);

    // All these should succeed from owner thread
    legends_step_result_t step_result;
    err = legends_step_cycles(handle, 1000, &step_result);
    EXPECT_EQ(err, LEGENDS_OK);

    err = legends_step_ms(handle, 10, &step_result);
    EXPECT_EQ(err, LEGENDS_OK);

    size_t count;
    err = legends_capture_text(handle, nullptr, 0, &count, nullptr);
    EXPECT_EQ(err, LEGENDS_OK);

    size_t size;
    uint16_t width, height;
    err = legends_capture_rgb(handle, nullptr, 0, &size, &width, &height);
    EXPECT_EQ(err, LEGENDS_OK);

    err = legends_key_event(handle, 0x1E, 1);
    EXPECT_EQ(err, LEGENDS_OK);

    err = legends_mouse_event(handle, 5, 5, 0);
    EXPECT_EQ(err, LEGENDS_OK);

    err = legends_reset(handle);
    EXPECT_EQ(err, LEGENDS_OK);

    uint8_t hash[32];
    err = legends_get_state_hash(handle, hash);
    EXPECT_EQ(err, LEGENDS_OK);

    err = legends_destroy(handle);
    EXPECT_EQ(err, LEGENDS_OK);
}

// Test multiple threads trying to access same handle concurrently
TEST_F(ThreadSafetyTest, ConcurrentAccessReturnsWrongThread) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    std::atomic<int> wrong_thread_count{0};
    std::vector<std::thread> threads;

    for (int i = 0; i < 5; ++i) {
        threads.emplace_back([&]() {
            legends_step_result_t result;
            legends_error_t err = legends_step_cycles(handle, 100, &result);
            if (err == LEGENDS_ERR_WRONG_THREAD) {
                wrong_thread_count++;
            }
        });
    }

    for (auto& t : threads) {
        t.join();
    }

    // All threads should have received WRONG_THREAD
    EXPECT_EQ(wrong_thread_count.load(), 5);

    legends_destroy(handle);
}

// Test that read-only queries from wrong thread still return WRONG_THREAD
TEST_F(ThreadSafetyTest, ReadOnlyQueriesFromWrongThreadReturnsError) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    std::atomic<legends_error_t> result1{LEGENDS_OK};
    std::atomic<legends_error_t> result2{LEGENDS_OK};
    std::atomic<legends_error_t> result3{LEGENDS_OK};

    std::thread t1([&]() {
        uint64_t time;
        result1 = legends_get_emu_time(handle, &time);
    });

    std::thread t2([&]() {
        uint64_t cycles;
        result2 = legends_get_total_cycles(handle, &cycles);
    });

    std::thread t3([&]() {
        int dirty;
        result3 = legends_is_frame_dirty(handle, &dirty);
    });

    t1.join();
    t2.join();
    t3.join();

    EXPECT_EQ(result1.load(), LEGENDS_ERR_WRONG_THREAD);
    EXPECT_EQ(result2.load(), LEGENDS_ERR_WRONG_THREAD);
    EXPECT_EQ(result3.load(), LEGENDS_ERR_WRONG_THREAD);

    legends_destroy(handle);
}

// Test thread ID checking consistency
TEST_F(ThreadSafetyTest, ThreadAffinityConsistentAcrossMultipleCalls) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    // Make multiple calls from same wrong thread - all should fail consistently
    std::atomic<int> wrong_thread_errors{0};
    std::thread other([&]() {
        for (int i = 0; i < 10; ++i) {
            legends_step_result_t result;
            if (legends_step_cycles(handle, 100, &result) == LEGENDS_ERR_WRONG_THREAD) {
                wrong_thread_errors++;
            }
        }
    });
    other.join();

    EXPECT_EQ(wrong_thread_errors.load(), 10)
        << "All calls from wrong thread must return WRONG_THREAD";

    legends_destroy(handle);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Test Hardening: Thread-Affinity for Destroy/Reset
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(ThreadSafetyTest, DestroyFromWrongThreadReturnsWrongThread) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    std::atomic<legends_error_t> result{LEGENDS_OK};
    std::thread other([&]() {
        result = legends_destroy(handle);
    });
    other.join();

    // Destroy from wrong thread should return WRONG_THREAD
    EXPECT_EQ(result.load(), LEGENDS_ERR_WRONG_THREAD)
        << "Destroy from wrong thread should return WRONG_THREAD";

    // Clean up from owner thread
    legends_destroy(handle);
}

TEST_F(ThreadSafetyTest, ResetStepDestroyFromWrongThread) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    std::atomic<legends_error_t> reset_err{LEGENDS_OK};
    std::atomic<legends_error_t> step_err{LEGENDS_OK};

    std::thread other([&]() {
        reset_err = legends_reset(handle);
        legends_step_result_t result;
        step_err = legends_step_cycles(handle, 1000, &result);
    });
    other.join();

    EXPECT_EQ(reset_err.load(), LEGENDS_ERR_WRONG_THREAD);
    EXPECT_EQ(step_err.load(), LEGENDS_ERR_WRONG_THREAD);

    legends_destroy(handle);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Test Hardening: Handle Registry (Single-Instance)
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(ThreadSafetyTest, HandleRegistryNoUseAfterFree) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    // Step once from owner thread to establish state
    legends_step_cycles(handle, 1000, nullptr);

    // Save the handle pointer value
    legends_handle old_handle = handle;

    // Destroy
    legends_destroy(handle);

    // Trying to use the old handle should fail gracefully
    // (either NULL_HANDLE or INVALID_HANDLE, but not crash)
    legends_step_result_t result;
    auto err = legends_step_cycles(old_handle, 1000, &result);

    // Should not return OK (handle is invalid now)
    EXPECT_NE(err, LEGENDS_OK)
        << "Using freed handle should not succeed";

    // Should not crash - if we got here, the test passed
}

TEST_F(ThreadSafetyTest, RapidCreateDestroyCycle) {
    // Test rapid create/destroy doesn't cause issues
    // Note: Each iteration needs fresh Platform state
    for (int i = 0; i < 5; ++i) {
        // Re-initialize platform for each iteration
        pal::Platform::shutdown();
        pal::Platform::initialize(pal::Backend::Headless);

        legends_handle handle = nullptr;
        auto err = legends_create(nullptr, &handle);
        ASSERT_EQ(err, LEGENDS_OK) << "Create failed on iteration " << i;

        legends_step_cycles(handle, 100, nullptr);

        err = legends_destroy(handle);
        EXPECT_EQ(err, LEGENDS_OK) << "Destroy failed on iteration " << i;
    }
}

TEST_F(ThreadSafetyTest, ConcurrentDestroyAttempts) {
    legends_handle handle = nullptr;
    legends_create(nullptr, &handle);

    std::atomic<int> wrong_thread_count{0};
    std::atomic<int> ok_count{0};
    std::vector<std::thread> threads;

    // Multiple threads try to destroy simultaneously
    for (int i = 0; i < 5; ++i) {
        threads.emplace_back([&]() {
            auto err = legends_destroy(handle);
            if (err == LEGENDS_ERR_WRONG_THREAD) {
                wrong_thread_count++;
            } else if (err == LEGENDS_OK) {
                ok_count++;
            }
        });
    }

    for (auto& t : threads) {
        t.join();
    }

    // All should get WRONG_THREAD since they're not the owner
    EXPECT_EQ(wrong_thread_count.load(), 5);
    EXPECT_EQ(ok_count.load(), 0);

    // Clean up from owner thread
    legends_destroy(handle);
}

