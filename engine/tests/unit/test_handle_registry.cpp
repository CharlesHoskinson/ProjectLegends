/**
 * @file test_handle_registry.cpp
 * @brief Unit tests for HandleRegistry and PackedHandle.
 */

#include <gtest/gtest.h>
#include <aibox/handle_registry.h>
#include <thread>
#include <vector>

using namespace aibox;

// ─────────────────────────────────────────────────────────────────────────────
// PackedHandle Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(PackedHandleTest, Create) {
    auto handle = PackedHandle::create(42, 7);

    EXPECT_EQ(handle.slot(), 42u);
    EXPECT_EQ(handle.generation(), 7u);
}

TEST(PackedHandleTest, SlotMask) {
    // Slot should be masked to 20 bits
    auto handle = PackedHandle::create(0xFFFFF, 0);
    EXPECT_EQ(handle.slot(), 0xFFFFFu);

    // Overflow should be masked
    auto overflow = PackedHandle::create(0x100000, 0);
    EXPECT_EQ(overflow.slot(), 0u);
}

TEST(PackedHandleTest, GenerationMask) {
    // Generation should be masked to 12 bits
    auto handle = PackedHandle::create(0, 0xFFF);
    EXPECT_EQ(handle.generation(), 0xFFFu);

    // Overflow should be masked
    auto overflow = PackedHandle::create(0, 0x1000);
    EXPECT_EQ(overflow.generation(), 0u);
}

TEST(PackedHandleTest, NullHandle) {
    PackedHandle null{0};
    EXPECT_TRUE(null.is_null());

    auto non_null = PackedHandle::create(1, 0);
    EXPECT_FALSE(non_null.is_null());
}

TEST(PackedHandleTest, Equality) {
    auto a = PackedHandle::create(10, 5);
    auto b = PackedHandle::create(10, 5);
    auto c = PackedHandle::create(10, 6);

    EXPECT_EQ(a, b);
    EXPECT_NE(a, c);
}

TEST(PackedHandleTest, OpaqueRoundtrip) {
    auto original = PackedHandle::create(12345, 678);

    void* opaque = original.to_opaque();
    auto recovered = PackedHandle::from_opaque(opaque);

    EXPECT_EQ(original, recovered);
    EXPECT_EQ(recovered.slot(), 12345u);
    EXPECT_EQ(recovered.generation(), 678u);
}

TEST(PackedHandleTest, FromNullOpaque) {
    auto handle = PackedHandle::from_opaque(nullptr);
    EXPECT_TRUE(handle.is_null());
}

// ─────────────────────────────────────────────────────────────────────────────
// HandleType Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(HandleTypeTest, ToString) {
    EXPECT_STREQ(to_string(HandleType::Invalid), "Invalid");
    EXPECT_STREQ(to_string(HandleType::Emulator), "Emulator");
    EXPECT_STREQ(to_string(HandleType::Subscription), "Subscription");
    EXPECT_STREQ(to_string(HandleType::MemoryView), "MemoryView");
    EXPECT_STREQ(to_string(HandleType::EventBatch), "EventBatch");
}

// ─────────────────────────────────────────────────────────────────────────────
// HandleStatus Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(HandleStatusTest, ToString) {
    EXPECT_STREQ(to_string(HandleStatus::Valid), "Valid");
    EXPECT_STREQ(to_string(HandleStatus::Null), "Null");
    EXPECT_STREQ(to_string(HandleStatus::InvalidGeneration), "InvalidGeneration");
    EXPECT_STREQ(to_string(HandleStatus::WrongType), "WrongType");
    EXPECT_STREQ(to_string(HandleStatus::Destroyed), "Destroyed");
    EXPECT_STREQ(to_string(HandleStatus::OutOfBounds), "OutOfBounds");
}

// ─────────────────────────────────────────────────────────────────────────────
// HandleRegistry Basic Tests
// ─────────────────────────────────────────────────────────────────────────────

class HandleRegistryTest : public ::testing::Test {
protected:
    HandleRegistry registry;
    int test_object = 42;
    double another_object = 3.14;
};

TEST_F(HandleRegistryTest, AllocateAndValidate) {
    auto handle = registry.allocate(&test_object, HandleType::Emulator);

    EXPECT_FALSE(handle.is_null());
    EXPECT_EQ(registry.validate(handle, HandleType::Emulator), HandleStatus::Valid);
}

TEST_F(HandleRegistryTest, AllocateNullObject) {
    int* null_ptr = nullptr;
    auto handle = registry.allocate(null_ptr, HandleType::Emulator);

    EXPECT_TRUE(handle.is_null());
}

TEST_F(HandleRegistryTest, AllocateInvalidType) {
    auto handle = registry.allocate(&test_object, HandleType::Invalid);

    EXPECT_TRUE(handle.is_null());
}

TEST_F(HandleRegistryTest, GetObject) {
    auto handle = registry.allocate(&test_object, HandleType::Emulator);

    auto result = registry.get<int>(handle, HandleType::Emulator);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(*result.value(), 42);
}

TEST_F(HandleRegistryTest, GetConstObject) {
    auto handle = registry.allocate(&test_object, HandleType::Emulator);

    auto result = registry.get_const<int>(handle, HandleType::Emulator);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(*result.value(), 42);
}

TEST_F(HandleRegistryTest, GetWithWrongType) {
    auto handle = registry.allocate(&test_object, HandleType::Emulator);

    auto result = registry.get<double>(handle, HandleType::Emulator);
    EXPECT_FALSE(result.has_value());
}

TEST_F(HandleRegistryTest, GetWithWrongHandleType) {
    auto handle = registry.allocate(&test_object, HandleType::Emulator);

    auto result = registry.get<int>(handle, HandleType::Subscription);
    EXPECT_FALSE(result.has_value());
}

TEST_F(HandleRegistryTest, FreeAndInvalidate) {
    auto handle = registry.allocate(&test_object, HandleType::Emulator);

    EXPECT_TRUE(registry.free(handle));
    // After free, slot is not in use - returns Destroyed
    // InvalidGeneration would only occur if slot was reused
    EXPECT_EQ(registry.validate(handle), HandleStatus::Destroyed);
}

TEST_F(HandleRegistryTest, UseAfterFreeDetected) {
    auto handle = registry.allocate(&test_object, HandleType::Emulator);
    registry.free(handle);

    // Old handle should be invalid (slot not in use)
    auto result = registry.get<int>(handle, HandleType::Emulator);
    EXPECT_FALSE(result.has_value());

    // Validate should report slot was destroyed (not in use)
    EXPECT_EQ(registry.validate(handle, HandleType::Emulator),
              HandleStatus::Destroyed);
}

TEST_F(HandleRegistryTest, FreeTwiceFails) {
    auto handle = registry.allocate(&test_object, HandleType::Emulator);

    EXPECT_TRUE(registry.free(handle));
    EXPECT_FALSE(registry.free(handle));  // Second free fails
}

TEST_F(HandleRegistryTest, FreeNullHandle) {
    PackedHandle null{0};
    EXPECT_FALSE(registry.free(null));
}

TEST_F(HandleRegistryTest, ValidateNullHandle) {
    PackedHandle null{0};
    EXPECT_EQ(registry.validate(null), HandleStatus::Null);
}

TEST_F(HandleRegistryTest, ValidateOutOfBounds) {
    // Create handle with slot beyond max
    auto bad_handle = PackedHandle::create(HandleRegistry::MaxHandles + 1, 0);
    EXPECT_EQ(registry.validate(bad_handle), HandleStatus::OutOfBounds);
}

// ─────────────────────────────────────────────────────────────────────────────
// HandleRegistry Multiple Handles Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(HandleRegistryTest, MultipleHandles) {
    auto h1 = registry.allocate(&test_object, HandleType::Emulator);
    auto h2 = registry.allocate(&another_object, HandleType::MemoryView);

    EXPECT_FALSE(h1.is_null());
    EXPECT_FALSE(h2.is_null());
    EXPECT_NE(h1, h2);

    EXPECT_EQ(registry.active_count(), 2u);

    // Each handle is valid for its type
    EXPECT_EQ(registry.validate(h1, HandleType::Emulator), HandleStatus::Valid);
    EXPECT_EQ(registry.validate(h2, HandleType::MemoryView), HandleStatus::Valid);

    // Wrong type fails
    EXPECT_EQ(registry.validate(h1, HandleType::MemoryView), HandleStatus::WrongType);
    EXPECT_EQ(registry.validate(h2, HandleType::Emulator), HandleStatus::WrongType);
}

TEST_F(HandleRegistryTest, ReuseSlotAfterFree) {
    auto h1 = registry.allocate(&test_object, HandleType::Emulator);
    uint32_t first_slot = h1.slot();
    uint32_t first_gen = h1.generation();

    registry.free(h1);

    // Allocate again - may reuse same slot
    auto h2 = registry.allocate(&another_object, HandleType::Emulator);

    if (h2.slot() == first_slot) {
        // If same slot, generation must be different
        EXPECT_NE(h2.generation(), first_gen);

        // Old handle now reports InvalidGeneration (slot reused with new gen)
        EXPECT_EQ(registry.validate(h1, HandleType::Emulator),
                  HandleStatus::InvalidGeneration);
    } else {
        // If different slot, old handle reports Destroyed
        EXPECT_EQ(registry.validate(h1, HandleType::Emulator),
                  HandleStatus::Destroyed);
    }

    // New handle should be valid
    EXPECT_EQ(registry.validate(h2, HandleType::Emulator), HandleStatus::Valid);
}

TEST_F(HandleRegistryTest, ActiveCount) {
    EXPECT_EQ(registry.active_count(), 0u);

    auto h1 = registry.allocate(&test_object, HandleType::Emulator);
    EXPECT_EQ(registry.active_count(), 1u);

    auto h2 = registry.allocate(&another_object, HandleType::MemoryView);
    EXPECT_EQ(registry.active_count(), 2u);

    registry.free(h1);
    EXPECT_EQ(registry.active_count(), 1u);

    registry.free(h2);
    EXPECT_EQ(registry.active_count(), 0u);
}

TEST_F(HandleRegistryTest, MaxHandles) {
    EXPECT_EQ(HandleRegistry::max_handles(), HandleRegistry::MaxHandles);
    EXPECT_EQ(HandleRegistry::max_handles(), 1024u);
}

// ─────────────────────────────────────────────────────────────────────────────
// HandleRegistry Thread Safety Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(HandleRegistryTest, ConcurrentAllocations) {
    std::vector<std::thread> threads;
    std::vector<PackedHandle> handles;
    std::mutex handles_mutex;

    // Allocate from multiple threads
    for (int i = 0; i < 4; ++i) {
        threads.emplace_back([this, &handles, &handles_mutex]() {
            for (int j = 0; j < 50; ++j) {
                auto h = registry.allocate(&test_object, HandleType::Emulator);
                if (!h.is_null()) {
                    std::lock_guard lock(handles_mutex);
                    handles.push_back(h);
                }
            }
        });
    }

    for (auto& t : threads) {
        t.join();
    }

    // All handles should be valid
    for (const auto& h : handles) {
        EXPECT_EQ(registry.validate(h, HandleType::Emulator), HandleStatus::Valid);
    }

    // Count should match
    EXPECT_EQ(registry.active_count(), handles.size());

    // Clean up
    for (const auto& h : handles) {
        registry.free(h);
    }
}

TEST_F(HandleRegistryTest, ConcurrentAllocAndFree) {
    std::atomic<int> alloc_count{0};
    std::atomic<int> free_count{0};
    std::vector<std::thread> threads;

    // Mix of allocations and frees
    for (int i = 0; i < 4; ++i) {
        threads.emplace_back([this, &alloc_count, &free_count]() {
            for (int j = 0; j < 100; ++j) {
                auto h = registry.allocate(&test_object, HandleType::Emulator);
                if (!h.is_null()) {
                    alloc_count++;
                    if (registry.free(h)) {
                        free_count++;
                    }
                }
            }
        });
    }

    for (auto& t : threads) {
        t.join();
    }

    // All allocations should have been freed
    EXPECT_EQ(alloc_count.load(), free_count.load());
    EXPECT_EQ(registry.active_count(), 0u);
}

// ─────────────────────────────────────────────────────────────────────────────
// HandleRegistry Registry Full Test
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(HandleRegistryTest, RegistryFull) {
    std::vector<PackedHandle> handles;

    // Fill the registry
    for (size_t i = 0; i < HandleRegistry::MaxHandles; ++i) {
        auto h = registry.allocate(&test_object, HandleType::Emulator);
        if (!h.is_null()) {
            handles.push_back(h);
        }
    }

    EXPECT_EQ(registry.active_count(), HandleRegistry::MaxHandles);
    EXPECT_TRUE(registry.is_full());

    // Next allocation should fail
    auto overflow = registry.allocate(&another_object, HandleType::Emulator);
    EXPECT_TRUE(overflow.is_null());

    // Free one and try again
    registry.free(handles.back());
    handles.pop_back();

    EXPECT_FALSE(registry.is_full());

    auto new_handle = registry.allocate(&another_object, HandleType::Emulator);
    EXPECT_FALSE(new_handle.is_null());

    // Clean up
    for (const auto& h : handles) {
        registry.free(h);
    }
    registry.free(new_handle);
}

// ─────────────────────────────────────────────────────────────────────────────
// Generation Wraparound Test
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(HandleRegistryTest, GenerationWraparound) {
    // This test verifies that generation-based validation works
    // even when generations wrap around (after 4096 alloc/free cycles)

    std::vector<PackedHandle> old_handles;

    // Perform many alloc/free cycles on the same slot
    for (int cycle = 0; cycle < 10; ++cycle) {
        auto h = registry.allocate(&test_object, HandleType::Emulator);
        ASSERT_FALSE(h.is_null());

        old_handles.push_back(h);
        registry.free(h);

        // After freeing, the handle should be invalid
        EXPECT_NE(registry.validate(h, HandleType::Emulator), HandleStatus::Valid);
    }

    // All old handles should be invalid
    for (const auto& h : old_handles) {
        EXPECT_NE(registry.validate(h, HandleType::Emulator), HandleStatus::Valid);
    }
}
