/**
 * @file test_callback_registry.cpp
 * @brief Unit tests for CallbackRegistry and CallbackToken.
 */

#include <gtest/gtest.h>
#include <legends/callback_registry.h>

using namespace legends;

// ─────────────────────────────────────────────────────────────────────────────
// Test Fixtures
// ─────────────────────────────────────────────────────────────────────────────

class CallbackRegistryTest : public ::testing::Test {
protected:
    CallbackRegistry registry_;

    static uint32_t simple_callback(void* userdata) {
        return *static_cast<uint32_t*>(userdata);
    }

    static uint32_t increment_callback(void* userdata) {
        return ++(*static_cast<uint32_t*>(userdata));
    }

    static uint32_t no_op_callback(void*) {
        return 0;
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// Registration Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(CallbackRegistryTest, RegisterReturnsValidToken) {
    uint32_t value = 42;
    auto token = registry_.register_callback(simple_callback, &value, "test");

    EXPECT_TRUE(token.has_value());
    EXPECT_TRUE(token->valid());
}

TEST_F(CallbackRegistryTest, RegisterReturnsUniqueIds) {
    uint32_t v1 = 1, v2 = 2, v3 = 3;

    auto t1 = registry_.register_callback(simple_callback, &v1);
    auto t2 = registry_.register_callback(simple_callback, &v2);
    auto t3 = registry_.register_callback(simple_callback, &v3);

    EXPECT_NE(t1->id(), t2->id());
    EXPECT_NE(t2->id(), t3->id());
    EXPECT_NE(t1->id(), t3->id());
}

TEST_F(CallbackRegistryTest, RegisterNullHandlerFails) {
    auto token = registry_.register_callback(nullptr, nullptr);

    EXPECT_FALSE(token.has_value());
}

TEST_F(CallbackRegistryTest, RegisterWithNullUserdata) {
    auto token = registry_.register_callback(no_op_callback, nullptr, "no-op");

    EXPECT_TRUE(token.has_value());
    EXPECT_EQ(registry_.invoke(token->id()), 0u);
}

// ─────────────────────────────────────────────────────────────────────────────
// Invocation Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(CallbackRegistryTest, InvokeReturnsCorrectValue) {
    uint32_t value = 123;
    auto token = registry_.register_callback(simple_callback, &value);

    EXPECT_EQ(registry_.invoke(token->id()), 123u);
}

TEST_F(CallbackRegistryTest, InvokePassesUserdata) {
    uint32_t value = 0;
    auto token = registry_.register_callback(increment_callback, &value);

    EXPECT_EQ(registry_.invoke(token->id()), 1u);
    EXPECT_EQ(registry_.invoke(token->id()), 2u);
    EXPECT_EQ(registry_.invoke(token->id()), 3u);
    EXPECT_EQ(value, 3u);
}

TEST_F(CallbackRegistryTest, InvokeInvalidIdReturnsZero) {
    EXPECT_EQ(registry_.invoke(999), 0u);
}

TEST_F(CallbackRegistryTest, InvokeAfterUnregisterReturnsZero) {
    uint32_t value = 42;
    CallbackId id;

    {
        auto token = registry_.register_callback(simple_callback, &value);
        id = token->id();
        EXPECT_EQ(registry_.invoke(id), 42u);
    }  // Token destroyed here

    EXPECT_EQ(registry_.invoke(id), 0u);
}

// ─────────────────────────────────────────────────────────────────────────────
// Token RAII Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(CallbackRegistryTest, TokenDestructorUnregisters) {
    uint32_t value = 42;
    CallbackId id;

    {
        auto token = registry_.register_callback(simple_callback, &value);
        id = token->id();
        EXPECT_TRUE(registry_.is_valid(id));
    }

    EXPECT_FALSE(registry_.is_valid(id));
}

TEST_F(CallbackRegistryTest, TokenMoveTransfersOwnership) {
    uint32_t value = 42;
    auto token1 = registry_.register_callback(simple_callback, &value);
    CallbackId id = token1->id();

    CallbackToken token2 = std::move(*token1);

    EXPECT_FALSE(token1->valid());
    EXPECT_TRUE(token2.valid());
    EXPECT_TRUE(registry_.is_valid(id));
}

TEST_F(CallbackRegistryTest, TokenMoveAssignment) {
    uint32_t v1 = 1, v2 = 2;
    auto token1 = registry_.register_callback(simple_callback, &v1);
    auto token2 = registry_.register_callback(simple_callback, &v2);

    CallbackId id1 = token1->id();
    CallbackId id2 = token2->id();

    *token1 = std::move(*token2);

    EXPECT_FALSE(registry_.is_valid(id1));  // Original callback unregistered
    EXPECT_TRUE(registry_.is_valid(id2));   // Moved callback still valid
    EXPECT_FALSE(token2->valid());
}

TEST_F(CallbackRegistryTest, TokenExplicitRelease) {
    uint32_t value = 42;
    auto token = registry_.register_callback(simple_callback, &value);
    CallbackId id = token->id();

    EXPECT_TRUE(token->valid());
    EXPECT_TRUE(registry_.is_valid(id));

    token->release();

    EXPECT_FALSE(token->valid());
    EXPECT_FALSE(registry_.is_valid(id));
}

TEST_F(CallbackRegistryTest, DoubleReleaseSafe) {
    uint32_t value = 42;
    auto token = registry_.register_callback(simple_callback, &value);

    token->release();
    EXPECT_NO_THROW(token->release());
    EXPECT_FALSE(token->valid());
}

TEST_F(CallbackRegistryTest, DefaultTokenIsInvalid) {
    CallbackToken token;
    EXPECT_FALSE(token.valid());
}

// ─────────────────────────────────────────────────────────────────────────────
// Active Count Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(CallbackRegistryTest, ActiveCountInitiallyZero) {
    EXPECT_EQ(registry_.active_count(), 0u);
}

TEST_F(CallbackRegistryTest, ActiveCountTracksRegistrations) {
    EXPECT_EQ(registry_.active_count(), 0u);

    uint32_t v1 = 1, v2 = 2;
    auto t1 = registry_.register_callback(simple_callback, &v1);
    EXPECT_EQ(registry_.active_count(), 1u);

    auto t2 = registry_.register_callback(simple_callback, &v2);
    EXPECT_EQ(registry_.active_count(), 2u);

    t1->release();
    EXPECT_EQ(registry_.active_count(), 1u);

    t2->release();
    EXPECT_EQ(registry_.active_count(), 0u);
}

// ─────────────────────────────────────────────────────────────────────────────
// Description Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(CallbackRegistryTest, DescriptionIsPreserved) {
    uint32_t value = 42;
    auto token = registry_.register_callback(simple_callback, &value, "MyCallback");

    auto desc = registry_.description(token->id());
    EXPECT_TRUE(desc.has_value());
    EXPECT_EQ(*desc, "MyCallback");
}

TEST_F(CallbackRegistryTest, DescriptionForInvalidIdIsEmpty) {
    auto desc = registry_.description(999);
    EXPECT_FALSE(desc.has_value());
}

TEST_F(CallbackRegistryTest, DescriptionAfterUnregister) {
    uint32_t value = 42;
    CallbackId id;

    {
        auto token = registry_.register_callback(simple_callback, &value, "Test");
        id = token->id();
    }

    auto desc = registry_.description(id);
    EXPECT_FALSE(desc.has_value());
}

// ─────────────────────────────────────────────────────────────────────────────
// Validity Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(CallbackRegistryTest, IsValidForRegistered) {
    uint32_t value = 42;
    auto token = registry_.register_callback(simple_callback, &value);

    EXPECT_TRUE(registry_.is_valid(token->id()));
}

TEST_F(CallbackRegistryTest, IsValidForInvalidId) {
    EXPECT_FALSE(registry_.is_valid(999));
}

TEST_F(CallbackRegistryTest, IsValidForUnregistered) {
    uint32_t value = 42;
    auto token = registry_.register_callback(simple_callback, &value);
    CallbackId id = token->id();

    token->release();

    EXPECT_FALSE(registry_.is_valid(id));
}

// ─────────────────────────────────────────────────────────────────────────────
// Entry Access Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(CallbackRegistryTest, GetEntryReturnsEntry) {
    uint32_t value = 42;
    auto token = registry_.register_callback(simple_callback, &value, "Entry");

    auto* entry = registry_.get_entry(token->id());
    ASSERT_NE(entry, nullptr);
    EXPECT_EQ(entry->handler, simple_callback);
    EXPECT_EQ(entry->userdata, &value);
    EXPECT_STREQ(entry->description, "Entry");
    EXPECT_TRUE(entry->active);
}

TEST_F(CallbackRegistryTest, GetEntryForInvalidIdReturnsNull) {
    EXPECT_EQ(registry_.get_entry(999), nullptr);
}

// ─────────────────────────────────────────────────────────────────────────────
// Slot Reuse Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(CallbackRegistryTest, SlotsAreReused) {
    uint32_t v1 = 1, v2 = 2;

    // Register and unregister first callback
    auto t1 = registry_.register_callback(simple_callback, &v1);
    CallbackId id1 = t1->id();
    t1->release();

    // Register second callback - should reuse the slot
    auto t2 = registry_.register_callback(simple_callback, &v2);
    CallbackId id2 = t2->id();

    EXPECT_EQ(id1, id2);  // Same slot reused
    EXPECT_EQ(registry_.invoke(id2), 2u);
}

// ─────────────────────────────────────────────────────────────────────────────
// Stress Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(CallbackRegistryTest, ManyRegistrations) {
    std::vector<std::optional<CallbackToken>> tokens;
    std::vector<uint32_t> values;

    values.resize(100);
    for (size_t i = 0; i < 100; ++i) {
        values[i] = static_cast<uint32_t>(i);
        auto token = registry_.register_callback(simple_callback, &values[i]);
        tokens.push_back(std::move(token));
    }

    EXPECT_EQ(registry_.active_count(), 100u);

    for (size_t i = 0; i < 100; ++i) {
        EXPECT_EQ(registry_.invoke(tokens[i]->id()), i);
    }
}

TEST_F(CallbackRegistryTest, MaxCallbacksLimit) {
    std::vector<std::optional<CallbackToken>> tokens;
    uint32_t value = 42;

    // Fill to capacity
    for (size_t i = 0; i < CallbackRegistry::MaxCallbacks; ++i) {
        auto token = registry_.register_callback(simple_callback, &value);
        ASSERT_TRUE(token.has_value()) << "Failed at " << i;
        tokens.push_back(std::move(token));
    }

    // Next registration should fail
    auto overflow = registry_.register_callback(simple_callback, &value);
    EXPECT_FALSE(overflow.has_value());
}
