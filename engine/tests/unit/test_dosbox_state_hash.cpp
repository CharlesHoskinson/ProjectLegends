/**
 * @file test_dosbox_state_hash.cpp
 * @brief Unit tests for DOSBox-X state hashing API.
 *
 * Tests the state hash functionality for determinism verification.
 */

#include <gtest/gtest.h>
#include "dosbox/state_hash.h"

#include <cstring>
#include <string>

using namespace dosbox;

// ═══════════════════════════════════════════════════════════════════════════════
// SHA-256 Tests (HashBuilder)
// ═══════════════════════════════════════════════════════════════════════════════

TEST(HashBuilderTest, EmptyStringHash) {
    // SHA-256 of empty string is well-known
    HashBuilder builder;
    StateHash hash = builder.finalize();

    std::string hex = hash_to_hex(hash);
    EXPECT_EQ(hex, "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855");
}

TEST(HashBuilderTest, AbcHash) {
    // SHA-256("abc") is a well-known test vector
    HashBuilder builder;
    builder.update("abc", 3);
    StateHash hash = builder.finalize();

    std::string hex = hash_to_hex(hash);
    EXPECT_EQ(hex, "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
}

TEST(HashBuilderTest, LongStringHash) {
    // SHA-256 of 1 million 'a' characters
    // This tests multiple block processing
    HashBuilder builder;
    std::string chunk(1000, 'a');
    for (int i = 0; i < 1000; ++i) {
        builder.update(chunk.data(), chunk.size());
    }
    StateHash hash = builder.finalize();

    std::string hex = hash_to_hex(hash);
    EXPECT_EQ(hex, "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0");
}

TEST(HashBuilderTest, IncrementalEqualsOneShot) {
    // Incremental hashing should equal one-shot
    std::string data = "The quick brown fox jumps over the lazy dog";

    HashBuilder builder1;
    builder1.update(data.data(), data.size());
    StateHash hash1 = builder1.finalize();

    HashBuilder builder2;
    for (char c : data) {
        builder2.update(&c, 1);
    }
    StateHash hash2 = builder2.finalize();

    EXPECT_EQ(hash1, hash2);
}

TEST(HashBuilderTest, ResetWorks) {
    HashBuilder builder;
    builder.update("test", 4);
    builder.reset();

    // After reset, should produce empty hash
    StateHash hash = builder.finalize();
    std::string hex = hash_to_hex(hash);
    EXPECT_EQ(hex, "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855");
}

TEST(HashBuilderTest, UpdateTypedValue) {
    HashBuilder builder;
    uint32_t value = 0x12345678;
    builder.update(value);
    StateHash hash = builder.finalize();

    // Just verify it produces a hash (exact value depends on endianness)
    EXPECT_NE(hash_to_hex(hash), "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855");
}

// ═══════════════════════════════════════════════════════════════════════════════
// State Hash API Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(StateHashTest, FastModeProducesHash) {
    auto result = get_state_hash(HashMode::Fast);
    ASSERT_TRUE(result.has_value());

    std::string hex = hash_to_hex(result.value());
    EXPECT_EQ(hex.size(), 64u);  // 32 bytes = 64 hex chars
}

TEST(StateHashTest, FullModeProducesHash) {
    auto result = get_state_hash(HashMode::Full);
    ASSERT_TRUE(result.has_value());

    std::string hex = hash_to_hex(result.value());
    EXPECT_EQ(hex.size(), 64u);
}

TEST(StateHashTest, FastAndFullModeDiffer) {
    auto fast = get_state_hash(HashMode::Fast);
    auto full = get_state_hash(HashMode::Full);

    ASSERT_TRUE(fast.has_value());
    ASSERT_TRUE(full.has_value());

    // Fast and full modes should produce different hashes
    EXPECT_NE(fast.value(), full.value());
}

TEST(StateHashTest, DeterministicHash) {
    // Same call should produce same hash
    auto result1 = get_state_hash(HashMode::Fast);
    auto result2 = get_state_hash(HashMode::Fast);

    ASSERT_TRUE(result1.has_value());
    ASSERT_TRUE(result2.has_value());

    EXPECT_EQ(result1.value(), result2.value());
}

TEST(StateHashTest, HashEqualWorks) {
    auto result1 = get_state_hash(HashMode::Fast);
    auto result2 = get_state_hash(HashMode::Fast);
    auto result3 = get_state_hash(HashMode::Full);

    ASSERT_TRUE(result1.has_value());
    ASSERT_TRUE(result2.has_value());
    ASSERT_TRUE(result3.has_value());

    EXPECT_TRUE(hash_equal(result1.value(), result2.value()));
    EXPECT_FALSE(hash_equal(result1.value(), result3.value()));
}

// ═══════════════════════════════════════════════════════════════════════════════
// C API Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(StateHashCApiTest, GetHashWorks) {
    uint8_t hash[DOSBOX_HASH_SIZE];
    int result = dosbox_get_state_hash(hash, DOSBOX_HASH_FAST);

    EXPECT_EQ(result, DOSBOX_OK);
}

TEST(StateHashCApiTest, NullOutputReturnsError) {
    int result = dosbox_get_state_hash(nullptr, DOSBOX_HASH_FAST);
    EXPECT_EQ(result, DOSBOX_ERR_INVALID_ARGUMENT);
}

TEST(StateHashCApiTest, HashToHexWorks) {
    uint8_t hash[DOSBOX_HASH_SIZE];
    char hex[65];

    dosbox_get_state_hash(hash, DOSBOX_HASH_FAST);
    int result = dosbox_hash_to_hex(hash, hex, sizeof(hex));

    EXPECT_EQ(result, DOSBOX_OK);
    EXPECT_EQ(std::strlen(hex), 64u);
}

TEST(StateHashCApiTest, HashToHexSmallBuffer) {
    uint8_t hash[DOSBOX_HASH_SIZE];
    char hex[32];  // Too small

    dosbox_get_state_hash(hash, DOSBOX_HASH_FAST);
    int result = dosbox_hash_to_hex(hash, hex, sizeof(hex));

    EXPECT_EQ(result, DOSBOX_ERR_BUFFER_TOO_SMALL);
}

TEST(StateHashCApiTest, HashToHexNullArgs) {
    uint8_t hash[DOSBOX_HASH_SIZE];
    char hex[65];

    EXPECT_EQ(dosbox_hash_to_hex(nullptr, hex, sizeof(hex)), DOSBOX_ERR_INVALID_ARGUMENT);
    EXPECT_EQ(dosbox_hash_to_hex(hash, nullptr, sizeof(hex)), DOSBOX_ERR_INVALID_ARGUMENT);
}

TEST(StateHashCApiTest, HashEqualWorks) {
    uint8_t hash1[DOSBOX_HASH_SIZE];
    uint8_t hash2[DOSBOX_HASH_SIZE];
    uint8_t hash3[DOSBOX_HASH_SIZE];

    dosbox_get_state_hash(hash1, DOSBOX_HASH_FAST);
    dosbox_get_state_hash(hash2, DOSBOX_HASH_FAST);
    dosbox_get_state_hash(hash3, DOSBOX_HASH_FULL);

    EXPECT_EQ(dosbox_hash_equal(hash1, hash2), 1);
    EXPECT_EQ(dosbox_hash_equal(hash1, hash3), 0);
}

TEST(StateHashCApiTest, HashEqualNullArgs) {
    uint8_t hash[DOSBOX_HASH_SIZE];
    dosbox_get_state_hash(hash, DOSBOX_HASH_FAST);

    EXPECT_EQ(dosbox_hash_equal(nullptr, hash), 0);
    EXPECT_EQ(dosbox_hash_equal(hash, nullptr), 0);
    EXPECT_EQ(dosbox_hash_equal(nullptr, nullptr), 0);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Hash Hex Conversion Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(HashToHexTest, AllZeros) {
    StateHash hash = {};
    std::string hex = hash_to_hex(hash);
    EXPECT_EQ(hex, "0000000000000000000000000000000000000000000000000000000000000000");
}

TEST(HashToHexTest, AllOnes) {
    StateHash hash;
    std::fill(hash.begin(), hash.end(), 0xff);
    std::string hex = hash_to_hex(hash);
    EXPECT_EQ(hex, "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff");
}

TEST(HashToHexTest, MixedBytes) {
    StateHash hash = {};
    hash[0] = 0x01;
    hash[1] = 0x23;
    hash[2] = 0x45;
    hash[3] = 0x67;
    hash[4] = 0x89;
    hash[5] = 0xab;
    hash[6] = 0xcd;
    hash[7] = 0xef;

    std::string hex = hash_to_hex(hash);
    EXPECT_TRUE(hex.starts_with("0123456789abcdef"));
}

// ═══════════════════════════════════════════════════════════════════════════════
// Sprint 2 Phase 1: Explicit Context API Tests
// ═══════════════════════════════════════════════════════════════════════════════

#include "dosbox/dosbox_context.h"

class ExplicitContextHashTest : public ::testing::Test {
protected:
    void SetUp() override {
        ctx_ = std::make_unique<DOSBoxContext>();
    }

    void TearDown() override {
        ctx_.reset();
    }

    std::unique_ptr<DOSBoxContext> ctx_;
};

TEST_F(ExplicitContextHashTest, NullContextReturnsError) {
    auto result = get_state_hash(nullptr, HashMode::Fast);

    ASSERT_FALSE(result.has_value());
    EXPECT_EQ(result.error().code(), ErrorCode::InvalidArgument);
}

TEST_F(ExplicitContextHashTest, ValidContextProducesHash) {
    auto result = get_state_hash(ctx_.get(), HashMode::Fast);

    ASSERT_TRUE(result.has_value());
    std::string hex = hash_to_hex(result.value());
    EXPECT_EQ(hex.size(), 64u);
}

TEST_F(ExplicitContextHashTest, ExplicitContextMatchesTransitionalApi) {
    // Set up thread-local context for transitional API
    set_current_context(ctx_.get());

    auto explicit_result = get_state_hash(ctx_.get(), HashMode::Fast);
    auto transitional_result = get_state_hash(HashMode::Fast);

    set_current_context(nullptr);

    ASSERT_TRUE(explicit_result.has_value());
    ASSERT_TRUE(transitional_result.has_value());

    // Both should produce identical hashes for the same context
    EXPECT_EQ(explicit_result.value(), transitional_result.value());
}

TEST_F(ExplicitContextHashTest, DifferentContextsProduceDifferentHashes) {
    auto ctx2 = std::make_unique<DOSBoxContext>();

    // Modify one context to ensure different state
    ctx_->timing.total_cycles = 1000;
    ctx2->timing.total_cycles = 2000;

    auto hash1 = get_state_hash(ctx_.get(), HashMode::Fast);
    auto hash2 = get_state_hash(ctx2.get(), HashMode::Fast);

    ASSERT_TRUE(hash1.has_value());
    ASSERT_TRUE(hash2.has_value());

    // Different state should produce different hashes
    EXPECT_NE(hash1.value(), hash2.value());
}

TEST_F(ExplicitContextHashTest, SameStateSameHash) {
    auto ctx2 = std::make_unique<DOSBoxContext>();

    // Both contexts start with identical default state
    auto hash1 = get_state_hash(ctx_.get(), HashMode::Fast);
    auto hash2 = get_state_hash(ctx2.get(), HashMode::Fast);

    ASSERT_TRUE(hash1.has_value());
    ASSERT_TRUE(hash2.has_value());

    // Same state should produce same hash (determinism)
    EXPECT_EQ(hash1.value(), hash2.value());
}

TEST_F(ExplicitContextHashTest, FastAndFullModesDifferWithExplicitContext) {
    auto fast = get_state_hash(ctx_.get(), HashMode::Fast);
    auto full = get_state_hash(ctx_.get(), HashMode::Full);

    ASSERT_TRUE(fast.has_value());
    ASSERT_TRUE(full.has_value());

    EXPECT_NE(fast.value(), full.value());
}

TEST_F(ExplicitContextHashTest, StateChangeChangesHash) {
    auto hash_before = get_state_hash(ctx_.get(), HashMode::Fast);
    ASSERT_TRUE(hash_before.has_value());

    // Modify state
    ctx_->cpu_state.cycles = 12345;

    auto hash_after = get_state_hash(ctx_.get(), HashMode::Fast);
    ASSERT_TRUE(hash_after.has_value());

    EXPECT_NE(hash_before.value(), hash_after.value());
}

// Test that explicit context API works without thread-local context set
TEST_F(ExplicitContextHashTest, WorksWithoutThreadLocalContext) {
    // Ensure no thread-local context is set
    set_current_context(nullptr);
    ASSERT_FALSE(has_current_context());

    // Explicit API should still work
    auto result = get_state_hash(ctx_.get(), HashMode::Fast);

    ASSERT_TRUE(result.has_value());
    std::string hex = hash_to_hex(result.value());
    EXPECT_EQ(hex.size(), 64u);
}
