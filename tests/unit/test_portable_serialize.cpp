/**
 * @file test_portable_serialize.cpp
 * @brief Unit tests for portable serialization.
 *
 * Tests that save states are portable across platforms by verifying
 * known byte sequences and round-trip consistency.
 */

#include <gtest/gtest.h>
#include <legends/legends_embed.h>
#include <pal/platform.h>
#include <cstring>
#include <vector>

class PortableSerializeTest : public ::testing::Test {
protected:
    legends_handle h_ = nullptr;

    void SetUp() override {
        pal::Platform::shutdown();
        pal::Platform::initialize(pal::Backend::Headless);
        legends_destroy(reinterpret_cast<legends_handle>(1));
        legends_create(nullptr, &h_);
        legends_step_ms(h_, 50, nullptr);
    }

    void TearDown() override {
        if (h_) legends_destroy(h_);
        pal::Platform::shutdown();
    }

    std::vector<uint8_t> save_state() {
        size_t size;
        legends_save_state(h_, nullptr, 0, &size);
        std::vector<uint8_t> state(size);
        legends_save_state(h_, state.data(), size, &size);
        return state;
    }
};

// Save state header has correct magic and version
TEST_F(PortableSerializeTest, HeaderMagicAndVersion) {
    auto state = save_state();
    ASSERT_GE(state.size(), 12u);

    // Magic: "DBXS" = 0x53584244 in little-endian
    uint32_t magic;
    std::memcpy(&magic, state.data(), 4);
    EXPECT_EQ(magic, 0x53584244u);

    // Version: 3
    uint32_t version;
    std::memcpy(&version, state.data() + 4, 4);
    EXPECT_EQ(version, 3u);
}

// Input events are serialized in portable format
TEST_F(PortableSerializeTest, InputEventsSerialized) {
    // Queue some input events
    legends_key_event(h_, 0x1E, 1);      // Key A down
    legends_mouse_event(h_, 10, -5, 1);  // Mouse move + left button
    legends_key_event(h_, 0x1E, 0);      // Key A up

    // Don't step - events are pending in queue

    auto state = save_state();

    // Load and verify the events are preserved
    legends_destroy(h_);
    legends_create(nullptr, &h_);
    legends_step_ms(h_, 50, nullptr);

    EXPECT_EQ(legends_load_state(h_, state.data(), state.size()), LEGENDS_OK);

    // Step to process the restored events
    uint8_t hash_before[32];
    legends_get_state_hash(h_, hash_before);

    legends_step_ms(h_, 100, nullptr);

    uint8_t hash_after[32];
    legends_get_state_hash(h_, hash_after);

    // State should change from processing input
    EXPECT_NE(memcmp(hash_before, hash_after, 32), 0);
}

// Verify wire format for a single key event
TEST_F(PortableSerializeTest, InputEventWireFormat) {
    // Queue a single key event
    legends_key_event(h_, 0x1E, 1);  // 'A' down

    auto state = save_state();

    struct SaveStateHeader {
        uint32_t magic;
        uint32_t version;
        uint32_t total_size;
        uint32_t checksum;
        uint32_t time_offset;
        uint32_t cpu_offset;
        uint32_t pic_offset;
        uint32_t dma_offset;
        uint32_t event_queue_offset;
        uint32_t input_offset;
        uint32_t frame_offset;
        uint32_t engine_offset;
        uint32_t engine_size;
        uint32_t _reserved[3];
    };
    struct SaveStateInputHeader {
        uint32_t event_count;
        uint32_t next_sequence_lo;
        uint32_t next_sequence_hi;
        uint32_t _reserved;
    };
    static_assert(sizeof(SaveStateHeader) == 64, "SaveStateHeader size must be 64");

    const auto* header = reinterpret_cast<const SaveStateHeader*>(state.data());
    const auto* input = reinterpret_cast<const SaveStateInputHeader*>(
        state.data() + header->input_offset);
    ASSERT_EQ(input->event_count, 1u);

    const uint8_t* evt = state.data() + header->input_offset + sizeof(SaveStateInputHeader);
    EXPECT_EQ(evt[0], 0u);  // InputEventType::Key

    uint64_t seq = 0;
    std::memcpy(&seq, evt + 8, sizeof(seq));
    EXPECT_EQ(seq, 0u);

    EXPECT_EQ(evt[16], 0x1Eu);  // scancode
    EXPECT_EQ(evt[17], 1u);     // is_down
    EXPECT_EQ(evt[18], 0u);     // is_extended
}

// DMA state round-trips correctly
TEST_F(PortableSerializeTest, DMAStateRoundTrip) {
    // Save, load, save again - should produce identical results
    auto state1 = save_state();

    EXPECT_EQ(legends_load_state(h_, state1.data(), state1.size()), LEGENDS_OK);

    auto state2 = save_state();

    // States should be identical (same data, same checksum)
    EXPECT_EQ(state1.size(), state2.size());

    // Compare checksums (at offset 12 in header)
    uint32_t checksum1, checksum2;
    std::memcpy(&checksum1, state1.data() + 12, 4);
    std::memcpy(&checksum2, state2.data() + 12, 4);
    EXPECT_EQ(checksum1, checksum2);
}

// Unified input queue preserves sequence numbers
TEST_F(PortableSerializeTest, InputSequencePreserved) {
    // Queue events in specific order
    legends_key_event(h_, 0x01, 1);  // Esc down
    legends_key_event(h_, 0x01, 0);  // Esc up
    legends_key_event(h_, 0x02, 1);  // 1 down
    legends_key_event(h_, 0x02, 0);  // 1 up

    // Save with pending events
    auto state = save_state();

    // Reload and step
    legends_destroy(h_);
    legends_create(nullptr, &h_);
    legends_step_ms(h_, 50, nullptr);
    EXPECT_EQ(legends_load_state(h_, state.data(), state.size()), LEGENDS_OK);

    uint8_t hash1[32];
    legends_step_ms(h_, 100, nullptr);
    legends_get_state_hash(h_, hash1);

    // Reload again and step - should get same hash (determinism)
    EXPECT_EQ(legends_load_state(h_, state.data(), state.size()), LEGENDS_OK);

    uint8_t hash2[32];
    legends_step_ms(h_, 100, nullptr);
    legends_get_state_hash(h_, hash2);

    EXPECT_EQ(memcmp(hash1, hash2, 32), 0);
}

// Checksum integrity
TEST_F(PortableSerializeTest, ChecksumIntegrity) {
    auto state = save_state();

    // Corrupt one byte in the data section (after header)
    if (state.size() > 100) {
        state[100] ^= 0xFF;
    }

    // Load should fail with checksum mismatch
    auto err = legends_load_state(h_, state.data(), state.size());
    EXPECT_EQ(err, LEGENDS_ERR_INVALID_STATE);
}

// Header total_size is correct
TEST_F(PortableSerializeTest, HeaderTotalSizeCorrect) {
    auto state = save_state();

    // Read total_size from header (offset 8)
    uint32_t total_size;
    std::memcpy(&total_size, state.data() + 8, 4);

    // Should equal actual buffer size used
    EXPECT_EQ(static_cast<size_t>(total_size), state.size());
}
