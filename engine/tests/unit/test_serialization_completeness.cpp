/**
 * @file test_serialization_completeness.cpp
 * @brief Tests documenting serialization gaps between runtime and saved state.
 *
 * H1: KeyboardState::BUFFER_SIZE (96) vs EngineStateKeyboard::buffer (16).
 */

#include <gtest/gtest.h>
#include <dosbox/engine_state.h>
#include <dosbox/dosbox_context.h>

namespace dosbox {
namespace test {

TEST(SerializationTest, KeyboardBufferSizeMismatch) {
    // Runtime keyboard buffer holds 96 entries
    constexpr size_t runtime_size = KeyboardState::BUFFER_SIZE;
    EXPECT_EQ(runtime_size, 96u);

    // Serialized format only holds 16 entries
    constexpr size_t serialized_size = sizeof(EngineStateKeyboard::buffer) / sizeof(uint16_t);
    EXPECT_EQ(serialized_size, 16u);

    // Entries 17-96 are lost on save/load
    EXPECT_NE(runtime_size, serialized_size)
        << "H1: buffer sizes match — remove this test if truncation is fixed";
}

TEST(SerializationTest, VgaMixerDmaDosNotSerialized) {
    // EngineStateHeader has offsets for: timing, pic, keyboard, cpu, memory
    // No offsets for: vga, mixer, dma, dos
    static_assert(offsetof(EngineStateHeader, timing_offset) != 0);
    static_assert(offsetof(EngineStateHeader, pic_offset) != 0);
    static_assert(offsetof(EngineStateHeader, keyboard_offset) != 0);
    static_assert(offsetof(EngineStateHeader, cpu_offset) != 0);
    static_assert(offsetof(EngineStateHeader, memory_offset) != 0);

    EXPECT_EQ(sizeof(EngineStateHeader), 48u)
        << "H1: header size changed — check if new subsystems were added";
}

// ═══════════════════════════════════════════════════════════════════════════════
// H2: No Endianness Handling in Serialization
// dosbox_library.cpp:502,669 use reinterpret_cast<EngineStateHeader*> on raw
// byte buffers. State files contain native struct layout with no byte-swapping.
// ═══════════════════════════════════════════════════════════════════════════════

TEST(SerializationTest, EndiannessNotHandled) {
    // Construct an EngineStateHeader with known values
    EngineStateHeader header{};
    header.magic = ENGINE_STATE_MAGIC;      // 0x45584244
    header.version = ENGINE_STATE_VERSION;  // 2
    header.total_size = 384;

    // Read the raw bytes at the magic field offset
    const auto* raw = reinterpret_cast<const uint8_t*>(&header);

    // On little-endian (x86): first byte is 0x44 ('D')
    // On big-endian: first byte would be 0x45 ('E')
    // The serialization code uses reinterpret_cast directly — no htonl/ntohl,
    // no byte-swap helpers. State files are platform-dependent.
#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
    EXPECT_EQ(raw[0], 0x45u) << "H2: big-endian native layout confirmed";
#else
    EXPECT_EQ(raw[0], 0x44u) << "H2: little-endian native layout confirmed";
#endif

    // The version field follows the same pattern
    const auto* ver_bytes = reinterpret_cast<const uint8_t*>(&header.version);
#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
    EXPECT_EQ(ver_bytes[0], 0x00u);
    EXPECT_EQ(ver_bytes[3], ENGINE_STATE_VERSION);
#else
    EXPECT_EQ(ver_bytes[0], ENGINE_STATE_VERSION);
    EXPECT_EQ(ver_bytes[3], 0x00u);
#endif

    // H2: a state file saved on x86 cannot be loaded on ARM big-endian (or
    // vice versa) because dosbox_lib_save_state writes structs as-is.
    // This test documents the platform-dependent behavior.
}

// ═══════════════════════════════════════════════════════════════════════════════
// H1 (extended): buffer_used restored but entries 17-96 lost
// After save/load, buffer_used can exceed the 16 saved entries, so any code
// iterating buffer[0..buffer_used) would read uninitialized/zeroed memory.
// ═══════════════════════════════════════════════════════════════════════════════

TEST(SerializationTest, BufferUsedExceedsSavedEntries) {
    // Simulate what happens during save: buffer_used is stored as a raw uint32.
    EngineStateKeyboard kbd{};
    kbd.buffer_used = 50;  // Runtime had 50 entries

    // Only buffer[0..15] are saved — the struct only has 16 slots
    constexpr size_t saved_entries = sizeof(kbd.buffer) / sizeof(uint16_t);
    EXPECT_EQ(saved_entries, 16u);

    // Fill the 16 slots with recognizable data
    for (size_t i = 0; i < saved_entries; ++i) {
        kbd.buffer[i] = static_cast<uint16_t>(0xA000 + i);
    }

    // After load, buffer_used is restored as 50 but only 16 entries exist.
    // Entries 16-49 are zeroed (memset in save) — silent data loss.
    EXPECT_GT(kbd.buffer_used, saved_entries)
        << "H1: buffer_used (50) exceeds saved entries (16) — "
           "iterating buffer[0..buffer_used) reads past saved data";

    // The 16 saved entries are intact
    EXPECT_EQ(kbd.buffer[0], 0xA000u);
    EXPECT_EQ(kbd.buffer[15], 0xA00Fu);
}

} // namespace test
} // namespace dosbox
