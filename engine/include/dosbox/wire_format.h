/**
 * @file wire_format.h
 * @brief Portable little-endian wire format read/write helpers.
 *
 * Extracted from legends_embed_api.cpp for reuse across engine
 * and legends layers. All functions use byte shifts for full
 * portability across architectures.
 *
 * @copyright GPL-2.0-or-later
 */

#ifndef DOSBOX_WIRE_FORMAT_H
#define DOSBOX_WIRE_FORMAT_H

#include <cstdint>

namespace dosbox::wire {

// ─────────────────────────────────────────────────────────────────────────────
// Write helpers (host -> little-endian wire)
// ─────────────────────────────────────────────────────────────────────────────

inline void write_u8(uint8_t* p, uint8_t v) { *p = v; }

inline void write_u16_le(uint8_t* p, uint16_t v) {
    p[0] = static_cast<uint8_t>(v & 0xFF);
    p[1] = static_cast<uint8_t>((v >> 8) & 0xFF);
}

inline void write_u32_le(uint8_t* p, uint32_t v) {
    p[0] = static_cast<uint8_t>(v & 0xFF);
    p[1] = static_cast<uint8_t>((v >> 8) & 0xFF);
    p[2] = static_cast<uint8_t>((v >> 16) & 0xFF);
    p[3] = static_cast<uint8_t>((v >> 24) & 0xFF);
}

inline void write_u64_le(uint8_t* p, uint64_t v) {
    for (int i = 0; i < 8; ++i)
        p[i] = static_cast<uint8_t>((v >> (i * 8)) & 0xFF);
}

inline void write_i16_le(uint8_t* p, int16_t v) {
    write_u16_le(p, static_cast<uint16_t>(v));
}

inline void write_i32_le(uint8_t* p, int32_t v) {
    write_u32_le(p, static_cast<uint32_t>(v));
}

inline void write_i64_le(uint8_t* p, int64_t v) {
    write_u64_le(p, static_cast<uint64_t>(v));
}

inline void write_bool(uint8_t* p, bool v) { *p = v ? 1 : 0; }

// ─────────────────────────────────────────────────────────────────────────────
// Read helpers (little-endian wire -> host)
// ─────────────────────────────────────────────────────────────────────────────

inline uint8_t read_u8(const uint8_t* p) { return *p; }

inline uint16_t read_u16_le(const uint8_t* p) {
    return static_cast<uint16_t>(p[0]) |
           (static_cast<uint16_t>(p[1]) << 8);
}

inline uint32_t read_u32_le(const uint8_t* p) {
    return static_cast<uint32_t>(p[0]) |
           (static_cast<uint32_t>(p[1]) << 8) |
           (static_cast<uint32_t>(p[2]) << 16) |
           (static_cast<uint32_t>(p[3]) << 24);
}

inline uint64_t read_u64_le(const uint8_t* p) {
    uint64_t v = 0;
    for (int i = 0; i < 8; ++i)
        v |= static_cast<uint64_t>(p[i]) << (i * 8);
    return v;
}

inline int16_t read_i16_le(const uint8_t* p) {
    return static_cast<int16_t>(read_u16_le(p));
}

inline int32_t read_i32_le(const uint8_t* p) {
    return static_cast<int32_t>(read_u32_le(p));
}

inline int64_t read_i64_le(const uint8_t* p) {
    return static_cast<int64_t>(read_u64_le(p));
}

inline bool read_bool(const uint8_t* p) { return *p != 0; }

} // namespace dosbox::wire

#endif // DOSBOX_WIRE_FORMAT_H
