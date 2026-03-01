// SPDX-License-Identifier: MIT
//
// Portable little-endian wire format read/write helpers.
// Independently written for the legends_ipc library (MIT).
// All functions use byte shifts for full cross-platform portability.
#ifndef LEGENDS_IPC_WIRE_FORMAT_H
#define LEGENDS_IPC_WIRE_FORMAT_H

#include <cstdint>
#include <span>
#include <gsl-lite/gsl-lite.hpp>

namespace legends_ipc::wire {

// ── Write helpers (host -> little-endian wire) ──────────────────────────────

inline void write_u8(std::span<uint8_t> buf, size_t offset, uint8_t v) {
    gsl_Expects(offset < buf.size());
    buf[offset] = v;
}

inline void write_u16_le(std::span<uint8_t> buf, size_t offset, uint16_t v) {
    gsl_Expects(offset + 2 <= buf.size());
    buf[offset]     = static_cast<uint8_t>(v & 0xFF);
    buf[offset + 1] = static_cast<uint8_t>((v >> 8) & 0xFF);
}

inline void write_u32_le(std::span<uint8_t> buf, size_t offset, uint32_t v) {
    gsl_Expects(offset + 4 <= buf.size());
    buf[offset]     = static_cast<uint8_t>(v & 0xFF);
    buf[offset + 1] = static_cast<uint8_t>((v >> 8) & 0xFF);
    buf[offset + 2] = static_cast<uint8_t>((v >> 16) & 0xFF);
    buf[offset + 3] = static_cast<uint8_t>((v >> 24) & 0xFF);
}

inline void write_u64_le(std::span<uint8_t> buf, size_t offset, uint64_t v) {
    gsl_Expects(offset + 8 <= buf.size());
    for (int i = 0; i < 8; ++i)
        buf[offset + i] = static_cast<uint8_t>((v >> (i * 8)) & 0xFF);
}

inline void write_i16_le(std::span<uint8_t> buf, size_t offset, int16_t v) {
    write_u16_le(buf, offset, static_cast<uint16_t>(v));
}

inline void write_i32_le(std::span<uint8_t> buf, size_t offset, int32_t v) {
    write_u32_le(buf, offset, static_cast<uint32_t>(v));
}

inline void write_i64_le(std::span<uint8_t> buf, size_t offset, int64_t v) {
    write_u64_le(buf, offset, static_cast<uint64_t>(v));
}

inline void write_bool(std::span<uint8_t> buf, size_t offset, bool v) {
    gsl_Expects(offset < buf.size());
    buf[offset] = v ? 1 : 0;
}

// ── Read helpers (little-endian wire -> host) ───────────────────────────────

inline uint8_t read_u8(std::span<const uint8_t> buf, size_t offset) {
    gsl_Expects(offset < buf.size());
    return buf[offset];
}

inline uint16_t read_u16_le(std::span<const uint8_t> buf, size_t offset) {
    gsl_Expects(offset + 2 <= buf.size());
    return static_cast<uint16_t>(buf[offset]) |
           (static_cast<uint16_t>(buf[offset + 1]) << 8);
}

inline uint32_t read_u32_le(std::span<const uint8_t> buf, size_t offset) {
    gsl_Expects(offset + 4 <= buf.size());
    return static_cast<uint32_t>(buf[offset]) |
           (static_cast<uint32_t>(buf[offset + 1]) << 8) |
           (static_cast<uint32_t>(buf[offset + 2]) << 16) |
           (static_cast<uint32_t>(buf[offset + 3]) << 24);
}

inline uint64_t read_u64_le(std::span<const uint8_t> buf, size_t offset) {
    gsl_Expects(offset + 8 <= buf.size());
    uint64_t v = 0;
    for (int i = 0; i < 8; ++i)
        v |= static_cast<uint64_t>(buf[offset + i]) << (i * 8);
    return v;
}

inline int16_t read_i16_le(std::span<const uint8_t> buf, size_t offset) {
    return static_cast<int16_t>(read_u16_le(buf, offset));
}

inline int32_t read_i32_le(std::span<const uint8_t> buf, size_t offset) {
    return static_cast<int32_t>(read_u32_le(buf, offset));
}

inline int64_t read_i64_le(std::span<const uint8_t> buf, size_t offset) {
    return static_cast<int64_t>(read_u64_le(buf, offset));
}

inline bool read_bool(std::span<const uint8_t> buf, size_t offset) {
    gsl_Expects(offset < buf.size());
    return buf[offset] != 0;
}

} // namespace legends_ipc::wire

#endif // LEGENDS_IPC_WIRE_FORMAT_H
