/**
 * @file zero_rle.h
 * @brief Zero-byte run-length encoding codec (header-only).
 *
 * Simple binary compression for mostly-zero data (e.g., DOS RAM).
 * Non-zero bytes pass through literally. Zero bytes are encoded as
 * an escape sequence: 0x00 HI LO where count=(HI<<8)|LO:
 *   - count=0: literal single zero byte
 *   - count=1-65535: that many consecutive zero bytes
 *
 * Achieves ~10:1 on typical DOS RAM (mostly zero).
 * No external dependencies.
 *
 * @copyright GPL-2.0-or-later
 */

#ifndef DOSBOX_ZERO_RLE_H
#define DOSBOX_ZERO_RLE_H

#include <cstddef>
#include <cstdint>

namespace dosbox {

/**
 * @brief Worst-case output size for zero_rle_encode.
 *
 * Worst case: alternating non-zero and single-zero bytes.
 * Each non-zero → 1 byte, each isolated zero → 3 bytes.
 * For N input bytes: up to 2*N output bytes + 3 for final run.
 */
inline size_t zero_rle_bound(size_t n) {
    return n * 2 + 3;
}

/**
 * @brief Encode data using zero-byte RLE compression.
 *
 * @param src   Source data
 * @param len   Source length in bytes
 * @param dst   Destination buffer (must be at least zero_rle_bound(len) bytes)
 * @param cap   Destination buffer capacity
 * @return Bytes written to dst, or 0 if dst is too small
 */
inline size_t zero_rle_encode(const uint8_t* src, size_t len,
                              uint8_t* dst, size_t cap) {
    if (!src || !dst) return 0;

    size_t out = 0;

    for (size_t i = 0; i < len; ) {
        if (src[i] != 0) {
            // Literal non-zero byte
            if (out >= cap) return 0;
            dst[out++] = src[i++];
        } else {
            // Count consecutive zeros
            size_t run_start = i;
            while (i < len && src[i] == 0 && (i - run_start) < 65535) {
                ++i;
            }
            size_t count = i - run_start;

            // Emit escape: 0x00 HI LO
            if (out + 3 > cap) return 0;
            dst[out++] = 0x00;
            dst[out++] = static_cast<uint8_t>((count >> 8) & 0xFF);
            dst[out++] = static_cast<uint8_t>(count & 0xFF);
        }
    }

    return out;
}

/**
 * @brief Decode zero-byte RLE compressed data.
 *
 * @param src   Compressed source data
 * @param len   Compressed data length
 * @param dst   Destination buffer for decompressed output
 * @param cap   Destination buffer capacity
 * @return Bytes written to dst, or 0 on error (truncated stream or overflow)
 */
inline size_t zero_rle_decode(const uint8_t* src, size_t len,
                              uint8_t* dst, size_t cap) {
    if (!src || !dst) return 0;

    size_t out = 0;

    for (size_t i = 0; i < len; ) {
        if (src[i] != 0) {
            // Literal non-zero byte
            if (out >= cap) return 0;
            dst[out++] = src[i++];
        } else {
            // Escape sequence: 0x00 HI LO
            if (i + 2 >= len) return 0;  // Truncated stream
            uint16_t count = static_cast<uint16_t>(
                (static_cast<uint16_t>(src[i + 1]) << 8) | src[i + 2]);
            i += 3;

            if (count == 0) {
                // Literal zero byte
                if (out >= cap) return 0;
                dst[out++] = 0x00;
            } else {
                // Run of count zeros
                if (out + count > cap) return 0;
                for (uint16_t j = 0; j < count; ++j) {
                    dst[out++] = 0x00;
                }
            }
        }
    }

    return out;
}

} // namespace dosbox

#endif // DOSBOX_ZERO_RLE_H
