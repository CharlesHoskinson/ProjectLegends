/* stb_image_write - v1.16 - public domain - http://nothings.org/stb
 *
 * Writes out PNG/BMP/TGA/JPG/HDR images from memory.
 *
 * This is a minimal extraction of stbi_write_png for Project Legends.
 * Only PNG output is implemented (the only format used by capture.cpp).
 *
 * Original by Sean Barrett and contributors.
 * Public domain / MIT license — see end of file.
 *
 * USAGE:
 *   In ONE C/C++ source file, define STB_IMAGE_WRITE_IMPLEMENTATION
 *   before including this header.
 */

#ifndef INCLUDE_STB_IMAGE_WRITE_H
#define INCLUDE_STB_IMAGE_WRITE_H

#ifdef __cplusplus
extern "C" {
#endif

#ifndef STBIW_ASSERT
#include <assert.h>
#define STBIW_ASSERT(x) assert(x)
#endif

// Write a PNG file. comp = 1 (gray), 2 (gray+alpha), 3 (RGB), 4 (RGBA).
// stride_in_bytes = 0 means packed (width * comp).
// Returns 0 on failure, non-zero on success.
extern int stbi_write_png(const char *filename, int w, int h, int comp,
                          const void *data, int stride_in_bytes);

#ifdef __cplusplus
}
#endif

// ─────────────────────────────────────────────────────────────────────────────

#ifdef STB_IMAGE_WRITE_IMPLEMENTATION

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

// ── CRC32 for PNG chunks ─────────────────────────────────────────────────────

static unsigned int stbiw__crc32_table[256];
static int stbiw__crc32_inited = 0;

static void stbiw__init_crc32(void) {
    unsigned int i, j, c;
    for (i = 0; i < 256; i++) {
        c = i;
        for (j = 0; j < 8; j++)
            c = (c >> 1) ^ ((c & 1) ? 0xEDB88320u : 0);
        stbiw__crc32_table[i] = c;
    }
    stbiw__crc32_inited = 1;
}

static unsigned int stbiw__crc32(const unsigned char *buf, int len) {
    unsigned int crc = 0xFFFFFFFFu;
    int i;
    if (!stbiw__crc32_inited) stbiw__init_crc32();
    for (i = 0; i < len; i++)
        crc = (crc >> 8) ^ stbiw__crc32_table[(crc ^ buf[i]) & 0xFF];
    return crc ^ 0xFFFFFFFFu;
}

// ── Adler-32 for zlib ────────────────────────────────────────────────────────

static unsigned int stbiw__adler32(unsigned int adler, const unsigned char *buf, int len) {
    unsigned int s1 = adler & 0xFFFF;
    unsigned int s2 = (adler >> 16) & 0xFFFF;
    int i;
    int blocklen;
    while (len > 0) {
        blocklen = len < 5552 ? len : 5552;
        len -= blocklen;
        for (i = 0; i < blocklen; i++) {
            s1 += buf[i];
            s2 += s1;
        }
        buf += blocklen;
        s1 %= 65521;
        s2 %= 65521;
    }
    return (s2 << 16) | s1;
}

// ── Write helpers ────────────────────────────────────────────────────────────

static void stbiw__put32be(unsigned char *p, unsigned int v) {
    p[0] = (unsigned char)(v >> 24);
    p[1] = (unsigned char)(v >> 16);
    p[2] = (unsigned char)(v >> 8);
    p[3] = (unsigned char)(v);
}

// ── zlib stored (uncompressed) wrapper ───────────────────────────────────────
// For simplicity we use zlib stored blocks (no compression).
// This keeps the code small while producing valid PNG files.

static unsigned char *stbiw__zlib_stored(const unsigned char *data, int data_len, int *out_len) {
    // zlib header (2 bytes) + stored blocks + adler32 (4 bytes)
    // Each stored block: 5 byte header + up to 65535 data bytes
    int num_blocks = (data_len + 65534) / 65535;
    int total = 2 + num_blocks * 5 + data_len + 4;
    unsigned char *out = (unsigned char *)malloc((size_t)total);
    if (!out) return NULL;

    int pos = 0;
    out[pos++] = 0x78; // zlib header: CMF
    out[pos++] = 0x01; // zlib header: FLG (no dict, level 0)

    int remaining = data_len;
    int offset = 0;
    while (remaining > 0) {
        int block_len = remaining > 65535 ? 65535 : remaining;
        int last = (remaining <= 65535) ? 1 : 0;
        out[pos++] = (unsigned char)last;
        out[pos++] = (unsigned char)(block_len & 0xFF);
        out[pos++] = (unsigned char)((block_len >> 8) & 0xFF);
        out[pos++] = (unsigned char)(~block_len & 0xFF);
        out[pos++] = (unsigned char)((~block_len >> 8) & 0xFF);
        memcpy(out + pos, data + offset, (size_t)block_len);
        pos += block_len;
        offset += block_len;
        remaining -= block_len;
    }

    unsigned int adler = stbiw__adler32(1, data, data_len);
    stbiw__put32be(out + pos, adler);
    pos += 4;

    *out_len = pos;
    return out;
}

// ── PNG chunk writing ────────────────────────────────────────────────────────

static int stbiw__write_png_chunk(FILE *f, const char *type,
                                   const unsigned char *data, int data_len) {
    unsigned char len_buf[4];
    unsigned char type_buf[4];
    unsigned char crc_buf[4];

    stbiw__put32be(len_buf, (unsigned int)data_len);
    memcpy(type_buf, type, 4);

    if (fwrite(len_buf, 1, 4, f) != 4) return 0;
    if (fwrite(type_buf, 1, 4, f) != 4) return 0;
    if (data_len > 0 && data) {
        if (fwrite(data, 1, (size_t)data_len, f) != (size_t)data_len) return 0;
    }

    // CRC covers type + data
    unsigned int crc = 0xFFFFFFFFu;
    if (!stbiw__crc32_inited) stbiw__init_crc32();
    {
        int i;
        for (i = 0; i < 4; i++)
            crc = (crc >> 8) ^ stbiw__crc32_table[(crc ^ type_buf[i]) & 0xFF];
        for (i = 0; i < data_len; i++)
            crc = (crc >> 8) ^ stbiw__crc32_table[(crc ^ data[i]) & 0xFF];
    }
    crc ^= 0xFFFFFFFFu;
    stbiw__put32be(crc_buf, crc);
    if (fwrite(crc_buf, 1, 4, f) != 4) return 0;

    return 1;
}

// ── stbi_write_png ───────────────────────────────────────────────────────────

int stbi_write_png(const char *filename, int w, int h, int comp,
                   const void *data, int stride_in_bytes) {
    FILE *f;
    int i;

    if (!filename || !data || w <= 0 || h <= 0 || comp < 1 || comp > 4)
        return 0;

    if (stride_in_bytes == 0)
        stride_in_bytes = w * comp;

#if defined(_MSC_VER) && _MSC_VER >= 1400
    if (fopen_s(&f, filename, "wb") != 0) return 0;
#else
    f = fopen(filename, "wb");
#endif
    if (!f) return 0;

    // PNG signature
    {
        static const unsigned char sig[8] = {137, 80, 78, 71, 13, 10, 26, 10};
        if (fwrite(sig, 1, 8, f) != 8) { fclose(f); return 0; }
    }

    // IHDR
    {
        unsigned char ihdr[13];
        stbiw__put32be(ihdr + 0, (unsigned int)w);
        stbiw__put32be(ihdr + 4, (unsigned int)h);
        ihdr[8] = 8; // bit depth
        ihdr[9] = (unsigned char)(comp >= 3 ? (comp == 4 ? 6 : 2) : (comp == 2 ? 4 : 0));
        ihdr[10] = 0; // compression
        ihdr[11] = 0; // filter
        ihdr[12] = 0; // interlace
        if (!stbiw__write_png_chunk(f, "IHDR", ihdr, 13)) { fclose(f); return 0; }
    }

    // IDAT — build filtered scanlines then zlib-wrap
    {
        int scanline_bytes = w * comp;
        int filtered_len = h * (1 + scanline_bytes); // filter byte + row data
        unsigned char *filtered = (unsigned char *)malloc((size_t)filtered_len);
        if (!filtered) { fclose(f); return 0; }

        for (i = 0; i < h; i++) {
            filtered[i * (1 + scanline_bytes)] = 0; // filter: None
            memcpy(filtered + i * (1 + scanline_bytes) + 1,
                   (const unsigned char *)data + i * stride_in_bytes,
                   (size_t)scanline_bytes);
        }

        int zlib_len = 0;
        unsigned char *zlib_data = stbiw__zlib_stored(filtered, filtered_len, &zlib_len);
        free(filtered);

        if (!zlib_data) { fclose(f); return 0; }
        int ok = stbiw__write_png_chunk(f, "IDAT", zlib_data, zlib_len);
        free(zlib_data);
        if (!ok) { fclose(f); return 0; }
    }

    // IEND
    if (!stbiw__write_png_chunk(f, "IEND", NULL, 0)) { fclose(f); return 0; }

    fclose(f);
    return 1;
}

#endif // STB_IMAGE_WRITE_IMPLEMENTATION
#endif // INCLUDE_STB_IMAGE_WRITE_H

/*
 * This software is available under 2 licenses — choose whichever you prefer.
 *
 * ALTERNATIVE A - MIT License
 * Copyright (c) 2017 Sean Barrett
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 * ALTERNATIVE B - Public Domain (www.unlicense.org)
 * This is free and unencumbered software released into the public domain.
 */
