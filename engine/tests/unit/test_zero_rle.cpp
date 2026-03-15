/**
 * @file test_zero_rle.cpp
 * @brief Unit tests for zero-byte RLE codec (Phase 3: RAM+VGA serialization).
 */

#include <gtest/gtest.h>
#include <dosbox/zero_rle.h>
#include <vector>
#include <cstring>
#include <numeric>

// ─────────────────────────────────────────────────────────────────────────────
// Round-trip tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ZeroRle, EmptyInput) {
    uint8_t dst[16];
    size_t enc = dosbox::zero_rle_encode(nullptr, 0, dst, sizeof(dst));
    EXPECT_EQ(enc, 0u);

    enc = dosbox::zero_rle_encode(dst, 0, dst, sizeof(dst));
    EXPECT_EQ(enc, 0u);
}

TEST(ZeroRle, AllNonZeroRoundTrip) {
    std::vector<uint8_t> src = {1, 2, 3, 0xFF, 0x80, 42};
    std::vector<uint8_t> enc(dosbox::zero_rle_bound(src.size()));
    size_t enc_size = dosbox::zero_rle_encode(src.data(), src.size(),
                                              enc.data(), enc.size());
    // All non-zero: output == input (no expansion)
    ASSERT_EQ(enc_size, src.size());
    EXPECT_EQ(std::memcmp(enc.data(), src.data(), src.size()), 0);

    // Decode back
    std::vector<uint8_t> dec(src.size());
    size_t dec_size = dosbox::zero_rle_decode(enc.data(), enc_size,
                                              dec.data(), dec.size());
    ASSERT_EQ(dec_size, src.size());
    EXPECT_EQ(src, dec);
}

TEST(ZeroRle, AllZerosRoundTrip) {
    const size_t N = 1000;
    std::vector<uint8_t> src(N, 0);
    std::vector<uint8_t> enc(dosbox::zero_rle_bound(N));
    size_t enc_size = dosbox::zero_rle_encode(src.data(), src.size(),
                                              enc.data(), enc.size());
    // 1000 zeros → 1 run → 3 bytes
    ASSERT_EQ(enc_size, 3u);
    EXPECT_EQ(enc[0], 0x00);
    EXPECT_EQ(enc[1], 0x03);  // 1000 >> 8
    EXPECT_EQ(enc[2], 0xE8);  // 1000 & 0xFF

    std::vector<uint8_t> dec(N);
    size_t dec_size = dosbox::zero_rle_decode(enc.data(), enc_size,
                                              dec.data(), dec.size());
    ASSERT_EQ(dec_size, N);
    EXPECT_EQ(src, dec);
}

TEST(ZeroRle, SingleZeroRoundTrip) {
    uint8_t src[] = {0};
    uint8_t enc[8];
    size_t enc_size = dosbox::zero_rle_encode(src, 1, enc, sizeof(enc));
    ASSERT_EQ(enc_size, 3u);  // 0x00 0x00 0x01

    uint8_t dec[1];
    size_t dec_size = dosbox::zero_rle_decode(enc, enc_size, dec, sizeof(dec));
    ASSERT_EQ(dec_size, 1u);
    EXPECT_EQ(dec[0], 0u);
}

TEST(ZeroRle, MixedDataRoundTrip) {
    // Simulate typical DOS RAM: non-zero code then large zero gap
    std::vector<uint8_t> src(4096, 0);
    // Write some "code" at the beginning
    for (int i = 0; i < 256; ++i) {
        src[i] = static_cast<uint8_t>(i + 1);  // 1..256 (non-zero)
    }
    // Write some data in the middle
    src[2048] = 0xAA;
    src[2049] = 0xBB;

    std::vector<uint8_t> enc(dosbox::zero_rle_bound(src.size()));
    size_t enc_size = dosbox::zero_rle_encode(src.data(), src.size(),
                                              enc.data(), enc.size());
    ASSERT_GT(enc_size, 0u);
    // Should compress well: 256 bytes literal + small overhead for zero runs
    EXPECT_LT(enc_size, src.size() / 2);

    std::vector<uint8_t> dec(src.size());
    size_t dec_size = dosbox::zero_rle_decode(enc.data(), enc_size,
                                              dec.data(), dec.size());
    ASSERT_EQ(dec_size, src.size());
    EXPECT_EQ(src, dec);
}

TEST(ZeroRle, AlternatingZerosAndNonZeros) {
    // Worst-case expansion pattern
    std::vector<uint8_t> src = {1, 0, 2, 0, 3, 0, 4, 0};
    std::vector<uint8_t> enc(dosbox::zero_rle_bound(src.size()));
    size_t enc_size = dosbox::zero_rle_encode(src.data(), src.size(),
                                              enc.data(), enc.size());
    // 4 non-zero (4 bytes) + 4 zero runs (4×3 = 12 bytes) = 16 bytes
    ASSERT_EQ(enc_size, 16u);

    std::vector<uint8_t> dec(src.size());
    size_t dec_size = dosbox::zero_rle_decode(enc.data(), enc_size,
                                              dec.data(), dec.size());
    ASSERT_EQ(dec_size, src.size());
    EXPECT_EQ(src, dec);
}

// ─────────────────────────────────────────────────────────────────────────────
// Edge cases
// ─────────────────────────────────────────────────────────────────────────────

TEST(ZeroRle, ExactlyMaxRunLength) {
    const size_t N = 65535;
    std::vector<uint8_t> src(N, 0);
    std::vector<uint8_t> enc(dosbox::zero_rle_bound(N));
    size_t enc_size = dosbox::zero_rle_encode(src.data(), src.size(),
                                              enc.data(), enc.size());
    // Single run of 65535 → 3 bytes
    ASSERT_EQ(enc_size, 3u);
    EXPECT_EQ(enc[0], 0x00);
    EXPECT_EQ(enc[1], 0xFF);
    EXPECT_EQ(enc[2], 0xFF);

    std::vector<uint8_t> dec(N);
    size_t dec_size = dosbox::zero_rle_decode(enc.data(), enc_size,
                                              dec.data(), dec.size());
    ASSERT_EQ(dec_size, N);
    for (size_t i = 0; i < N; ++i) EXPECT_EQ(dec[i], 0);
}

TEST(ZeroRle, OverMaxRunLengthSplitsIntoTwoRuns) {
    const size_t N = 65536;  // One more than max run
    std::vector<uint8_t> src(N, 0);
    std::vector<uint8_t> enc(dosbox::zero_rle_bound(N));
    size_t enc_size = dosbox::zero_rle_encode(src.data(), src.size(),
                                              enc.data(), enc.size());
    // Two runs: 65535 + 1 → 6 bytes
    ASSERT_EQ(enc_size, 6u);

    std::vector<uint8_t> dec(N);
    size_t dec_size = dosbox::zero_rle_decode(enc.data(), enc_size,
                                              dec.data(), dec.size());
    ASSERT_EQ(dec_size, N);
    for (size_t i = 0; i < N; ++i) EXPECT_EQ(dec[i], 0);
}

TEST(ZeroRle, LargeZeroRun_16MB) {
    // Simulate 16MB of zeros (typical empty DOS RAM)
    const size_t N = 16 * 1024 * 1024;
    std::vector<uint8_t> src(N, 0);
    std::vector<uint8_t> enc(dosbox::zero_rle_bound(N));
    size_t enc_size = dosbox::zero_rle_encode(src.data(), src.size(),
                                              enc.data(), enc.size());
    // ceil(16M / 65535) = 256 runs → 768 bytes
    size_t expected_runs = (N + 65534) / 65535;
    ASSERT_EQ(enc_size, expected_runs * 3);

    std::vector<uint8_t> dec(N);
    size_t dec_size = dosbox::zero_rle_decode(enc.data(), enc_size,
                                              dec.data(), dec.size());
    ASSERT_EQ(dec_size, N);
}

TEST(ZeroRle, OutputTooSmallReturnsZero) {
    std::vector<uint8_t> src = {0, 0, 0};  // Needs 3 bytes output
    uint8_t enc[2];  // Too small
    size_t enc_size = dosbox::zero_rle_encode(src.data(), src.size(),
                                              enc, sizeof(enc));
    EXPECT_EQ(enc_size, 0u);
}

TEST(ZeroRle, DecodeTruncatedStreamReturnsZero) {
    // Truncated escape sequence: 0x00 followed by only 1 byte
    uint8_t enc[] = {0x00, 0x01};
    uint8_t dec[16];
    size_t dec_size = dosbox::zero_rle_decode(enc, 2, dec, sizeof(dec));
    EXPECT_EQ(dec_size, 0u);
}

TEST(ZeroRle, DecodeOutputOverflowReturnsZero) {
    // Encode 100 zeros
    uint8_t enc[] = {0x00, 0x00, 0x64};  // Run of 100
    uint8_t dec[50];  // Too small
    size_t dec_size = dosbox::zero_rle_decode(enc, 3, dec, sizeof(dec));
    EXPECT_EQ(dec_size, 0u);
}

TEST(ZeroRle, LiteralZeroEscapeDecodes) {
    // 0x00 0x00 0x00 = literal zero (count=0)
    uint8_t enc[] = {0x00, 0x00, 0x00};
    uint8_t dec[4];
    size_t dec_size = dosbox::zero_rle_decode(enc, 3, dec, sizeof(dec));
    ASSERT_EQ(dec_size, 1u);
    EXPECT_EQ(dec[0], 0u);
}

// ─────────────────────────────────────────────────────────────────────────────
// Worst-case bound verification
// ─────────────────────────────────────────────────────────────────────────────

TEST(ZeroRle, BoundIsAlwaysSufficient) {
    // Test with worst-case pattern: alternating 0x01, 0x00
    for (size_t n = 1; n <= 256; ++n) {
        std::vector<uint8_t> src(n);
        for (size_t i = 0; i < n; ++i) {
            src[i] = (i % 2 == 0) ? 0x42 : 0x00;
        }
        size_t bound = dosbox::zero_rle_bound(n);
        std::vector<uint8_t> enc(bound);
        size_t enc_size = dosbox::zero_rle_encode(src.data(), src.size(),
                                                  enc.data(), enc.size());
        ASSERT_GT(enc_size, 0u) << "Failed for n=" << n;
        ASSERT_LE(enc_size, bound) << "Exceeded bound for n=" << n;

        // Verify round-trip
        std::vector<uint8_t> dec(n);
        size_t dec_size = dosbox::zero_rle_decode(enc.data(), enc_size,
                                                  dec.data(), dec.size());
        ASSERT_EQ(dec_size, n) << "Decode size mismatch for n=" << n;
        EXPECT_EQ(src, dec) << "Data mismatch for n=" << n;
    }
}

TEST(ZeroRle, NullPointersReturnZero) {
    uint8_t buf[8] = {};
    EXPECT_EQ(dosbox::zero_rle_encode(nullptr, 10, buf, 8), 0u);
    EXPECT_EQ(dosbox::zero_rle_encode(buf, 8, nullptr, 8), 0u);
    EXPECT_EQ(dosbox::zero_rle_decode(nullptr, 3, buf, 8), 0u);
    EXPECT_EQ(dosbox::zero_rle_decode(buf, 3, nullptr, 8), 0u);
}
