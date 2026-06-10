// SPDX-License-Identifier: GPL-2.0-or-later
/**
 * @file fuzz_engine_memory_blob.cpp
 * @brief CRC-aware libFuzzer target for V5 engine RAM blobs.
 *
 * The V5 engine state loader verifies CRC32 before it reaches the sub-block
 * directory and RAM zero-RLE decode. This target keeps a valid V5 state shape,
 * mutates the RAM blob and related RAM metadata, then recomputes the checksum
 * so mutations exercise the loader past header validation.
 */

#include "dosbox/dosbox_library.h"
#include "dosbox/engine_state.h"
#include "dosbox/zero_rle.h"

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

extern "C" size_t LLVMFuzzerMutate(uint8_t* data, size_t size, size_t max_size);

namespace {

dosbox_lib_handle_t g_handle = nullptr;
bool g_initialized = false;
std::vector<uint8_t> g_seed_state;
size_t g_ram_entry_offset = 0;
dosbox::V5DirEntry g_seed_ram_entry{};
uint32_t g_seed_memory_offset = 0;
uint64_t g_crc_valid_ram_inputs = 0;
uint64_t g_rle_decode_reached = 0;
uint64_t g_oversized_ram_rejections = 0;

template <typename T>
bool read_struct(const uint8_t* data, size_t size, size_t offset, T& out) {
    if (offset > size || sizeof(T) > size - offset) {
        return false;
    }
    std::memcpy(&out, data + offset, sizeof(T));
    return true;
}

template <typename T>
bool write_struct(uint8_t* data, size_t size, size_t offset, const T& in) {
    if (offset > size || sizeof(T) > size - offset) {
        return false;
    }
    std::memcpy(data + offset, &in, sizeof(T));
    return true;
}

bool find_ram_entry(const uint8_t* data,
                    size_t size,
                    size_t& entry_offset,
                    dosbox::V5DirEntry& entry) {
    dosbox::EngineStateHeader header{};
    if (!read_struct(data, size, 0, header) ||
        header.magic != dosbox::ENGINE_STATE_MAGIC ||
        header.version < 5 ||
        header.total_size > size ||
        header.total_size < dosbox::ENGINE_STATE_SIZE_V5_BASE) {
        return false;
    }

    dosbox::V5SubBlockDir dir{};
    constexpr size_t dir_offset = dosbox::ENGINE_STATE_SIZE_V5_BASE;
    if (!read_struct(data, header.total_size, dir_offset, dir) ||
        dir.dir_magic != dosbox::V5_DIR_MAGIC) {
        return false;
    }

    const size_t entries_offset = dir_offset + sizeof(dosbox::V5SubBlockDir);
    const size_t entries_bytes =
        static_cast<size_t>(dir.entry_count) * sizeof(dosbox::V5DirEntry);
    if (entries_offset > header.total_size ||
        entries_bytes > header.total_size - entries_offset) {
        return false;
    }

    for (uint16_t i = 0; i < dir.entry_count; ++i) {
        dosbox::V5DirEntry current{};
        const size_t current_offset = entries_offset + i * sizeof(dosbox::V5DirEntry);
        if (!read_struct(data, header.total_size, current_offset, current)) {
            return false;
        }
        if (current.tag == dosbox::V5_SUBTAG_RAM) {
            if (current.offset > header.total_size ||
                current.size > header.total_size - current.offset) {
                return false;
            }
            entry_offset = current_offset;
            entry = current;
            return true;
        }
    }

    return false;
}

void refresh_checksum(uint8_t* data, size_t size) {
    dosbox::EngineStateHeader header{};
    if (!read_struct(data, size, 0, header) ||
        size < sizeof(dosbox::EngineStateHeader)) {
        return;
    }

    header.magic = dosbox::ENGINE_STATE_MAGIC;
    header.version = dosbox::ENGINE_STATE_VERSION;
    header.total_size = static_cast<uint32_t>(
        std::min<size_t>(size, UINT32_MAX));
    header.checksum = 0;

    const size_t checksummed_size =
        static_cast<size_t>(header.total_size) - sizeof(dosbox::EngineStateHeader);
    header.checksum = dosbox::compute_crc32(
        data + sizeof(dosbox::EngineStateHeader), checksummed_size);
    write_struct(data, size, 0, header);
}

bool has_valid_crc_ram_state(const uint8_t* data, size_t size) {
    dosbox::EngineStateHeader header{};
    if (!read_struct(data, size, 0, header) ||
        header.magic != dosbox::ENGINE_STATE_MAGIC ||
        header.version < 5 ||
        header.total_size > size ||
        header.total_size < sizeof(dosbox::EngineStateHeader)) {
        return false;
    }

    const auto computed = dosbox::compute_crc32(
        data + sizeof(dosbox::EngineStateHeader),
        static_cast<size_t>(header.total_size) - sizeof(dosbox::EngineStateHeader));
    if (computed != header.checksum) {
        return false;
    }

    size_t entry_offset = 0;
    dosbox::V5DirEntry entry{};
    return find_ram_entry(data, header.total_size, entry_offset, entry);
}

std::string last_error() {
    size_t needed = 0;
    if (dosbox_lib_get_last_error(g_handle, nullptr, 0, &needed) != DOSBOX_LIB_OK ||
        needed == 0) {
        return {};
    }
    std::vector<char> buffer(needed);
    if (dosbox_lib_get_last_error(g_handle, buffer.data(), buffer.size(), &needed) !=
        DOSBOX_LIB_OK) {
        return {};
    }
    return std::string(buffer.data());
}

void ensure_initialized() {
    if (g_initialized) {
        return;
    }

    dosbox_lib_destroy(g_handle);
    if (dosbox_lib_create(nullptr, &g_handle) != DOSBOX_LIB_OK) {
        std::abort();
    }
    if (dosbox_lib_init(g_handle) != DOSBOX_LIB_OK) {
        std::abort();
    }

    g_initialized = true;
}

void ensure_seed_state() {
    if (!g_seed_state.empty()) {
        return;
    }

    ensure_initialized();

    size_t state_size = 0;
    if (dosbox_lib_save_state(g_handle, nullptr, 0, &state_size) != DOSBOX_LIB_OK ||
        state_size == 0) {
        std::abort();
    }

    g_seed_state.resize(state_size);
    if (dosbox_lib_save_state(g_handle, g_seed_state.data(), g_seed_state.size(),
                              &state_size) != DOSBOX_LIB_OK) {
        std::abort();
    }
    g_seed_state.resize(state_size);

    dosbox::EngineStateHeader header{};
    if (!read_struct(g_seed_state.data(), g_seed_state.size(), 0, header)) {
        std::abort();
    }
    g_seed_memory_offset = header.memory_offset;

    if (!find_ram_entry(g_seed_state.data(), g_seed_state.size(),
                        g_ram_entry_offset, g_seed_ram_entry)) {
        std::abort();
    }
}

size_t copy_seed(uint8_t* data, size_t max_size) {
    ensure_seed_state();
    if (g_seed_state.size() > max_size) {
        return 0;
    }
    std::memcpy(data, g_seed_state.data(), g_seed_state.size());
    return g_seed_state.size();
}

void write_zero_rle_blob(uint8_t* data, size_t size, uint32_t decoded_size) {
    if (g_seed_ram_entry.offset >= size) {
        return;
    }

    auto* dst = data + g_seed_ram_entry.offset;
    const size_t cap = size - g_seed_ram_entry.offset;
    size_t out = 0;
    uint32_t remaining = decoded_size;
    while (remaining > 0 && out + 3 <= cap) {
        const uint16_t run = static_cast<uint16_t>(
            std::min<uint32_t>(remaining, 65535u));
        dst[out++] = 0x00;
        dst[out++] = static_cast<uint8_t>((run >> 8) & 0xff);
        dst[out++] = static_cast<uint8_t>(run & 0xff);
        remaining -= run;
    }

    dosbox::V5DirEntry entry = g_seed_ram_entry;
    entry.size = static_cast<uint32_t>(out);
    entry.orig_size = decoded_size;
    write_struct(data, size, g_ram_entry_offset, entry);
}

void mutate_ram_blob(uint8_t* data, size_t size, unsigned int seed) {
    dosbox::V5DirEntry entry = g_seed_ram_entry;
    const size_t blob_offset = entry.offset;
    const size_t blob_cap = (blob_offset < size) ? size - blob_offset : 0;
    if (blob_cap == 0) {
        return;
    }

    switch (seed % 8) {
    case 0:
    case 1:
    case 2: {
        const size_t mutable_size = std::min<size_t>(entry.size, blob_cap);
        const size_t new_size = LLVMFuzzerMutate(data + blob_offset,
                                                 mutable_size,
                                                 mutable_size);
        entry.size = static_cast<uint32_t>(new_size);
        write_struct(data, size, g_ram_entry_offset, entry);
        break;
    }
    case 3: {
        LLVMFuzzerMutate(reinterpret_cast<uint8_t*>(&entry), sizeof(entry),
                         sizeof(entry));
        entry.tag = dosbox::V5_SUBTAG_RAM;
        entry.flags = dosbox::V5_BLOCK_FLAG_COMPRESSED;
        entry.offset = g_seed_ram_entry.offset;
        entry.size = std::min<uint32_t>(
            entry.size == 0 ? g_seed_ram_entry.size : entry.size,
            static_cast<uint32_t>(std::min<size_t>(blob_cap, UINT32_MAX)));
        write_struct(data, size, g_ram_entry_offset, entry);
        break;
    }
    case 4: {
        dosbox::EngineStateMemory mem{};
        if (read_struct(data, size, g_seed_memory_offset, mem)) {
            const uint64_t oversized = g_seed_ram_entry.orig_size +
                1u + static_cast<uint32_t>(seed & 0xffffu);
            mem.size = oversized;
            write_struct(data, size, g_seed_memory_offset, mem);
            entry.orig_size = static_cast<uint32_t>(
                std::min<uint64_t>(oversized, UINT32_MAX));
            write_struct(data, size, g_ram_entry_offset, entry);
        }
        break;
    }
    case 5: {
        const uint32_t decoded_size = static_cast<uint32_t>(
            seed % (g_seed_ram_entry.orig_size + 1u));
        write_zero_rle_blob(data, size, decoded_size);
        break;
    }
    case 6: {
        dosbox::EngineStateMemory mem{};
        if (read_struct(data, size, g_seed_memory_offset, mem)) {
            LLVMFuzzerMutate(reinterpret_cast<uint8_t*>(&mem), sizeof(mem),
                             sizeof(mem));
            write_struct(data, size, g_seed_memory_offset, mem);
        }
        break;
    }
    default: {
        std::array<uint8_t, 64> scratch{};
        const size_t scratch_size = LLVMFuzzerMutate(scratch.data(), 1,
                                                     scratch.size());
        const size_t copy_size = std::min(scratch_size, blob_cap);
        std::memcpy(data + blob_offset, scratch.data(), copy_size);
        entry.size = static_cast<uint32_t>(copy_size);
        write_struct(data, size, g_ram_entry_offset, entry);
        break;
    }
    }
}

void print_stats() {
    std::fprintf(stderr,
                 "fuzz_engine_memory_blob: crc_valid_ram_inputs=%llu "
                 "rle_decode_reached=%llu oversized_ram_rejections=%llu\n",
                 static_cast<unsigned long long>(g_crc_valid_ram_inputs),
                 static_cast<unsigned long long>(g_rle_decode_reached),
                 static_cast<unsigned long long>(g_oversized_ram_rejections));
}

} // namespace

extern "C" int LLVMFuzzerInitialize(int*, char***) {
    ensure_seed_state();
    std::atexit(print_stats);
    return 0;
}

extern "C" int LLVMFuzzerTestOneInput(const uint8_t* data, size_t size) {
    ensure_initialized();

    const bool valid_ram_state = has_valid_crc_ram_state(data, size);
    if (valid_ram_state) {
        ++g_crc_valid_ram_inputs;
    }

    const auto err = dosbox_lib_load_state(g_handle, data, size);
    if (valid_ram_state) {
        if (err == DOSBOX_LIB_OK) {
            ++g_rle_decode_reached;
        } else {
            const auto message = last_error();
            if (message.find("RAM blob decompression failed") != std::string::npos) {
                ++g_rle_decode_reached;
            } else if (message.find("RAM blob exceeds live allocation") !=
                       std::string::npos) {
                ++g_oversized_ram_rejections;
            }
        }
    }

    dosbox_lib_reset(g_handle);
    return 0;
}

extern "C" size_t LLVMFuzzerCustomMutator(uint8_t* data,
                                           size_t size,
                                           size_t max_size,
                                           unsigned int seed) {
    ensure_seed_state();

    size_t state_size = size;
    if (state_size != g_seed_state.size() ||
        !has_valid_crc_ram_state(data, state_size)) {
        state_size = copy_seed(data, max_size);
        if (state_size == 0) {
            return LLVMFuzzerMutate(data, size, max_size);
        }
    }

    mutate_ram_blob(data, state_size, seed);
    refresh_checksum(data, state_size);
    return state_size;
}
