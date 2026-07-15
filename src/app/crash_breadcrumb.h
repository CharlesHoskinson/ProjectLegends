// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Crash breadcrumb ring buffer with per-slot sequence numbers (seqlock)
// so concurrent add/readInto is race-free under TSan (#39).

#pragma once

#include <atomic>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <vector>

namespace legends {

enum class BreadcrumbCategory : uint8_t {
    General = 0,
    Engine  = 1,
    IO      = 2,
    Render  = 3,
    Audio   = 4,
};

struct BreadcrumbEntry {
    static constexpr size_t kMaxMessageLen = 128;

    uint64_t timestamp_us = 0;
    char     message[kMaxMessageLen] = {};
    uint32_t thread_id = 0;
    uint8_t  category  = 0;

    void clear() {
        timestamp_us = 0;
        message[0]   = '\0';
        thread_id    = 0;
        category     = 0;
    }
};

class CrashBreadcrumb {
public:
    static constexpr size_t kCapacity = 64;

    CrashBreadcrumb();
    ~CrashBreadcrumb();

    void add(const char* message,
             BreadcrumbCategory category = BreadcrumbCategory::General);

    [[nodiscard]] std::vector<BreadcrumbEntry> read() const;
    [[nodiscard]] size_t readInto(BreadcrumbEntry* out, size_t max_entries) const;
    void   clear();

    [[nodiscard]] uint64_t totalCount() const {
        return write_index_.load(std::memory_order_acquire);
    }

private:
    // Per-slot seqlock: odd = write in progress, even = stable snapshot.
    struct alignas(64) Slot {
        std::atomic<uint64_t> seq{0};
        BreadcrumbEntry       data{};
    };

    Slot                     slots_[kCapacity];
    std::atomic<uint64_t>    write_index_{0};

    [[nodiscard]] static uint32_t currentThreadId();
    [[nodiscard]] static uint64_t currentTimestampUs();
};

[[nodiscard]] CrashBreadcrumb& globalBreadcrumb();

#define LEGENDS_BREADCRUMB(msg) ::legends::globalBreadcrumb().add(msg)

} // namespace legends
