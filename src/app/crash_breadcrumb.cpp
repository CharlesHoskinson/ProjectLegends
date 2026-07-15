// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Seqlock ring buffer: concurrent writers claim unique indices via
// write_index_; each slot's seq fences field writes so readers never
// observe a torn BreadcrumbEntry (closes TSan race family #39).

#include "app/crash_breadcrumb.h"

#include <algorithm>
#include <chrono>
#include <cstring>

#if defined(_WIN32)
#  ifndef WIN32_LEAN_AND_MEAN
#    define WIN32_LEAN_AND_MEAN
#  endif
#  ifndef NOMINMAX
#    define NOMINMAX
#  endif
#  include <windows.h>
#else
#  include <pthread.h>
#  include <unistd.h>
#endif

namespace legends {

CrashBreadcrumb::CrashBreadcrumb() {
    clear();
}

CrashBreadcrumb::~CrashBreadcrumb() = default;

void CrashBreadcrumb::add(const char* message, BreadcrumbCategory category) {
    if (!message) return;

    uint64_t idx = write_index_.fetch_add(1, std::memory_order_relaxed);
    size_t slot_i = static_cast<size_t>(idx % kCapacity);
    Slot& slot = slots_[slot_i];

    // Serialize writers that land on the same physical slot after wrap-around.
    // Odd seq = write in progress; CAS even→odd claims the slot.
    uint64_t s = 0;
    for (;;) {
        s = slot.seq.load(std::memory_order_acquire);
        if (s & 1ULL) {
            continue;  // concurrent writer on this slot
        }
        if (slot.seq.compare_exchange_weak(
                s, s + 1, std::memory_order_acq_rel, std::memory_order_acquire)) {
            break;
        }
    }

    BreadcrumbEntry& entry = slot.data;
    entry.timestamp_us = currentTimestampUs();
    entry.thread_id = currentThreadId();
    entry.category = static_cast<uint8_t>(category);

    size_t len = std::strlen(message);
    size_t copy_len = std::min(len, BreadcrumbEntry::kMaxMessageLen - 1);
    std::memcpy(entry.message, message, copy_len);
    entry.message[copy_len] = '\0';

    // End write (even sequence) — publish complete entry.
    slot.seq.store(s + 2, std::memory_order_release);
}

std::vector<BreadcrumbEntry> CrashBreadcrumb::read() const {
    std::vector<BreadcrumbEntry> result;
    result.resize(kCapacity);
    size_t count = readInto(result.data(), kCapacity);
    result.resize(count);
    return result;
}

size_t CrashBreadcrumb::readInto(BreadcrumbEntry* out, size_t max_entries) const {
    if (!out || max_entries == 0) return 0;

    uint64_t total = write_index_.load(std::memory_order_acquire);
    if (total == 0) return 0;

    uint64_t count = std::min(total, static_cast<uint64_t>(kCapacity));
    uint64_t start = (total > kCapacity) ? (total - kCapacity) : 0;
    size_t out_count = static_cast<size_t>(std::min(count, static_cast<uint64_t>(max_entries)));

    for (size_t i = 0; i < out_count; ++i) {
        size_t slot_i = static_cast<size_t>((start + i) % kCapacity);
        const Slot& slot = slots_[slot_i];

        // Seqlock read: retry if write in progress or tore mid-copy.
        for (;;) {
            uint64_t s1 = slot.seq.load(std::memory_order_acquire);
            if (s1 & 1ULL) {
                // Writer active — spin briefly then retry.
                continue;
            }
            BreadcrumbEntry tmp;
            std::memcpy(&tmp, &slot.data, sizeof(BreadcrumbEntry));
            std::atomic_thread_fence(std::memory_order_acquire);
            uint64_t s2 = slot.seq.load(std::memory_order_acquire);
            if (s1 == s2) {
                out[i] = tmp;
                break;
            }
        }
    }

    return out_count;
}

void CrashBreadcrumb::clear() {
    write_index_.store(0, std::memory_order_release);
    for (auto& slot : slots_) {
        uint64_t s = slot.seq.load(std::memory_order_relaxed);
        slot.seq.store(s + 1, std::memory_order_release);
        slot.data.clear();
        slot.seq.store(s + 2, std::memory_order_release);
    }
}

uint32_t CrashBreadcrumb::currentThreadId() {
#if defined(_WIN32)
    return static_cast<uint32_t>(GetCurrentThreadId());
#else
    return static_cast<uint32_t>(
        reinterpret_cast<uintptr_t>(reinterpret_cast<void*>(pthread_self())) & 0xFFFFFFFFu);
#endif
}

uint64_t CrashBreadcrumb::currentTimestampUs() {
    auto now = std::chrono::steady_clock::now();
    return static_cast<uint64_t>(
        std::chrono::duration_cast<std::chrono::microseconds>(
            now.time_since_epoch()).count());
}

CrashBreadcrumb& globalBreadcrumb() {
    static CrashBreadcrumb instance;
    return instance;
}

} // namespace legends
