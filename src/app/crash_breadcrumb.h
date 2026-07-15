// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Crash breadcrumb ring buffer. Serialized with a mutex so concurrent
// add/readInto/clear are data-race free under TSan (#39 / audit F013).
// Frequency is crash/debug path only — lock cost is acceptable.

#pragma once

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <mutex>
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

    [[nodiscard]] uint64_t totalCount() const;

private:
    mutable std::mutex       mu_;
    BreadcrumbEntry          entries_[kCapacity];
    uint64_t                 write_index_{0};

    [[nodiscard]] static uint32_t currentThreadId();
    [[nodiscard]] static uint64_t currentTimestampUs();
};

[[nodiscard]] CrashBreadcrumb& globalBreadcrumb();

#define LEGENDS_BREADCRUMB(msg) ::legends::globalBreadcrumb().add(msg)

} // namespace legends
