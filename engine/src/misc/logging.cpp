/**
 * @file logging.cpp
 * @brief Implementation of context-owned logging for DOSBox-X library mode.
 *
 * Thread-safety: The logging state is protected by a mutex for callback
 * registration, but log calls themselves are designed to be fast and
 * minimize locking overhead.
 *
 * @copyright GPL-2.0-or-later
 */

#include "dosbox/logging.h"

#include <cstdio>
#include <cstdarg>
#include <cstring>
#include <mutex>
#include <atomic>

// ═══════════════════════════════════════════════════════════════════════════════
// Global State (Transitional - will move to DOSBoxContext in PR #9)
// ═══════════════════════════════════════════════════════════════════════════════

namespace {

// Mutex for callback registration (not for logging itself)
std::mutex g_log_mutex;

// Current callback and userdata
dosbox_log_callback g_log_callback = nullptr;
void* g_log_userdata = nullptr;

// Minimum log level (atomic for lock-free reads in hot path)
std::atomic<dosbox_log_level> g_min_log_level{DOSBOX_LOG_INFO};

// Buffer size for printf-style formatting
constexpr size_t LOG_BUFFER_SIZE = 1024;

} // anonymous namespace

// ═══════════════════════════════════════════════════════════════════════════════
// C API Implementation
// ═══════════════════════════════════════════════════════════════════════════════

extern "C" {

void dosbox_set_log_callback(dosbox_log_callback callback, void* userdata) {
    std::lock_guard<std::mutex> lock(g_log_mutex);
    g_log_callback = callback;
    g_log_userdata = userdata;
}

void dosbox_set_log_level(dosbox_log_level level) {
    g_min_log_level.store(level, std::memory_order_relaxed);
}

dosbox_log_level dosbox_get_log_level(void) {
    return g_min_log_level.load(std::memory_order_relaxed);
}

const char* dosbox_log_level_name(dosbox_log_level level) {
    switch (level) {
        case DOSBOX_LOG_ERROR: return "ERROR";
        case DOSBOX_LOG_WARN:  return "WARN";
        case DOSBOX_LOG_INFO:  return "INFO";
        case DOSBOX_LOG_DEBUG: return "DEBUG";
        case DOSBOX_LOG_TRACE: return "TRACE";
        default:               return "UNKNOWN";
    }
}

} // extern "C"

// ═══════════════════════════════════════════════════════════════════════════════
// C++ Implementation
// ═══════════════════════════════════════════════════════════════════════════════

namespace dosbox {

namespace detail {

void default_log_handler(
    dosbox_log_level level,
    const char* subsystem,
    const char* message,
    void* /*userdata*/
) noexcept {
    // Default handler writes to stderr with format: [LEVEL] subsystem: message
    const char* level_str = dosbox_log_level_name(level);
    std::fprintf(stderr, "[%s] %s: %s\n", level_str, subsystem, message);
}

} // namespace detail

// ─────────────────────────────────────────────────────────────────────────────
// Core Logging Functions
// ─────────────────────────────────────────────────────────────────────────────

void log_raw(LogLevel level, const char* subsystem, std::string_view message) noexcept {
    // Fast path: check level without locking
    if (static_cast<int>(level) > static_cast<int>(g_min_log_level.load(std::memory_order_relaxed))) {
        return;
    }

    // Get callback (brief lock, copy out)
    dosbox_log_callback callback = nullptr;
    void* userdata = nullptr;
    {
        std::lock_guard<std::mutex> lock(g_log_mutex);
        callback = g_log_callback;
        userdata = g_log_userdata;
    }

    // Convert string_view to null-terminated (if not already)
    // For efficiency, we check if it's already null-terminated
    char buffer[LOG_BUFFER_SIZE];
    const char* msg_cstr = nullptr;

    if (message.size() < LOG_BUFFER_SIZE) {
        // Check if already null-terminated at the right position
        if (message.data()[message.size()] == '\0') {
            msg_cstr = message.data();
        } else {
            // Copy to buffer and null-terminate
            std::memcpy(buffer, message.data(), message.size());
            buffer[message.size()] = '\0';
            msg_cstr = buffer;
        }
    } else {
        // Truncate to buffer size
        std::memcpy(buffer, message.data(), LOG_BUFFER_SIZE - 1);
        buffer[LOG_BUFFER_SIZE - 1] = '\0';
        msg_cstr = buffer;
    }

    // Call handler
    dosbox_log_level c_level = static_cast<dosbox_log_level>(level);
    if (callback) {
        callback(c_level, subsystem, msg_cstr, userdata);
    }
#ifndef DOSBOX_LIBRARY_MODE
    else {
        // In standalone mode, use default handler if no callback set
        detail::default_log_handler(c_level, subsystem, msg_cstr, nullptr);
    }
#endif
}

void log_printf(LogLevel level, const char* subsystem, const char* fmt, ...) noexcept {
    // Fast path: check level without formatting
    if (static_cast<int>(level) > static_cast<int>(g_min_log_level.load(std::memory_order_relaxed))) {
        return;
    }

    // Format the message
    char buffer[LOG_BUFFER_SIZE];
    va_list args;
    va_start(args, fmt);
    int written = std::vsnprintf(buffer, LOG_BUFFER_SIZE, fmt, args);
    va_end(args);

    // Handle truncation
    if (written < 0) {
        // Encoding error
        buffer[0] = '\0';
    } else if (static_cast<size_t>(written) >= LOG_BUFFER_SIZE) {
        // Truncated - add ellipsis
        buffer[LOG_BUFFER_SIZE - 4] = '.';
        buffer[LOG_BUFFER_SIZE - 3] = '.';
        buffer[LOG_BUFFER_SIZE - 2] = '.';
        buffer[LOG_BUFFER_SIZE - 1] = '\0';
    }

    // Delegate to raw logging
    log_raw(level, subsystem, buffer);
}

} // namespace dosbox
