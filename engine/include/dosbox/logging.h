/**
 * @file logging.h
 * @brief Context-owned logging infrastructure for DOSBox-X library mode.
 *
 * This implements per-context logging as defined in LIBRARY_CONTRACT.md:
 * - All output goes through callbacks, never stdout/stderr
 * - Per-context callbacks for multi-instance safety (future V2)
 * - Fast path (log_raw) for hot loops without formatting overhead
 *
 * Usage:
 *   // Host sets callback
 *   dosbox_set_log_callback(handle, my_logger, userdata);
 *
 *   // Core uses macros (transitional, uses current_context())
 *   LOG_MSG("CPU", "Executing at %04X:%04X", cs, ip);
 *   LOG_ERROR("DISK", "Failed to open {}", path);
 *
 * @copyright GPL-2.0-or-later
 */

#ifndef DOSBOX_LOGGING_H
#define DOSBOX_LOGGING_H

#include <cstdint>
#include <cstddef>

#ifdef __cplusplus
#include <string_view>
#include <format>
#include <source_location>
#endif

// ═══════════════════════════════════════════════════════════════════════════════
// C ABI Types (FFI-safe)
// ═══════════════════════════════════════════════════════════════════════════════

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Log severity levels.
 *
 * Ordered from most to least severe for filtering.
 */
typedef enum dosbox_log_level {
    DOSBOX_LOG_ERROR = 0,   /**< Errors that affect operation */
    DOSBOX_LOG_WARN  = 1,   /**< Warnings about potential issues */
    DOSBOX_LOG_INFO  = 2,   /**< Informational messages */
    DOSBOX_LOG_DEBUG = 3,   /**< Debug information */
    DOSBOX_LOG_TRACE = 4    /**< Detailed trace for debugging */
} dosbox_log_level;

/**
 * @brief Log callback function type.
 *
 * @param level     Severity level of the message
 * @param subsystem Subsystem identifier (e.g., "CPU", "VGA", "DISK")
 * @param message   The log message (null-terminated)
 * @param userdata  User-provided context from registration
 */
typedef void (*dosbox_log_callback)(
    dosbox_log_level level,
    const char* subsystem,
    const char* message,
    void* userdata
);

/**
 * @brief Set the log callback for a context.
 *
 * @param callback  Function to receive log messages (NULL to disable)
 * @param userdata  User context passed to callback
 */
void dosbox_set_log_callback(dosbox_log_callback callback, void* userdata);

/**
 * @brief Set minimum log level (messages below this are filtered).
 *
 * @param level  Minimum level to log (default: DOSBOX_LOG_INFO)
 */
void dosbox_set_log_level(dosbox_log_level level);

/**
 * @brief Get current minimum log level.
 */
dosbox_log_level dosbox_get_log_level(void);

/**
 * @brief Convert log level to string.
 */
const char* dosbox_log_level_name(dosbox_log_level level);

#ifdef __cplusplus
} /* extern "C" */
#endif

// ═══════════════════════════════════════════════════════════════════════════════
// C++ API
// ═══════════════════════════════════════════════════════════════════════════════

#ifdef __cplusplus

namespace dosbox {

// ─────────────────────────────────────────────────────────────────────────────
// Log Level (C++ enum class wrapper)
// ─────────────────────────────────────────────────────────────────────────────

enum class LogLevel : int {
    Error = DOSBOX_LOG_ERROR,
    Warn  = DOSBOX_LOG_WARN,
    Info  = DOSBOX_LOG_INFO,
    Debug = DOSBOX_LOG_DEBUG,
    Trace = DOSBOX_LOG_TRACE
};

/**
 * @brief Convert LogLevel to string.
 */
[[nodiscard]] inline const char* log_level_name(LogLevel level) noexcept {
    return dosbox_log_level_name(static_cast<dosbox_log_level>(level));
}

// ─────────────────────────────────────────────────────────────────────────────
// Log Callback Type (C++)
// ─────────────────────────────────────────────────────────────────────────────

using LogCallback = dosbox_log_callback;

// ─────────────────────────────────────────────────────────────────────────────
// Logging Functions
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Log a pre-formatted message (fast path).
 *
 * Use this in hot loops where formatting overhead matters.
 * No formatting is performed; message is passed directly to callback.
 *
 * @param level     Severity level
 * @param subsystem Subsystem identifier
 * @param message   Pre-formatted message
 */
void log_raw(LogLevel level, const char* subsystem, std::string_view message) noexcept;

/**
 * @brief Log with printf-style formatting.
 *
 * @param level     Severity level
 * @param subsystem Subsystem identifier
 * @param fmt       printf format string
 * @param ...       Format arguments
 */
void log_printf(LogLevel level, const char* subsystem, const char* fmt, ...) noexcept;

/**
 * @brief Log with std::format formatting.
 *
 * @param level     Severity level
 * @param subsystem Subsystem identifier
 * @param fmt       std::format string
 * @param args      Format arguments
 */
template<typename... Args>
void log_fmt(LogLevel level, const char* subsystem,
             std::format_string<Args...> fmt, Args&&... args) {
    // Check level before formatting (avoid work if filtered)
    if (static_cast<int>(level) > static_cast<int>(
            static_cast<LogLevel>(dosbox_get_log_level()))) {
        return;
    }
    std::string msg = std::format(fmt, std::forward<Args>(args)...);
    log_raw(level, subsystem, msg);
}

/**
 * @brief Check if a log level is enabled.
 *
 * Use this to guard expensive log argument computation.
 */
[[nodiscard]] inline bool log_level_enabled(LogLevel level) noexcept {
    return static_cast<int>(level) <= static_cast<int>(
        static_cast<LogLevel>(dosbox_get_log_level()));
}

// ─────────────────────────────────────────────────────────────────────────────
// Internal: Default Handler
// ─────────────────────────────────────────────────────────────────────────────

namespace detail {

/**
 * @brief Default log handler that writes to stderr.
 *
 * Used when no callback is set. In library mode, this is typically
 * replaced by the host's callback.
 */
void default_log_handler(
    dosbox_log_level level,
    const char* subsystem,
    const char* message,
    void* userdata
) noexcept;

} // namespace detail

} // namespace dosbox

// ═══════════════════════════════════════════════════════════════════════════════
// Logging Macros (Transitional)
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * These macros provide a transitional API that will work with both the
 * current global logging and future per-context logging.
 *
 * Usage:
 *   LOG_MSG("CPU", "Executing instruction at %04X:%04X", cs, ip);
 *   LOG_ERROR("DISK", "Failed to open file: {}", path);
 *   LOG_DEBUG("VGA", "Mode change: {}x{}", width, height);
 */

// Guard macro for expensive argument computation
#define LOG_LEVEL_ENABLED(level) \
    ::dosbox::log_level_enabled(::dosbox::LogLevel::level)

// Printf-style logging (legacy compatibility)
#define LOG_MSG(subsys, ...) \
    ::dosbox::log_printf(::dosbox::LogLevel::Info, subsys, __VA_ARGS__)

#define LOG_ERROR(subsys, ...) \
    ::dosbox::log_printf(::dosbox::LogLevel::Error, subsys, __VA_ARGS__)

#define LOG_WARN(subsys, ...) \
    ::dosbox::log_printf(::dosbox::LogLevel::Warn, subsys, __VA_ARGS__)

#define LOG_DEBUG(subsys, ...) \
    ::dosbox::log_printf(::dosbox::LogLevel::Debug, subsys, __VA_ARGS__)

#define LOG_TRACE(subsys, ...) \
    ::dosbox::log_printf(::dosbox::LogLevel::Trace, subsys, __VA_ARGS__)

// std::format-style logging (modern C++)
#define LOG_FMT(level, subsys, fmt, ...) \
    ::dosbox::log_fmt(::dosbox::LogLevel::level, subsys, fmt, ##__VA_ARGS__)

// Fast path for pre-formatted messages
#define LOG_RAW(level, subsys, msg) \
    ::dosbox::log_raw(::dosbox::LogLevel::level, subsys, msg)

// Conditional logging (only evaluates args if level enabled)
#define LOG_IF(level, subsys, ...) \
    do { \
        if (LOG_LEVEL_ENABLED(level)) { \
            LOG_FMT(level, subsys, __VA_ARGS__); \
        } \
    } while (0)

#endif /* __cplusplus */

#endif /* DOSBOX_LOGGING_H */
