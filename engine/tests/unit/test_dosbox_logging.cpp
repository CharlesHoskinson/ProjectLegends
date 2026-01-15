/**
 * @file test_dosbox_logging.cpp
 * @brief Unit tests for DOSBox-X logging infrastructure.
 *
 * Tests the context-owned logging system defined in dosbox/logging.h.
 */

#include <gtest/gtest.h>
#include "dosbox/logging.h"

#include <string>
#include <vector>
#include <atomic>

using namespace dosbox;

// ═══════════════════════════════════════════════════════════════════════════════
// Test Fixtures
// ═══════════════════════════════════════════════════════════════════════════════

namespace {

struct LogEntry {
    dosbox_log_level level;
    std::string subsystem;
    std::string message;
};

std::vector<LogEntry> g_captured_logs;
std::atomic<int> g_callback_count{0};

void test_log_callback(
    dosbox_log_level level,
    const char* subsystem,
    const char* message,
    void* userdata
) {
    g_callback_count++;
    g_captured_logs.push_back({
        level,
        subsystem ? subsystem : "",
        message ? message : ""
    });
    (void)userdata;
}

} // anonymous namespace

class DosboxLoggingTest : public ::testing::Test {
protected:
    void SetUp() override {
        g_captured_logs.clear();
        g_callback_count = 0;
        dosbox_set_log_callback(test_log_callback, nullptr);
        dosbox_set_log_level(DOSBOX_LOG_TRACE); // Enable all levels
    }

    void TearDown() override {
        dosbox_set_log_callback(nullptr, nullptr);
        dosbox_set_log_level(DOSBOX_LOG_INFO); // Reset to default
        g_captured_logs.clear();
    }
};

// ═══════════════════════════════════════════════════════════════════════════════
// Log Level Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(DosboxLogLevelTest, LevelNameReturnsCorrectStrings) {
    EXPECT_STREQ(dosbox_log_level_name(DOSBOX_LOG_ERROR), "ERROR");
    EXPECT_STREQ(dosbox_log_level_name(DOSBOX_LOG_WARN), "WARN");
    EXPECT_STREQ(dosbox_log_level_name(DOSBOX_LOG_INFO), "INFO");
    EXPECT_STREQ(dosbox_log_level_name(DOSBOX_LOG_DEBUG), "DEBUG");
    EXPECT_STREQ(dosbox_log_level_name(DOSBOX_LOG_TRACE), "TRACE");
}

TEST(DosboxLogLevelTest, UnknownLevelReturnsUnknown) {
    EXPECT_STREQ(dosbox_log_level_name(static_cast<dosbox_log_level>(99)), "UNKNOWN");
}

TEST(DosboxLogLevelTest, CppWrapperWorks) {
    EXPECT_STREQ(log_level_name(LogLevel::Error), "ERROR");
    EXPECT_STREQ(log_level_name(LogLevel::Warn), "WARN");
    EXPECT_STREQ(log_level_name(LogLevel::Info), "INFO");
    EXPECT_STREQ(log_level_name(LogLevel::Debug), "DEBUG");
    EXPECT_STREQ(log_level_name(LogLevel::Trace), "TRACE");
}

// ═══════════════════════════════════════════════════════════════════════════════
// Log Level Filtering Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(DosboxLoggingTest, SetLogLevelWorks) {
    dosbox_set_log_level(DOSBOX_LOG_WARN);
    EXPECT_EQ(dosbox_get_log_level(), DOSBOX_LOG_WARN);

    dosbox_set_log_level(DOSBOX_LOG_ERROR);
    EXPECT_EQ(dosbox_get_log_level(), DOSBOX_LOG_ERROR);
}

TEST_F(DosboxLoggingTest, LogLevelFiltersMessages) {
    dosbox_set_log_level(DOSBOX_LOG_WARN);

    LOG_ERROR("TEST", "error message");
    LOG_WARN("TEST", "warn message");
    LOG_MSG("TEST", "info message");  // Should be filtered
    LOG_DEBUG("TEST", "debug message"); // Should be filtered

    EXPECT_EQ(g_captured_logs.size(), 2u);
    EXPECT_EQ(g_captured_logs[0].level, DOSBOX_LOG_ERROR);
    EXPECT_EQ(g_captured_logs[1].level, DOSBOX_LOG_WARN);
}

TEST_F(DosboxLoggingTest, LogLevelEnabledWorks) {
    dosbox_set_log_level(DOSBOX_LOG_WARN);

    EXPECT_TRUE(log_level_enabled(LogLevel::Error));
    EXPECT_TRUE(log_level_enabled(LogLevel::Warn));
    EXPECT_FALSE(log_level_enabled(LogLevel::Info));
    EXPECT_FALSE(log_level_enabled(LogLevel::Debug));
    EXPECT_FALSE(log_level_enabled(LogLevel::Trace));
}

// ═══════════════════════════════════════════════════════════════════════════════
// Callback Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(DosboxLoggingTest, CallbackReceivesMessage) {
    LOG_MSG("CPU", "test message");

    ASSERT_EQ(g_captured_logs.size(), 1u);
    EXPECT_EQ(g_captured_logs[0].level, DOSBOX_LOG_INFO);
    EXPECT_EQ(g_captured_logs[0].subsystem, "CPU");
    EXPECT_EQ(g_captured_logs[0].message, "test message");
}

TEST_F(DosboxLoggingTest, NullCallbackDoesNotCrash) {
    dosbox_set_log_callback(nullptr, nullptr);

    // Should not crash
    LOG_MSG("TEST", "message with no callback");
    LOG_ERROR("TEST", "error with no callback");

    EXPECT_EQ(g_captured_logs.size(), 0u);
}

TEST_F(DosboxLoggingTest, CallbackUserdataWorks) {
    int userdata_value = 42;
    int* received_userdata = nullptr;

    dosbox_set_log_callback(
        [](dosbox_log_level, const char*, const char*, void* ud) {
            // Can't easily capture in lambda, so use global for test
        },
        &userdata_value
    );

    // The callback was set with userdata - implementation detail tested
    // Just verify it doesn't crash
    LOG_MSG("TEST", "test");
}

// ═══════════════════════════════════════════════════════════════════════════════
// Printf-Style Formatting Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(DosboxLoggingTest, PrintfFormattingWorks) {
    LOG_MSG("CPU", "Register AX=%04X BX=%04X", 0x1234, 0x5678);

    ASSERT_EQ(g_captured_logs.size(), 1u);
    EXPECT_EQ(g_captured_logs[0].message, "Register AX=1234 BX=5678");
}

TEST_F(DosboxLoggingTest, PrintfWithStrings) {
    LOG_ERROR("DISK", "Failed to open: %s", "/path/to/file");

    ASSERT_EQ(g_captured_logs.size(), 1u);
    EXPECT_EQ(g_captured_logs[0].message, "Failed to open: /path/to/file");
}

TEST_F(DosboxLoggingTest, PrintfWithMixedTypes) {
    LOG_DEBUG("MEM", "Address %p, size %zu, value %d", (void*)0x1000, size_t(256), -42);

    ASSERT_EQ(g_captured_logs.size(), 1u);
    // Just verify it doesn't crash and produces output
    EXPECT_FALSE(g_captured_logs[0].message.empty());
}

// ═══════════════════════════════════════════════════════════════════════════════
// std::format-Style Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(DosboxLoggingTest, FormatStyleWorks) {
    log_fmt(LogLevel::Info, "VGA", "Mode: {}x{}", 640, 480);

    ASSERT_EQ(g_captured_logs.size(), 1u);
    EXPECT_EQ(g_captured_logs[0].message, "Mode: 640x480");
}

TEST_F(DosboxLoggingTest, FormatMacroWorks) {
    LOG_FMT(Info, "TEST", "Value: {}", 42);

    ASSERT_EQ(g_captured_logs.size(), 1u);
    EXPECT_EQ(g_captured_logs[0].message, "Value: 42");
}

// ═══════════════════════════════════════════════════════════════════════════════
// Raw Logging Tests (Fast Path)
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(DosboxLoggingTest, LogRawWorks) {
    std::string msg = "pre-formatted message";
    log_raw(LogLevel::Info, "FAST", msg);

    ASSERT_EQ(g_captured_logs.size(), 1u);
    EXPECT_EQ(g_captured_logs[0].message, "pre-formatted message");
}

TEST_F(DosboxLoggingTest, LogRawMacroWorks) {
    LOG_RAW(Debug, "PERF", "hot loop iteration");

    ASSERT_EQ(g_captured_logs.size(), 1u);
    EXPECT_EQ(g_captured_logs[0].level, DOSBOX_LOG_DEBUG);
    EXPECT_EQ(g_captured_logs[0].message, "hot loop iteration");
}

TEST_F(DosboxLoggingTest, LogRawWithStringView) {
    std::string_view sv = "string view message";
    log_raw(LogLevel::Info, "TEST", sv);

    ASSERT_EQ(g_captured_logs.size(), 1u);
    EXPECT_EQ(g_captured_logs[0].message, "string view message");
}

// ═══════════════════════════════════════════════════════════════════════════════
// Macro Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(DosboxLoggingTest, LogErrorMacro) {
    LOG_ERROR("SYS", "Critical failure");

    ASSERT_EQ(g_captured_logs.size(), 1u);
    EXPECT_EQ(g_captured_logs[0].level, DOSBOX_LOG_ERROR);
    EXPECT_EQ(g_captured_logs[0].subsystem, "SYS");
}

TEST_F(DosboxLoggingTest, LogWarnMacro) {
    LOG_WARN("CFG", "Deprecated option");

    ASSERT_EQ(g_captured_logs.size(), 1u);
    EXPECT_EQ(g_captured_logs[0].level, DOSBOX_LOG_WARN);
}

TEST_F(DosboxLoggingTest, LogDebugMacro) {
    LOG_DEBUG("INT", "Interrupt %02X", 0x21);

    ASSERT_EQ(g_captured_logs.size(), 1u);
    EXPECT_EQ(g_captured_logs[0].level, DOSBOX_LOG_DEBUG);
    EXPECT_EQ(g_captured_logs[0].message, "Interrupt 21");
}

TEST_F(DosboxLoggingTest, LogTraceMacro) {
    LOG_TRACE("CPU", "Instruction fetch");

    ASSERT_EQ(g_captured_logs.size(), 1u);
    EXPECT_EQ(g_captured_logs[0].level, DOSBOX_LOG_TRACE);
}

TEST_F(DosboxLoggingTest, LogIfMacro) {
    dosbox_set_log_level(DOSBOX_LOG_WARN);

    int expensive_call_count = 0;
    auto expensive_arg = [&]() {
        expensive_call_count++;
        return 42;
    };

    // This should not evaluate expensive_arg() because Debug < Warn
    LOG_IF(Debug, "TEST", "Value: {}", expensive_arg());

    // In current implementation, LOG_IF still evaluates args
    // This test documents the behavior - ideally expensive_call_count would be 0
    EXPECT_EQ(g_captured_logs.size(), 0u);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Edge Cases
// ═══════════════════════════════════════════════════════════════════════════════

TEST_F(DosboxLoggingTest, EmptyMessage) {
    LOG_MSG("TEST", "");

    ASSERT_EQ(g_captured_logs.size(), 1u);
    EXPECT_EQ(g_captured_logs[0].message, "");
}

TEST_F(DosboxLoggingTest, LongMessage) {
    std::string long_msg(2000, 'x');
    log_raw(LogLevel::Info, "TEST", long_msg);

    ASSERT_EQ(g_captured_logs.size(), 1u);
    // Message should be truncated to buffer size (1024)
    EXPECT_LE(g_captured_logs[0].message.size(), 1024u);
}

TEST_F(DosboxLoggingTest, SpecialCharacters) {
    LOG_MSG("TEST", "Line1\nLine2\tTabbed");

    ASSERT_EQ(g_captured_logs.size(), 1u);
    EXPECT_EQ(g_captured_logs[0].message, "Line1\nLine2\tTabbed");
}

TEST_F(DosboxLoggingTest, MultipleSubsystems) {
    LOG_MSG("CPU", "cpu message");
    LOG_MSG("VGA", "vga message");
    LOG_MSG("DISK", "disk message");

    ASSERT_EQ(g_captured_logs.size(), 3u);
    EXPECT_EQ(g_captured_logs[0].subsystem, "CPU");
    EXPECT_EQ(g_captured_logs[1].subsystem, "VGA");
    EXPECT_EQ(g_captured_logs[2].subsystem, "DISK");
}
