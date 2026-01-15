/**
 * @file test_error.cpp
 * @brief Unit tests for Error class and ErrorCode enum.
 */

#include <gtest/gtest.h>
#include <aibox/error.h>

using namespace aibox;

// ─────────────────────────────────────────────────────────────────────────────
// ErrorCode Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ErrorCodeTest, NameReturnsCorrectString) {
    EXPECT_STREQ(error_code_name(ErrorCode::Ok), "Ok");
    EXPECT_STREQ(error_code_name(ErrorCode::Unknown), "Unknown");
    EXPECT_STREQ(error_code_name(ErrorCode::NotImplemented), "NotImplemented");
    EXPECT_STREQ(error_code_name(ErrorCode::InvalidArgument), "InvalidArgument");
    EXPECT_STREQ(error_code_name(ErrorCode::InvalidState), "InvalidState");
}

TEST(ErrorCodeTest, ResourceErrorCodesHaveNames) {
    EXPECT_STREQ(error_code_name(ErrorCode::OutOfMemory), "OutOfMemory");
    EXPECT_STREQ(error_code_name(ErrorCode::ResourceExhausted), "ResourceExhausted");
    EXPECT_STREQ(error_code_name(ErrorCode::ResourceBusy), "ResourceBusy");
    EXPECT_STREQ(error_code_name(ErrorCode::ResourceNotFound), "ResourceNotFound");
}

TEST(ErrorCodeTest, IoErrorCodesHaveNames) {
    EXPECT_STREQ(error_code_name(ErrorCode::FileNotFound), "FileNotFound");
    EXPECT_STREQ(error_code_name(ErrorCode::FileAccessDenied), "FileAccessDenied");
    EXPECT_STREQ(error_code_name(ErrorCode::FileReadError), "FileReadError");
    EXPECT_STREQ(error_code_name(ErrorCode::FileWriteError), "FileWriteError");
    EXPECT_STREQ(error_code_name(ErrorCode::PathTooLong), "PathTooLong");
}

TEST(ErrorCodeTest, ConfigErrorCodesHaveNames) {
    EXPECT_STREQ(error_code_name(ErrorCode::ConfigParseError), "ConfigParseError");
    EXPECT_STREQ(error_code_name(ErrorCode::ConfigValueInvalid), "ConfigValueInvalid");
    EXPECT_STREQ(error_code_name(ErrorCode::ConfigSectionMissing), "ConfigSectionMissing");
}

TEST(ErrorCodeTest, EmulationErrorCodesHaveNames) {
    EXPECT_STREQ(error_code_name(ErrorCode::CpuError), "CpuError");
    EXPECT_STREQ(error_code_name(ErrorCode::MemoryError), "MemoryError");
    EXPECT_STREQ(error_code_name(ErrorCode::DmaError), "DmaError");
    EXPECT_STREQ(error_code_name(ErrorCode::InterruptError), "InterruptError");
    EXPECT_STREQ(error_code_name(ErrorCode::DeviceError), "DeviceError");
}

TEST(ErrorCodeTest, FfiErrorCodesHaveNames) {
    EXPECT_STREQ(error_code_name(ErrorCode::NullPointer), "NullPointer");
    EXPECT_STREQ(error_code_name(ErrorCode::InvalidHandle), "InvalidHandle");
    EXPECT_STREQ(error_code_name(ErrorCode::BufferTooSmall), "BufferTooSmall");
}

TEST(ErrorCodeTest, UnknownCodeReturnsUnknown) {
    EXPECT_STREQ(error_code_name(static_cast<ErrorCode>(99999)), "Unknown");
    EXPECT_STREQ(error_code_name(static_cast<ErrorCode>(-1)), "Unknown");
}

// ─────────────────────────────────────────────────────────────────────────────
// Error Class Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ErrorTest, ConstructionCapturesAllFields) {
    Error err(ErrorCode::FileNotFound, "test.conf not found");

    EXPECT_EQ(err.code(), ErrorCode::FileNotFound);
    EXPECT_EQ(err.message(), "test.conf not found");
    EXPECT_NE(err.location().line(), 0u);
}

TEST(ErrorTest, CodeAccessorWorks) {
    Error err(ErrorCode::InvalidArgument, "bad value");
    EXPECT_EQ(err.code(), ErrorCode::InvalidArgument);
}

TEST(ErrorTest, MessageAccessorWorks) {
    Error err(ErrorCode::ConfigParseError, "unexpected token");
    EXPECT_EQ(err.message(), "unexpected token");
}

TEST(ErrorTest, LocationCapturesFile) {
    // With explicit location, captures call site
    Error err(ErrorCode::Unknown, "test", AIBOX_CURRENT_LOCATION);
    std::string file = err.location().file_name();
    EXPECT_NE(file.find("test_error"), std::string::npos);
}

TEST(ErrorTest, LocationCapturesLine) {
    // With explicit location, captures call site line
    int line_before = __LINE__;
    Error err(ErrorCode::Unknown, "test", AIBOX_CURRENT_LOCATION);
    int line_after = __LINE__;

    EXPECT_GE(err.location().line(), static_cast<uint32_t>(line_before));
    EXPECT_LE(err.location().line(), static_cast<uint32_t>(line_after));
}

TEST(ErrorTest, FormatIncludesCode) {
    Error err(ErrorCode::InvalidArgument, "bad value");
    std::string formatted = err.format();
    EXPECT_NE(formatted.find("InvalidArgument"), std::string::npos);
}

TEST(ErrorTest, FormatIncludesMessage) {
    Error err(ErrorCode::DmaError, "channel overflow");
    std::string formatted = err.format();
    EXPECT_NE(formatted.find("channel overflow"), std::string::npos);
}

TEST(ErrorTest, FormatIncludesFile) {
    // With explicit location, format includes .cpp extension
    Error err(ErrorCode::Unknown, "test", AIBOX_CURRENT_LOCATION);
    std::string formatted = err.format();
    EXPECT_NE(formatted.find(".cpp"), std::string::npos);
}

TEST(ErrorTest, FormattedConstructorWorks) {
    auto err = Error::formatted(
        ErrorCode::ConfigValueInvalid,
        "Value {} out of range [{}, {}]",
        100, 0, 50
    );

    EXPECT_EQ(err.code(), ErrorCode::ConfigValueInvalid);
    EXPECT_NE(err.message().find("100"), std::string::npos);
    EXPECT_NE(err.message().find("0"), std::string::npos);
    EXPECT_NE(err.message().find("50"), std::string::npos);
}

TEST(ErrorTest, FormattedWithStrings) {
    auto err = Error::formatted(
        ErrorCode::FileNotFound,
        "File '{}' not found in '{}'",
        "config.ini", "/etc"
    );

    EXPECT_NE(err.message().find("config.ini"), std::string::npos);
    EXPECT_NE(err.message().find("/etc"), std::string::npos);
}

TEST(ErrorTest, IsChecksCorrectCode) {
    Error err(ErrorCode::DmaError, "channel fault");

    EXPECT_TRUE(err.is(ErrorCode::DmaError));
    EXPECT_FALSE(err.is(ErrorCode::CpuError));
    EXPECT_FALSE(err.is(ErrorCode::MemoryError));
    EXPECT_FALSE(err.is(ErrorCode::Ok));
}

TEST(ErrorTest, EmptyMessageAllowed) {
    Error err(ErrorCode::Unknown, "");
    EXPECT_EQ(err.message(), "");
}

TEST(ErrorTest, LongMessagePreserved) {
    std::string long_msg(500, 'x');
    Error err(ErrorCode::Unknown, long_msg);
    EXPECT_EQ(err.message(), long_msg);
}

TEST(ErrorTest, CopyConstructorWorks) {
    Error err1(ErrorCode::CpuError, "original");
    Error err2 = err1;

    EXPECT_EQ(err2.code(), err1.code());
    EXPECT_EQ(err2.message(), err1.message());
}

TEST(ErrorTest, MoveConstructorWorks) {
    Error err1(ErrorCode::MemoryError, "moveable");
    Error err2 = std::move(err1);

    EXPECT_EQ(err2.code(), ErrorCode::MemoryError);
    EXPECT_EQ(err2.message(), "moveable");
}

// ─────────────────────────────────────────────────────────────────────────────
// AIBOX_ERROR Macro Test
// ─────────────────────────────────────────────────────────────────────────────

TEST(ErrorMacroTest, AiboxErrorMacroWorks) {
    auto err = AIBOX_ERROR(ErrorCode::InvalidState, "test error");

    EXPECT_EQ(err.code(), ErrorCode::InvalidState);
    EXPECT_EQ(err.message(), "test error");
    EXPECT_NE(err.location().line(), 0u);
}
