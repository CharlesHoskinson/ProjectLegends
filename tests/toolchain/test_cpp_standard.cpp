/**
 * @file test_cpp_standard.cpp
 * @brief Compile-time verification that C++23 mode is active.
 *
 * This file serves as a CI gate to ensure the build system correctly
 * enables C++23. If this file compiles, the toolchain is configured correctly.
 *
 * Why this matters:
 * - MSVC command lines can be surprising (/std:c++latest vs /std:c++23preview)
 * - CMake version mismatches can silently fall back to older standards
 * - This gives immediate, clear feedback when the toolchain is misconfigured
 *
 * @copyright GPL-2.0-or-later
 */

// ═══════════════════════════════════════════════════════════════════════════
// C++23 Standard Verification
// ═══════════════════════════════════════════════════════════════════════════

// C++23 defines __cplusplus as 202302L, but GCC 13 uses 202100L (C++2b draft)
// even when invoked with -std=c++23. GCC 14+ uses the official 202302L value.
// MSVC uses _MSVC_LANG instead of __cplusplus for standard version.
#if defined(_MSVC_LANG)
    static_assert(_MSVC_LANG >= 202302L,
        "MSVC is not compiling in C++23 mode. "
        "Expected _MSVC_LANG >= 202302L (C++23). "
        "Check that /std:c++23preview is set.");
#else
    static_assert(__cplusplus >= 202100L,
        "Not compiling in C++23 mode. "
        "Expected __cplusplus >= 202100L (C++23 or C++2b draft). "
        "Check CMAKE_CXX_STANDARD and compiler flags.");
#endif

// ═══════════════════════════════════════════════════════════════════════════
// C++23 Feature Tests (compile-time verification)
// ═══════════════════════════════════════════════════════════════════════════

#include <version>

// std::expected (P0323R12) - core to our error model
#if defined(__cpp_lib_expected)
    static_assert(__cpp_lib_expected >= 202202L,
        "std::expected feature test macro too old");
#else
    #error "std::expected not available - C++23 library support incomplete"
#endif

// std::format (P2216R3) - used in error formatting
// Note: libc++ (used with clang sanitizer builds) may lack std::format
// even with C++23 mode. This is a known limitation of older libc++ versions.
#if defined(__cpp_lib_format)
    static_assert(__cpp_lib_format >= 202110L,
        "std::format feature test macro too old");
    #define LEGENDS_HAS_FORMAT 1
#else
    #pragma message("std::format not available - some C++23 library features missing (libc++ limitation)")
    #define LEGENDS_HAS_FORMAT 0
#endif

// std::ranges (P2387R3) - useful for data processing
#if defined(__cpp_lib_ranges)
    static_assert(__cpp_lib_ranges >= 202110L,
        "std::ranges feature test macro too old");
#else
    #error "std::ranges not available - C++23 library support incomplete"
#endif

// Deducing this (P0847R7) - language feature
#if defined(__cpp_explicit_this_parameter)
    static_assert(__cpp_explicit_this_parameter >= 202110L,
        "Deducing this feature test macro too old");
#endif
// Note: Not all compilers support this yet, so we don't #error

// ═══════════════════════════════════════════════════════════════════════════
// Runtime Test (optional - mainly for CI reporting)
// ═══════════════════════════════════════════════════════════════════════════

#include <gtest/gtest.h>
#include <expected>
#if LEGENDS_HAS_FORMAT
#include <format>
#endif
#include <span>

namespace {

TEST(CppStandard, VersionMacro) {
#if defined(_MSVC_LANG)
    EXPECT_GE(_MSVC_LANG, 202302L) << "MSVC not in C++23 mode";
    // Log the actual value for debugging
    std::cout << "_MSVC_LANG = " << _MSVC_LANG << std::endl;
#else
    EXPECT_GE(__cplusplus, 202100L) << "Not in C++23 mode";
    std::cout << "__cplusplus = " << __cplusplus << std::endl;
#endif
}

TEST(CppStandard, ExpectedAvailable) {
    // Verify std::expected works as expected
    std::expected<int, std::string> ok_result = 42;
    EXPECT_TRUE(ok_result.has_value());
    EXPECT_EQ(ok_result.value(), 42);

    std::expected<int, std::string> err_result = std::unexpected("error");
    EXPECT_FALSE(err_result.has_value());
    EXPECT_EQ(err_result.error(), "error");
}

#if LEGENDS_HAS_FORMAT
TEST(CppStandard, FormatAvailable) {
    // Verify std::format works
    std::string result = std::format("Hello, {}!", "C++23");
    EXPECT_EQ(result, "Hello, C++23!");

    result = std::format("{:08X}", 0xDEADBEEF);
    EXPECT_EQ(result, "DEADBEEF");
}
#endif

TEST(CppStandard, SpanAvailable) {
    // Verify std::span works (C++20, but ensure library is complete)
    int arr[] = {1, 2, 3, 4, 5};
    std::span<int> s(arr);
    EXPECT_EQ(s.size(), 5u);
    EXPECT_EQ(s[0], 1);
    EXPECT_EQ(s[4], 5);
}

} // namespace
