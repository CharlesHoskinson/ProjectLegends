/**
 * @file test_cxx23.cpp
 * @brief C++23 feature validation test.
 *
 * This file is used by CMake's try_compile to verify that the compiler
 * and standard library support the C++23 features required by AIBox.
 *
 * Required features:
 * - std::expected<T, E> from <expected>
 * - std::format from <format>
 * - std::span<T> from <span>
 * - std::ranges from <ranges>
 * - std::source_location from <source_location>
 */

#include <expected>
#include <format>
#include <span>
#include <ranges>
#include <source_location>
#include <string>
#include <vector>

// Test std::expected
std::expected<int, std::string> test_expected(bool succeed) {
    if (succeed) {
        return 42;
    }
    return std::unexpected("error");
}

// Test std::format
std::string test_format() {
    return std::format("Value: {}, Hex: {:x}", 255, 255);
}

// Test std::span
int test_span(std::span<const int> values) {
    int sum = 0;
    for (int v : values) {
        sum += v;
    }
    return sum;
}

// Test std::ranges
int test_ranges() {
    std::vector<int> nums = {1, 2, 3, 4, 5};
    auto even = nums | std::views::filter([](int n) { return n % 2 == 0; });
    int sum = 0;
    for (int n : even) {
        sum += n;
    }
    return sum;
}

// Test std::source_location
const char* test_source_location() {
    auto loc = std::source_location::current();
    return loc.file_name();
}

int main() {
    // Verify all features compile and link
    auto result = test_expected(true);
    if (!result) return 1;

    auto formatted = test_format();
    if (formatted.empty()) return 2;

    int arr[] = {1, 2, 3, 4, 5};
    int sum = test_span(arr);
    if (sum != 15) return 3;

    int even_sum = test_ranges();
    if (even_sum != 6) return 4;

    auto file = test_source_location();
    if (file == nullptr) return 5;

    // All features work
    return 0;
}
