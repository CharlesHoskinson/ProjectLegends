/**
 * @file optional_utils.h
 * @brief Utilities for std::optional and std::variant.
 *
 * Provides helper functions for working with optional values
 * and variants, following functional programming patterns.
 */

#pragma once

#include <optional>
#include <variant>
#include <stdexcept>
#include <type_traits>
#include <utility>

namespace aibox {

// ─────────────────────────────────────────────────────────────────────────────
// std::optional Utilities
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Get value from optional or throw.
 *
 * @param opt Optional to unwrap
 * @param msg Error message if empty
 * @return Reference to contained value
 * @throws std::runtime_error if empty
 *
 * Example:
 * @code
 *   std::optional<int> value = get_value();
 *   int& v = unwrap_or_throw(value, "Value not found");
 * @endcode
 */
template<typename T>
[[nodiscard]] T& unwrap_or_throw(
    std::optional<T>& opt,
    const char* msg = "Optional is empty")
{
    if (!opt.has_value()) {
        throw std::runtime_error(msg);
    }
    return *opt;
}

/**
 * @brief Get value from const optional or throw.
 */
template<typename T>
[[nodiscard]] const T& unwrap_or_throw(
    const std::optional<T>& opt,
    const char* msg = "Optional is empty")
{
    if (!opt.has_value()) {
        throw std::runtime_error(msg);
    }
    return *opt;
}

/**
 * @brief Get value from optional or return default.
 *
 * @param opt Optional to unwrap
 * @param default_value Value to return if empty
 * @return Contained value or default
 */
template<typename T, typename U>
[[nodiscard]] T value_or(const std::optional<T>& opt, U&& default_value) {
    return opt.value_or(std::forward<U>(default_value));
}

/**
 * @brief Map optional value through function.
 *
 * If the optional has a value, applies the function and returns
 * an optional containing the result. Otherwise returns empty.
 *
 * @param opt Optional to map
 * @param f Function to apply
 * @return Optional with mapped value, or empty if input empty
 *
 * Example:
 * @code
 *   std::optional<int> x = 5;
 *   auto doubled = map_optional(x, [](int n) { return n * 2; });
 *   // doubled == std::optional<int>(10)
 * @endcode
 */
template<typename T, typename F>
[[nodiscard]] auto map_optional(const std::optional<T>& opt, F&& f)
    -> std::optional<std::invoke_result_t<F, const T&>>
{
    if (opt.has_value()) {
        return std::invoke(std::forward<F>(f), *opt);
    }
    return std::nullopt;
}

/**
 * @brief Map mutable optional value through function.
 */
template<typename T, typename F>
[[nodiscard]] auto map_optional(std::optional<T>& opt, F&& f)
    -> std::optional<std::invoke_result_t<F, T&>>
{
    if (opt.has_value()) {
        return std::invoke(std::forward<F>(f), *opt);
    }
    return std::nullopt;
}

/**
 * @brief Flat map optional value (for functions returning optional).
 *
 * Like map_optional, but for functions that return std::optional.
 * Avoids nested optionals.
 *
 * @param opt Optional to flat map
 * @param f Function returning optional
 * @return Optional from function, or empty if input empty
 *
 * Example:
 * @code
 *   std::optional<int> parse_int(const std::string& s);
 *
 *   std::optional<std::string> input = "42";
 *   auto result = flat_map_optional(input, parse_int);
 *   // result == std::optional<int>(42)
 * @endcode
 */
template<typename T, typename F>
[[nodiscard]] auto flat_map_optional(const std::optional<T>& opt, F&& f)
    -> std::invoke_result_t<F, const T&>
{
    if (opt.has_value()) {
        return std::invoke(std::forward<F>(f), *opt);
    }
    return std::nullopt;
}

/**
 * @brief Filter optional based on predicate.
 *
 * Returns the optional if it has a value and satisfies the predicate,
 * otherwise returns empty.
 *
 * @param opt Optional to filter
 * @param pred Predicate to test
 * @return Optional if predicate passes, empty otherwise
 */
template<typename T, typename Pred>
[[nodiscard]] std::optional<T> filter_optional(
    const std::optional<T>& opt, Pred&& pred)
{
    if (opt.has_value() && std::invoke(std::forward<Pred>(pred), *opt)) {
        return opt;
    }
    return std::nullopt;
}

/**
 * @brief Apply side-effect function if optional has value.
 *
 * @param opt Optional to inspect
 * @param f Function to apply to value
 * @return Reference to original optional (for chaining)
 */
template<typename T, typename F>
const std::optional<T>& if_present(const std::optional<T>& opt, F&& f) {
    if (opt.has_value()) {
        std::invoke(std::forward<F>(f), *opt);
    }
    return opt;
}

/**
 * @brief Apply side-effect function if optional is empty.
 *
 * @param opt Optional to inspect
 * @param f Function to call if empty
 * @return Reference to original optional (for chaining)
 */
template<typename T, typename F>
const std::optional<T>& if_empty(const std::optional<T>& opt, F&& f) {
    if (!opt.has_value()) {
        std::invoke(std::forward<F>(f));
    }
    return opt;
}

// ─────────────────────────────────────────────────────────────────────────────
// std::variant Utilities
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Check if variant holds specific type.
 *
 * @tparam T Type to check for
 * @param v Variant to check
 * @return true if variant holds type T
 *
 * Example:
 * @code
 *   std::variant<int, std::string> v = 42;
 *   if (holds<int>(v)) {
 *       std::cout << std::get<int>(v);
 *   }
 * @endcode
 */
template<typename T, typename... Types>
[[nodiscard]] constexpr bool holds(const std::variant<Types...>& v) noexcept {
    return std::holds_alternative<T>(v);
}

/**
 * @brief Get value from variant or return default.
 *
 * @tparam T Type to get
 * @param v Variant to get from
 * @param default_value Value to return if variant doesn't hold T
 * @return Value of type T from variant or default
 */
template<typename T, typename... Types>
[[nodiscard]] T get_or(const std::variant<Types...>& v, T default_value) {
    if (auto* ptr = std::get_if<T>(&v)) {
        return *ptr;
    }
    return default_value;
}

/**
 * @brief Visit variant with visitor function.
 *
 * Wrapper around std::visit with better error messages.
 *
 * @param vis Visitor callable
 * @param vars Variants to visit
 * @return Result of visiting
 */
template<typename Visitor, typename... Variants>
[[nodiscard]] constexpr decltype(auto) visit_variant(
    Visitor&& vis,
    Variants&&... vars)
{
    return std::visit(std::forward<Visitor>(vis),
                      std::forward<Variants>(vars)...);
}

/**
 * @brief Get pointer to variant value if it holds the type.
 *
 * @tparam T Type to get pointer to
 * @param v Variant to get from
 * @return Pointer to value if variant holds T, nullptr otherwise
 */
template<typename T, typename... Types>
[[nodiscard]] constexpr T* get_if_ptr(std::variant<Types...>& v) noexcept {
    return std::get_if<T>(&v);
}

/**
 * @brief Get const pointer to variant value if it holds the type.
 */
template<typename T, typename... Types>
[[nodiscard]] constexpr const T* get_if_ptr(
    const std::variant<Types...>& v) noexcept
{
    return std::get_if<T>(&v);
}

/**
 * @brief Overload pattern helper for std::visit.
 *
 * Combines multiple lambdas into a single visitor.
 *
 * Example:
 * @code
 *   std::variant<int, std::string> v = "hello";
 *   std::visit(overload{
 *       [](int i) { std::cout << "int: " << i; },
 *       [](const std::string& s) { std::cout << "string: " << s; }
 *   }, v);
 * @endcode
 */
template<class... Ts>
struct overload : Ts... {
    using Ts::operator()...;
};

// Deduction guide for C++17
template<class... Ts>
overload(Ts...) -> overload<Ts...>;

/**
 * @brief Match variant and call appropriate handler.
 *
 * Convenience function combining overload and std::visit.
 *
 * @param v Variant to match
 * @param handlers Handlers for each type
 * @return Result of matched handler
 *
 * Example:
 * @code
 *   std::variant<int, std::string, double> v = 3.14;
 *   match(v,
 *       [](int i) { return std::to_string(i); },
 *       [](double d) { return std::to_string(d); },
 *       [](const std::string& s) { return s; }
 *   );
 * @endcode
 */
template<typename Variant, typename... Handlers>
[[nodiscard]] decltype(auto) match(Variant&& v, Handlers&&... handlers) {
    return std::visit(
        overload{std::forward<Handlers>(handlers)...},
        std::forward<Variant>(v)
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Optional<Result> Combination
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Convert optional to pointer.
 *
 * Returns pointer to contained value, or nullptr if empty.
 *
 * @param opt Optional to convert
 * @return Pointer to value or nullptr
 */
template<typename T>
[[nodiscard]] T* to_pointer(std::optional<T>& opt) noexcept {
    return opt.has_value() ? &*opt : nullptr;
}

/**
 * @brief Convert optional to const pointer.
 */
template<typename T>
[[nodiscard]] const T* to_pointer(const std::optional<T>& opt) noexcept {
    return opt.has_value() ? &*opt : nullptr;
}

} // namespace aibox
