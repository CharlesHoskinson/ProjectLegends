/**
 * @file function_ref.h
 * @brief Non-owning, non-allocating function reference.
 *
 * Use for hot-path callbacks where std::function overhead
 * is unacceptable. Similar to std::string_view for strings.
 *
 * @warning The referenced callable must outlive the function_ref.
 */

#pragma once

#include <type_traits>
#include <utility>
#include <cstddef>

namespace legends {

/**
 * @brief Non-owning reference to a callable.
 *
 * Zero overhead compared to function pointer + userdata pattern.
 * Type-erased: can reference lambdas, function pointers, functors.
 *
 * @tparam Signature Function signature (e.g., void(int), int(float, float))
 *
 * Example:
 * @code
 *   void process(function_ref<int(int)> callback) {
 *       int result = callback(42);
 *   }
 *
 *   // Call with lambda
 *   process([](int x) { return x * 2; });
 *
 *   // Call with function pointer
 *   int double_it(int x) { return x * 2; }
 *   process(double_it);
 * @endcode
 */
template<typename Signature>
class function_ref;

template<typename R, typename... Args>
class function_ref<R(Args...)> {
public:
    /**
     * @brief Construct from any callable.
     *
     * @tparam F Callable type (lambda, functor, function pointer)
     * @param f Reference to callable (must outlive this function_ref)
     */
    template<typename F,
             typename = std::enable_if_t<
                 std::is_invocable_r_v<R, F&, Args...> &&
                 !std::is_same_v<std::decay_t<F>, function_ref>
             >>
    constexpr function_ref(F& f) noexcept
        : obj_(const_cast<void*>(static_cast<const void*>(std::addressof(f))))
        , invoke_(&invoke_impl<F>)
    {}

    /**
     * @brief Construct from function pointer.
     */
    constexpr function_ref(R (*f)(Args...)) noexcept
        : obj_(reinterpret_cast<void*>(f))
        , invoke_(&invoke_fn_ptr)
    {}

    // Copyable
    constexpr function_ref(const function_ref&) noexcept = default;
    constexpr function_ref& operator=(const function_ref&) noexcept = default;

    /**
     * @brief Invoke the referenced callable.
     */
    constexpr R operator()(Args... args) const {
        return invoke_(obj_, std::forward<Args>(args)...);
    }

    /**
     * @brief Swap two function_refs.
     */
    constexpr void swap(function_ref& other) noexcept {
        std::swap(obj_, other.obj_);
        std::swap(invoke_, other.invoke_);
    }

private:
    void* obj_;
    R (*invoke_)(void*, Args...);

    template<typename F>
    static R invoke_impl(void* obj, Args... args) {
        return (*static_cast<F*>(obj))(std::forward<Args>(args)...);
    }

    static R invoke_fn_ptr(void* obj, Args... args) {
        return reinterpret_cast<R(*)(Args...)>(obj)(std::forward<Args>(args)...);
    }
};

// Deduction guide for function pointers
template<typename R, typename... Args>
function_ref(R (*)(Args...)) -> function_ref<R(Args...)>;

/**
 * @brief Swap two function_refs.
 */
template<typename Sig>
constexpr void swap(function_ref<Sig>& lhs, function_ref<Sig>& rhs) noexcept {
    lhs.swap(rhs);
}

} // namespace legends
