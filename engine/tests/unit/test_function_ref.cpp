/**
 * @file test_function_ref.cpp
 * @brief Unit tests for function_ref class.
 */

#include <gtest/gtest.h>
#include <aibox/function_ref.h>

using namespace aibox;

// ─────────────────────────────────────────────────────────────────────────────
// Basic Invocation Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(FunctionRefTest, InvokesLambda) {
    auto lambda = [](int x) { return x * 2; };
    function_ref<int(int)> ref(lambda);

    EXPECT_EQ(ref(21), 42);
}

TEST(FunctionRefTest, InvokesLambdaWithCapture) {
    int multiplier = 3;
    auto lambda = [&multiplier](int x) { return x * multiplier; };
    function_ref<int(int)> ref(lambda);

    EXPECT_EQ(ref(14), 42);
}

TEST(FunctionRefTest, InvokesMutableLambda) {
    int counter = 0;
    auto lambda = [&counter]() mutable { return ++counter; };
    function_ref<int()> ref(lambda);

    EXPECT_EQ(ref(), 1);
    EXPECT_EQ(ref(), 2);
    EXPECT_EQ(ref(), 3);
    EXPECT_EQ(counter, 3);
}

// Free function for testing
static int free_function(int x) { return x + 1; }

TEST(FunctionRefTest, InvokesFreeFunction) {
    function_ref<int(int)> ref(free_function);

    EXPECT_EQ(ref(41), 42);
}

TEST(FunctionRefTest, InvokesConvertedLambda) {
    // Lambda converted to function pointer
    auto fn = +[](int x) -> int { return x * 2; };
    function_ref<int(int)> ref(fn);

    EXPECT_EQ(ref(21), 42);
}

TEST(FunctionRefTest, InvokesFunctor) {
    struct Functor {
        int value;
        int operator()(int x) const { return x + value; }
    };

    Functor f{40};
    function_ref<int(int)> ref(f);

    EXPECT_EQ(ref(2), 42);
}

// ─────────────────────────────────────────────────────────────────────────────
// Copy and Assignment Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(FunctionRefTest, CopyConstructor) {
    auto lambda = [](int x) { return x * 2; };
    function_ref<int(int)> ref1(lambda);
    function_ref<int(int)> ref2(ref1);

    EXPECT_EQ(ref1(10), 20);
    EXPECT_EQ(ref2(10), 20);
}

TEST(FunctionRefTest, CopyAssignment) {
    auto lambda1 = [](int x) { return x * 2; };
    auto lambda2 = [](int x) { return x * 3; };

    function_ref<int(int)> ref1(lambda1);
    function_ref<int(int)> ref2(lambda2);

    EXPECT_EQ(ref2(10), 30);

    ref2 = ref1;

    EXPECT_EQ(ref2(10), 20);
}

// ─────────────────────────────────────────────────────────────────────────────
// Void Return Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(FunctionRefTest, VoidReturn) {
    int called = 0;
    auto lambda = [&called]() { called++; };
    function_ref<void()> ref(lambda);

    ref();
    ref();

    EXPECT_EQ(called, 2);
}

TEST(FunctionRefTest, VoidReturnWithArgs) {
    int result = 0;
    auto lambda = [&result](int a, int b) { result = a + b; };
    function_ref<void(int, int)> ref(lambda);

    ref(10, 32);

    EXPECT_EQ(result, 42);
}

// ─────────────────────────────────────────────────────────────────────────────
// Multiple Arguments Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(FunctionRefTest, TwoArguments) {
    auto lambda = [](int a, int b) { return a + b; };
    function_ref<int(int, int)> ref(lambda);

    EXPECT_EQ(ref(10, 32), 42);
}

TEST(FunctionRefTest, ThreeArguments) {
    auto lambda = [](int a, int b, int c) { return a + b + c; };
    function_ref<int(int, int, int)> ref(lambda);

    EXPECT_EQ(ref(1, 2, 3), 6);
}

TEST(FunctionRefTest, FourArguments) {
    auto lambda = [](int a, int b, int c, int d) { return a * b + c * d; };
    function_ref<int(int, int, int, int)> ref(lambda);

    EXPECT_EQ(ref(2, 3, 6, 6), 42);  // 2*3 + 6*6 = 6 + 36 = 42
}

// ─────────────────────────────────────────────────────────────────────────────
// Reference Arguments Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(FunctionRefTest, ReferenceArgument) {
    auto lambda = [](int& x) { x = 42; };
    function_ref<void(int&)> ref(lambda);

    int value = 0;
    ref(value);

    EXPECT_EQ(value, 42);
}

TEST(FunctionRefTest, ConstReferenceArgument) {
    auto lambda = [](const std::string& s) { return s.length(); };
    function_ref<size_t(const std::string&)> ref(lambda);

    std::string str = "hello";
    EXPECT_EQ(ref(str), 5u);
}

// ─────────────────────────────────────────────────────────────────────────────
// Swap Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(FunctionRefTest, MemberSwap) {
    auto lambda1 = [](int x) { return x * 2; };
    auto lambda2 = [](int x) { return x * 3; };

    function_ref<int(int)> ref1(lambda1);
    function_ref<int(int)> ref2(lambda2);

    EXPECT_EQ(ref1(10), 20);
    EXPECT_EQ(ref2(10), 30);

    ref1.swap(ref2);

    EXPECT_EQ(ref1(10), 30);
    EXPECT_EQ(ref2(10), 20);
}

TEST(FunctionRefTest, FreeSwap) {
    auto lambda1 = [](int x) { return x * 2; };
    auto lambda2 = [](int x) { return x * 3; };

    function_ref<int(int)> ref1(lambda1);
    function_ref<int(int)> ref2(lambda2);

    swap(ref1, ref2);

    EXPECT_EQ(ref1(10), 30);
    EXPECT_EQ(ref2(10), 20);
}

// ─────────────────────────────────────────────────────────────────────────────
// Deduction Guide Test
// ─────────────────────────────────────────────────────────────────────────────

TEST(FunctionRefTest, DeductionGuideFromFunctionPointer) {
    // Uses CTAD with function pointer
    function_ref ref(free_function);

    EXPECT_EQ(ref(41), 42);
}

// ─────────────────────────────────────────────────────────────────────────────
// Size Test (ensuring it's lightweight)
// ─────────────────────────────────────────────────────────────────────────────

TEST(FunctionRefTest, SizeIsTwoPointers) {
    // function_ref should be exactly two pointers in size
    EXPECT_EQ(sizeof(function_ref<int(int)>), 2 * sizeof(void*));
}

// ─────────────────────────────────────────────────────────────────────────────
// Return Value Forwarding
// ─────────────────────────────────────────────────────────────────────────────

TEST(FunctionRefTest, ReturnsStruct) {
    struct Point { int x, y; };

    auto lambda = []() { return Point{10, 20}; };
    function_ref<Point()> ref(lambda);

    Point p = ref();
    EXPECT_EQ(p.x, 10);
    EXPECT_EQ(p.y, 20);
}

TEST(FunctionRefTest, ReturnsReference) {
    int value = 42;
    auto lambda = [&value]() -> int& { return value; };
    function_ref<int&()> ref(lambda);

    int& result = ref();
    EXPECT_EQ(&result, &value);
}
