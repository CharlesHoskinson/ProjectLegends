/**
 * @file test_input_integration.cpp
 * @brief Unit tests for platform input integration (PR #19).
 *
 * Tests:
 * - Headless stub input provider integration
 * - DOSBoxContext input provider configuration
 * - ThreadSafeInput through context
 * - Custom input provider injection
 * - Input event injection and polling
 */

#include <gtest/gtest.h>
#include "dosbox/dosbox_context.h"
#include "dosbox/platform/input.h"
#include "dosbox/platform/headless.h"
#include "aibox/headless_stub.h"

using namespace dosbox;
using namespace dosbox::platform;

// ═══════════════════════════════════════════════════════════════════════════════
// Headless Stub Input Provider Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(HeadlessInputTest, DefaultNoProvider) {
    // Clear any existing provider
    aibox::headless::SetInputProvider(nullptr);

    EXPECT_FALSE(aibox::headless::HasInputProvider());
    EXPECT_EQ(aibox::headless::GetInputProvider(), nullptr);
}

TEST(HeadlessInputTest, SetInputProvider) {
    ThreadSafeInput input;

    aibox::headless::SetInputProvider(&input);

    EXPECT_TRUE(aibox::headless::HasInputProvider());
    EXPECT_EQ(aibox::headless::GetInputProvider(), &input);

    // Clean up
    aibox::headless::SetInputProvider(nullptr);
}

TEST(HeadlessInputTest, PushKeyEventUsesProvider) {
    ThreadSafeInput input;
    aibox::headless::SetInputProvider(&input);

    // Push key event through headless stub
    bool result = aibox::headless::PushKeyEvent(
        static_cast<uint16_t>(KeyCode::A), true);

    EXPECT_TRUE(result);
    EXPECT_TRUE(input.has_events());

    // Poll and verify
    auto event = input.poll_event();
    ASSERT_TRUE(event.has_value());
    EXPECT_EQ(event->type, InputEventType::KeyDown);
    EXPECT_EQ(event->key.code, KeyCode::A);

    // Clean up
    aibox::headless::SetInputProvider(nullptr);
}

TEST(HeadlessInputTest, PushKeyUpEvent) {
    ThreadSafeInput input;
    aibox::headless::SetInputProvider(&input);

    // Push key up event
    aibox::headless::PushKeyEvent(
        static_cast<uint16_t>(KeyCode::Escape), false);

    auto event = input.poll_event();
    ASSERT_TRUE(event.has_value());
    EXPECT_EQ(event->type, InputEventType::KeyUp);
    EXPECT_EQ(event->key.code, KeyCode::Escape);

    // Clean up
    aibox::headless::SetInputProvider(nullptr);
}

TEST(HeadlessInputTest, PushMouseMotionUsesProvider) {
    ThreadSafeInput input;
    aibox::headless::SetInputProvider(&input);

    // Push mouse motion
    bool result = aibox::headless::PushMouseMotion(10, -5);

    EXPECT_TRUE(result);

    auto event = input.poll_event();
    ASSERT_TRUE(event.has_value());
    EXPECT_EQ(event->type, InputEventType::MouseMotion);
    EXPECT_EQ(event->mouse_motion.dx, 10);
    EXPECT_EQ(event->mouse_motion.dy, -5);

    // Clean up
    aibox::headless::SetInputProvider(nullptr);
}

TEST(HeadlessInputTest, PushMouseButtonUsesProvider) {
    ThreadSafeInput input;
    aibox::headless::SetInputProvider(&input);

    // Push mouse button down
    aibox::headless::PushMouseButton(0, true);  // Left button

    auto event = input.poll_event();
    ASSERT_TRUE(event.has_value());
    EXPECT_EQ(event->type, InputEventType::MouseButtonDown);
    EXPECT_EQ(event->mouse_button.button, MouseButton::Left);

    // Push mouse button up
    aibox::headless::PushMouseButton(2, false);  // Right button

    event = input.poll_event();
    ASSERT_TRUE(event.has_value());
    EXPECT_EQ(event->type, InputEventType::MouseButtonUp);
    EXPECT_EQ(event->mouse_button.button, MouseButton::Right);

    // Clean up
    aibox::headless::SetInputProvider(nullptr);
}

TEST(HeadlessInputTest, PushInputEventUsesProvider) {
    ThreadSafeInput input;
    aibox::headless::SetInputProvider(&input);

    // Create and push raw event
    InputEvent event = InputEvent::wheel(0, -3);
    bool result = aibox::headless::PushInputEvent(event);

    EXPECT_TRUE(result);

    auto polled = input.poll_event();
    ASSERT_TRUE(polled.has_value());
    EXPECT_EQ(polled->type, InputEventType::MouseWheel);
    EXPECT_EQ(polled->mouse_wheel.dy, -3);

    // Clean up
    aibox::headless::SetInputProvider(nullptr);
}

TEST(HeadlessInputTest, PushFailsWithNoProvider) {
    aibox::headless::SetInputProvider(nullptr);

    bool result = aibox::headless::PushKeyEvent(
        static_cast<uint16_t>(KeyCode::A), true);

    EXPECT_FALSE(result);
}

// ═══════════════════════════════════════════════════════════════════════════════
// DOSBoxContext Input Provider Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(ContextInputTest, HasBuiltInThreadSafeInput) {
    DOSBoxContext ctx;

    // Context has its own thread-safe input
    auto& input = ctx.thread_safe_input();

    // Should be empty initially
    EXPECT_FALSE(input.has_events());
}

TEST(ContextInputTest, DefaultNoCustomProvider) {
    DOSBoxContext ctx;

    EXPECT_EQ(ctx.get_input_provider(), nullptr);
}

TEST(ContextInputTest, SetCustomInputProvider) {
    DOSBoxContext ctx;
    ThreadSafeInput custom_input;

    ctx.set_input_provider(&custom_input);

    EXPECT_EQ(ctx.get_input_provider(), &custom_input);
}

TEST(ContextInputTest, CurrentContextUsesBuiltInInput) {
    DOSBoxContext ctx;
    ctx.initialize();

    // Clear any previous state
    aibox::headless::SetInputProvider(nullptr);

    // Set as current context
    ContextGuard guard(ctx);

    // Should have wired up the built-in thread-safe input
    EXPECT_TRUE(aibox::headless::HasInputProvider());
    EXPECT_EQ(aibox::headless::GetInputProvider(), &ctx.thread_safe_input());
}

TEST(ContextInputTest, CurrentContextUsesCustomProvider) {
    DOSBoxContext ctx;
    ctx.initialize();
    ThreadSafeInput custom_input;

    // Set custom provider
    ctx.set_input_provider(&custom_input);

    // Set as current context
    ContextGuard guard(ctx);

    // Should use custom provider
    EXPECT_EQ(aibox::headless::GetInputProvider(), &custom_input);
}

TEST(ContextInputTest, ContextSwitchingUpdatesProvider) {
    DOSBoxContext ctx1;
    DOSBoxContext ctx2;
    ctx1.initialize();
    ctx2.initialize();

    // Push event to ctx1's input
    ctx1.thread_safe_input().push_key(KeyCode::A, true);

    // Push different event to ctx2's input
    ctx2.thread_safe_input().push_key(KeyCode::B, true);

    {
        ContextGuard guard1(ctx1);
        auto* provider = aibox::headless::GetInputProvider();
        EXPECT_EQ(provider, &ctx1.thread_safe_input());
        EXPECT_TRUE(provider->has_events());

        auto event = provider->poll_event();
        ASSERT_TRUE(event.has_value());
        EXPECT_EQ(event->key.code, KeyCode::A);
    }

    {
        ContextGuard guard2(ctx2);
        auto* provider = aibox::headless::GetInputProvider();
        EXPECT_EQ(provider, &ctx2.thread_safe_input());
        EXPECT_TRUE(provider->has_events());

        auto event = provider->poll_event();
        ASSERT_TRUE(event.has_value());
        EXPECT_EQ(event->key.code, KeyCode::B);
    }
}

TEST(ContextInputTest, ClearCurrentContextClearsProvider) {
    DOSBoxContext ctx;
    ctx.initialize();

    set_current_context(&ctx);
    EXPECT_TRUE(aibox::headless::HasInputProvider());

    set_current_context(nullptr);
    EXPECT_FALSE(aibox::headless::HasInputProvider());
}

// ═══════════════════════════════════════════════════════════════════════════════
// Headless Backend Integration Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(HeadlessBackendInputTest, BackendInputIntegration) {
    auto backend = make_headless_backend();
    DOSBoxContext ctx;
    ctx.initialize();

    // Use headless backend input with context
    ctx.set_input_provider(&backend->input);

    ContextGuard guard(ctx);

    // Input should flow through backend
    aibox::headless::PushKeyEvent(
        static_cast<uint16_t>(KeyCode::Space), true);

    EXPECT_TRUE(backend->input.has_events());

    auto event = backend->input.poll_event();
    ASSERT_TRUE(event.has_value());
    EXPECT_EQ(event->key.code, KeyCode::Space);
}

// ═══════════════════════════════════════════════════════════════════════════════
// Input Event Sequence Tests
// ═══════════════════════════════════════════════════════════════════════════════

TEST(InputSequenceTest, TypeString) {
    DOSBoxContext ctx;
    ctx.initialize();

    ContextGuard guard(ctx);

    // Simulate typing "AB"
    aibox::headless::PushKeyEvent(static_cast<uint16_t>(KeyCode::A), true);
    aibox::headless::PushKeyEvent(static_cast<uint16_t>(KeyCode::A), false);
    aibox::headless::PushKeyEvent(static_cast<uint16_t>(KeyCode::B), true);
    aibox::headless::PushKeyEvent(static_cast<uint16_t>(KeyCode::B), false);

    auto& input = ctx.thread_safe_input();

    // Should have 4 events
    auto e1 = input.poll_event();
    EXPECT_EQ(e1->type, InputEventType::KeyDown);
    EXPECT_EQ(e1->key.code, KeyCode::A);

    auto e2 = input.poll_event();
    EXPECT_EQ(e2->type, InputEventType::KeyUp);
    EXPECT_EQ(e2->key.code, KeyCode::A);

    auto e3 = input.poll_event();
    EXPECT_EQ(e3->type, InputEventType::KeyDown);
    EXPECT_EQ(e3->key.code, KeyCode::B);

    auto e4 = input.poll_event();
    EXPECT_EQ(e4->type, InputEventType::KeyUp);
    EXPECT_EQ(e4->key.code, KeyCode::B);

    // Queue should be empty
    EXPECT_FALSE(input.has_events());
}

TEST(InputSequenceTest, MouseClick) {
    DOSBoxContext ctx;
    ctx.initialize();

    ContextGuard guard(ctx);

    // Simulate mouse click at position
    aibox::headless::PushMouseMotion(100, 50);
    aibox::headless::PushMouseButton(0, true);   // Left down
    aibox::headless::PushMouseButton(0, false);  // Left up

    auto& input = ctx.thread_safe_input();

    auto e1 = input.poll_event();
    EXPECT_EQ(e1->type, InputEventType::MouseMotion);

    auto e2 = input.poll_event();
    EXPECT_EQ(e2->type, InputEventType::MouseButtonDown);

    auto e3 = input.poll_event();
    EXPECT_EQ(e3->type, InputEventType::MouseButtonUp);
}

TEST(InputSequenceTest, InputPreservedAcrossContextSwitch) {
    DOSBoxContext ctx1;
    DOSBoxContext ctx2;
    ctx1.initialize();
    ctx2.initialize();

    // Inject events into each context
    {
        ContextGuard guard1(ctx1);
        aibox::headless::PushKeyEvent(static_cast<uint16_t>(KeyCode::Num1), true);
        aibox::headless::PushKeyEvent(static_cast<uint16_t>(KeyCode::Num2), true);
    }

    {
        ContextGuard guard2(ctx2);
        aibox::headless::PushKeyEvent(static_cast<uint16_t>(KeyCode::Num3), true);
    }

    // Verify events are preserved in each context
    EXPECT_EQ(ctx1.thread_safe_input().queue_size(), 2u);
    EXPECT_EQ(ctx2.thread_safe_input().queue_size(), 1u);

    // Poll ctx1 events
    auto e1 = ctx1.thread_safe_input().poll_event();
    EXPECT_EQ(e1->key.code, KeyCode::Num1);

    auto e2 = ctx1.thread_safe_input().poll_event();
    EXPECT_EQ(e2->key.code, KeyCode::Num2);

    // Poll ctx2 events
    auto e3 = ctx2.thread_safe_input().poll_event();
    EXPECT_EQ(e3->key.code, KeyCode::Num3);
}
