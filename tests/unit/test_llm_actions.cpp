/**
 * @file test_llm_actions.cpp
 * @brief Unit tests for LLM action types.
 */

#include <gtest/gtest.h>
#include <legends/llm_actions.h>

using namespace legends::llm;

// ─────────────────────────────────────────────────────────────────────────────
// TypeAction Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(TypeActionTest, DefaultConstruction) {
    TypeAction action{};

    EXPECT_TRUE(action.text.empty());
    EXPECT_EQ(action.delay_between_ms, 0u);
}

TEST(TypeActionTest, WithText) {
    TypeAction action{"Hello World", 10};

    EXPECT_EQ(action.text, "Hello World");
    EXPECT_EQ(action.delay_between_ms, 10u);
}

TEST(TypeActionTest, Equality) {
    TypeAction a{"test", 5};
    TypeAction b{"test", 5};
    TypeAction c{"other", 5};

    EXPECT_EQ(a, b);
    EXPECT_NE(a, c);
}

// ─────────────────────────────────────────────────────────────────────────────
// MouseButton Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(MouseButtonTest, ToString) {
    EXPECT_STREQ(to_string(MouseButton::Left), "left");
    EXPECT_STREQ(to_string(MouseButton::Right), "right");
    EXPECT_STREQ(to_string(MouseButton::Middle), "middle");
}

TEST(MouseButtonTest, Values) {
    EXPECT_EQ(static_cast<uint8_t>(MouseButton::Left), 0);
    EXPECT_EQ(static_cast<uint8_t>(MouseButton::Right), 1);
    EXPECT_EQ(static_cast<uint8_t>(MouseButton::Middle), 2);
}

// ─────────────────────────────────────────────────────────────────────────────
// ClickAction Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ClickActionTest, DefaultConstruction) {
    ClickAction action{};

    EXPECT_EQ(action.x, 0);
    EXPECT_EQ(action.y, 0);
    EXPECT_EQ(action.button, MouseButton::Left);
    EXPECT_FALSE(action.double_click);
    EXPECT_TRUE(action.text_coordinates);
}

TEST(ClickActionTest, WithCoordinates) {
    ClickAction action{10, 5, MouseButton::Right, true, false};

    EXPECT_EQ(action.x, 10);
    EXPECT_EQ(action.y, 5);
    EXPECT_EQ(action.button, MouseButton::Right);
    EXPECT_TRUE(action.double_click);
    EXPECT_FALSE(action.text_coordinates);
}

TEST(ClickActionTest, Equality) {
    ClickAction a{10, 5, MouseButton::Left, false, true};
    ClickAction b{10, 5, MouseButton::Left, false, true};
    ClickAction c{10, 6, MouseButton::Left, false, true};

    EXPECT_EQ(a, b);
    EXPECT_NE(a, c);
}

// ─────────────────────────────────────────────────────────────────────────────
// WaitAction Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(WaitActionTest, DefaultConstruction) {
    WaitAction action{};

    EXPECT_EQ(action.milliseconds, 0u);
    EXPECT_FALSE(action.wait_for_idle);
}

TEST(WaitActionTest, WithDuration) {
    WaitAction action{500, true};

    EXPECT_EQ(action.milliseconds, 500u);
    EXPECT_TRUE(action.wait_for_idle);
}

TEST(WaitActionTest, Equality) {
    WaitAction a{100, false};
    WaitAction b{100, false};
    WaitAction c{200, false};

    EXPECT_EQ(a, b);
    EXPECT_NE(a, c);
}

// ─────────────────────────────────────────────────────────────────────────────
// HypercallAction Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(HypercallActionTest, DefaultConstruction) {
    HypercallAction action{};

    EXPECT_EQ(action.command_id, 0);
    EXPECT_EQ(action.param_a, 0u);
    EXPECT_EQ(action.param_b, 0u);
    EXPECT_TRUE(action.wait_for_response);
}

TEST(HypercallActionTest, WithParams) {
    HypercallAction action{0x0001, 0x12345678, 0xABCDEF00, false};

    EXPECT_EQ(action.command_id, 0x0001);
    EXPECT_EQ(action.param_a, 0x12345678u);
    EXPECT_EQ(action.param_b, 0xABCDEF00u);
    EXPECT_FALSE(action.wait_for_response);
}

TEST(HypercallActionTest, Equality) {
    HypercallAction a{1, 100, 200, true};
    HypercallAction b{1, 100, 200, true};
    HypercallAction c{2, 100, 200, true};

    EXPECT_EQ(a, b);
    EXPECT_NE(a, c);
}

// ─────────────────────────────────────────────────────────────────────────────
// SpecialKey Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(SpecialKeyTest, ToString) {
    EXPECT_STREQ(to_string(SpecialKey::Enter), "Enter");
    EXPECT_STREQ(to_string(SpecialKey::Escape), "Escape");
    EXPECT_STREQ(to_string(SpecialKey::Tab), "Tab");
    EXPECT_STREQ(to_string(SpecialKey::Backspace), "Backspace");
    EXPECT_STREQ(to_string(SpecialKey::Up), "Up");
    EXPECT_STREQ(to_string(SpecialKey::Down), "Down");
    EXPECT_STREQ(to_string(SpecialKey::Left), "Left");
    EXPECT_STREQ(to_string(SpecialKey::Right), "Right");
    EXPECT_STREQ(to_string(SpecialKey::Home), "Home");
    EXPECT_STREQ(to_string(SpecialKey::End), "End");
    EXPECT_STREQ(to_string(SpecialKey::PageUp), "PageUp");
    EXPECT_STREQ(to_string(SpecialKey::PageDown), "PageDown");
    EXPECT_STREQ(to_string(SpecialKey::Insert), "Insert");
    EXPECT_STREQ(to_string(SpecialKey::Delete), "Delete");
}

TEST(SpecialKeyTest, FunctionKeys) {
    EXPECT_STREQ(to_string(SpecialKey::F1), "F1");
    EXPECT_STREQ(to_string(SpecialKey::F2), "F2");
    EXPECT_STREQ(to_string(SpecialKey::F3), "F3");
    EXPECT_STREQ(to_string(SpecialKey::F4), "F4");
    EXPECT_STREQ(to_string(SpecialKey::F5), "F5");
    EXPECT_STREQ(to_string(SpecialKey::F6), "F6");
    EXPECT_STREQ(to_string(SpecialKey::F7), "F7");
    EXPECT_STREQ(to_string(SpecialKey::F8), "F8");
    EXPECT_STREQ(to_string(SpecialKey::F9), "F9");
    EXPECT_STREQ(to_string(SpecialKey::F10), "F10");
    EXPECT_STREQ(to_string(SpecialKey::F11), "F11");
    EXPECT_STREQ(to_string(SpecialKey::F12), "F12");
}

TEST(SpecialKeyTest, ModifierCombinations) {
    EXPECT_STREQ(to_string(SpecialKey::CtrlC), "CtrlC");
    EXPECT_STREQ(to_string(SpecialKey::CtrlZ), "CtrlZ");
    EXPECT_STREQ(to_string(SpecialKey::CtrlBreak), "CtrlBreak");
    EXPECT_STREQ(to_string(SpecialKey::AltF4), "AltF4");
    EXPECT_STREQ(to_string(SpecialKey::AltEnter), "AltEnter");
}

// ─────────────────────────────────────────────────────────────────────────────
// SpecialKeyAction Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(SpecialKeyActionTest, DefaultConstruction) {
    SpecialKeyAction action{};

    EXPECT_EQ(action.key, SpecialKey::Enter);
}

TEST(SpecialKeyActionTest, WithKey) {
    SpecialKeyAction action{SpecialKey::F1};

    EXPECT_EQ(action.key, SpecialKey::F1);
}

TEST(SpecialKeyActionTest, Equality) {
    SpecialKeyAction a{SpecialKey::Escape};
    SpecialKeyAction b{SpecialKey::Escape};
    SpecialKeyAction c{SpecialKey::Enter};

    EXPECT_EQ(a, b);
    EXPECT_NE(a, c);
}

// ─────────────────────────────────────────────────────────────────────────────
// Action Variant Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ActionVariantTest, TypeAction) {
    Action action = TypeAction{"test"};

    EXPECT_EQ(get_action_type(action), ActionType::Type);
    EXPECT_TRUE(std::holds_alternative<TypeAction>(action));
}

TEST(ActionVariantTest, ClickAction) {
    Action action = ClickAction{10, 5};

    EXPECT_EQ(get_action_type(action), ActionType::Click);
    EXPECT_TRUE(std::holds_alternative<ClickAction>(action));
}

TEST(ActionVariantTest, WaitAction) {
    Action action = WaitAction{100};

    EXPECT_EQ(get_action_type(action), ActionType::Wait);
    EXPECT_TRUE(std::holds_alternative<WaitAction>(action));
}

TEST(ActionVariantTest, HypercallAction) {
    Action action = HypercallAction{1, 100, 200};

    EXPECT_EQ(get_action_type(action), ActionType::Hypercall);
    EXPECT_TRUE(std::holds_alternative<HypercallAction>(action));
}

TEST(ActionVariantTest, SpecialKeyAction) {
    Action action = SpecialKeyAction{SpecialKey::F1};

    EXPECT_EQ(get_action_type(action), ActionType::SpecialKey);
    EXPECT_TRUE(std::holds_alternative<SpecialKeyAction>(action));
}

// ─────────────────────────────────────────────────────────────────────────────
// ActionType Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ActionTypeTest, ToString) {
    EXPECT_STREQ(to_string(ActionType::Type), "type");
    EXPECT_STREQ(to_string(ActionType::Click), "click");
    EXPECT_STREQ(to_string(ActionType::Wait), "wait");
    EXPECT_STREQ(to_string(ActionType::Hypercall), "hypercall");
    EXPECT_STREQ(to_string(ActionType::SpecialKey), "special_key");
}

TEST(ActionTypeTest, Values) {
    EXPECT_EQ(static_cast<uint8_t>(ActionType::Type), 0);
    EXPECT_EQ(static_cast<uint8_t>(ActionType::Click), 1);
    EXPECT_EQ(static_cast<uint8_t>(ActionType::Wait), 2);
    EXPECT_EQ(static_cast<uint8_t>(ActionType::Hypercall), 3);
    EXPECT_EQ(static_cast<uint8_t>(ActionType::SpecialKey), 4);
}

// ─────────────────────────────────────────────────────────────────────────────
// ActionStatus Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ActionStatusTest, ToString) {
    EXPECT_STREQ(to_string(ActionStatus::Success), "ok");
    EXPECT_STREQ(to_string(ActionStatus::Error), "error");
    EXPECT_STREQ(to_string(ActionStatus::Timeout), "timeout");
    EXPECT_STREQ(to_string(ActionStatus::Skipped), "skipped");
}

TEST(ActionStatusTest, Values) {
    EXPECT_EQ(static_cast<uint8_t>(ActionStatus::Success), 0);
    EXPECT_EQ(static_cast<uint8_t>(ActionStatus::Error), 1);
    EXPECT_EQ(static_cast<uint8_t>(ActionStatus::Timeout), 2);
    EXPECT_EQ(static_cast<uint8_t>(ActionStatus::Skipped), 3);
}

// ─────────────────────────────────────────────────────────────────────────────
// ActionResult Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ActionResultTest, DefaultConstruction) {
    ActionResult result{};

    EXPECT_EQ(result.action_index, 0u);
    EXPECT_EQ(result.status, ActionStatus::Success);
    EXPECT_TRUE(result.error_message.empty());
    EXPECT_EQ(result.duration_us, 0u);
    EXPECT_TRUE(result.success());
}

TEST(ActionResultTest, Success) {
    ActionResult result;
    result.action_index = 5;
    result.status = ActionStatus::Success;
    result.duration_us = 1234;

    EXPECT_TRUE(result.success());
    EXPECT_EQ(result.action_index, 5u);
    EXPECT_EQ(result.duration_us, 1234u);
}

TEST(ActionResultTest, Error) {
    ActionResult result;
    result.action_index = 3;
    result.status = ActionStatus::Error;
    result.error_message = "Invalid action";

    EXPECT_FALSE(result.success());
    EXPECT_EQ(result.error_message, "Invalid action");
}

TEST(ActionResultTest, Timeout) {
    ActionResult result;
    result.status = ActionStatus::Timeout;

    EXPECT_FALSE(result.success());
}

// ─────────────────────────────────────────────────────────────────────────────
// ActionBatch Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ActionBatchTest, DefaultConstruction) {
    ActionBatch batch{};

    EXPECT_TRUE(batch.actions.empty());
    EXPECT_EQ(batch.timeout_ms, DefaultTimeoutMs);
    EXPECT_TRUE(batch.return_frame);
    EXPECT_TRUE(batch.stop_on_error);
}

TEST(ActionBatchTest, Constants) {
    EXPECT_EQ(MaxBatchSize, 100u);
    EXPECT_EQ(MaxTypeLength, 1024u);
    EXPECT_EQ(DefaultTimeoutMs, 5000u);
    EXPECT_EQ(MaxTimeoutMs, 60000u);
}

TEST(ActionBatchTest, AddActions) {
    ActionBatch batch;
    batch.actions.push_back(TypeAction{"test"});
    batch.actions.push_back(WaitAction{100});
    batch.actions.push_back(SpecialKeyAction{SpecialKey::Enter});

    EXPECT_EQ(batch.actions.size(), 3u);
}

// ─────────────────────────────────────────────────────────────────────────────
// ActionBatchResponse Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ActionBatchResponseTest, DefaultConstruction) {
    ActionBatchResponse response{};

    EXPECT_TRUE(response.success);
    EXPECT_TRUE(response.results.empty());
    EXPECT_FALSE(response.frame.has_value());
    EXPECT_EQ(response.total_duration_us, 0u);
}

TEST(ActionBatchResponseTest, SuccessCount) {
    ActionBatchResponse response;

    ActionResult r1;
    r1.status = ActionStatus::Success;
    response.results.push_back(r1);

    ActionResult r2;
    r2.status = ActionStatus::Error;
    response.results.push_back(r2);

    ActionResult r3;
    r3.status = ActionStatus::Success;
    response.results.push_back(r3);

    EXPECT_EQ(response.success_count(), 2u);
}

TEST(ActionBatchResponseTest, FirstError) {
    ActionBatchResponse response;

    ActionResult r1;
    r1.action_index = 0;
    r1.status = ActionStatus::Success;
    response.results.push_back(r1);

    ActionResult r2;
    r2.action_index = 1;
    r2.status = ActionStatus::Error;
    r2.error_message = "First error";
    response.results.push_back(r2);

    ActionResult r3;
    r3.action_index = 2;
    r3.status = ActionStatus::Error;
    r3.error_message = "Second error";
    response.results.push_back(r3);

    const ActionResult* first_err = response.first_error();
    ASSERT_NE(first_err, nullptr);
    EXPECT_EQ(first_err->action_index, 1u);
    EXPECT_EQ(first_err->error_message, "First error");
}

TEST(ActionBatchResponseTest, FirstErrorNoErrors) {
    ActionBatchResponse response;

    ActionResult r1;
    r1.status = ActionStatus::Success;
    response.results.push_back(r1);

    EXPECT_EQ(response.first_error(), nullptr);
}

TEST(ActionBatchResponseTest, WithFrame) {
    ActionBatchResponse response;
    response.frame = TokenEfficientFrame{};
    response.frame->frame_id = 42;

    EXPECT_TRUE(response.frame.has_value());
    EXPECT_EQ(response.frame->frame_id, 42u);
}
