/**
 * @file test_events.cpp
 * @brief Unit tests for event type definitions.
 */

#include <gtest/gtest.h>
#include <legends/events.h>
#include <algorithm>
#include <cstring>
#include <vector>

using namespace legends::events;

// ─────────────────────────────────────────────────────────────────────────────
// TextCell Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(TextCellTest, DefaultConstruction) {
    TextCell cell{};

    EXPECT_EQ(cell.character, 0);
    EXPECT_EQ(cell.foreground, 0);
    EXPECT_EQ(cell.background, 0);
    EXPECT_FALSE(cell.blink);
}

TEST(TextCellTest, Equality) {
    TextCell a{u'A', 7, 0, false};
    TextCell b{u'A', 7, 0, false};
    TextCell c{u'B', 7, 0, false};

    EXPECT_EQ(a, b);
    EXPECT_NE(a, c);
}

TEST(TextCellTest, SizeIs6Bytes) {
    EXPECT_EQ(sizeof(TextCell), 6u);
}

TEST(TextCellTest, ForegroundRange) {
    TextCell cell{};
    cell.foreground = 15;  // Maximum color
    EXPECT_EQ(cell.foreground, 15);
}

TEST(TextCellTest, BackgroundRange) {
    TextCell cell{};
    cell.background = 7;  // Standard max without blink
    EXPECT_EQ(cell.background, 7);
}

// ─────────────────────────────────────────────────────────────────────────────
// TextModeScreen Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(TextModeScreenTest, DefaultConstruction) {
    TextModeScreen screen{};

    EXPECT_EQ(screen.columns, 0);
    EXPECT_EQ(screen.rows, 0);
    EXPECT_EQ(screen.cursor_x, 0);
    EXPECT_EQ(screen.cursor_y, 0);
    EXPECT_FALSE(screen.cursor_visible);
}

TEST(TextModeScreenTest, StandardMode) {
    TextModeScreen screen{};
    screen.columns = 80;
    screen.rows = 25;
    screen.cursor_visible = true;

    EXPECT_EQ(screen.cell_count(), 2000u);
}

TEST(TextModeScreenTest, AtFunction) {
    TextModeScreen screen{};
    screen.columns = 80;
    screen.rows = 25;

    // Set a cell
    screen.at(10, 5) = TextCell{u'X', 14, 1, false};

    // Retrieve it
    const auto& cell = screen.at(10, 5);
    EXPECT_EQ(cell.character, u'X');
    EXPECT_EQ(cell.foreground, 14);
    EXPECT_EQ(cell.background, 1);
}

TEST(TextModeScreenTest, MaxCells) {
    EXPECT_EQ(TextModeScreen::MaxCells, 80u * 50u);
}

// ─────────────────────────────────────────────────────────────────────────────
// TextModeDiff Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(TextModeDiffTest, DefaultConstruction) {
    TextModeDiff diff{};

    EXPECT_EQ(diff.frame_number, 0u);
    EXPECT_EQ(diff.changed_count, 0u);
    EXPECT_FALSE(diff.cursor_changed);
}

TEST(TextModeDiffTest, AddChange) {
    TextModeDiff diff{};

    TextCell cell{u'A', 7, 0, false};
    EXPECT_TRUE(diff.add_change(100, cell));
    EXPECT_EQ(diff.changed_count, 1u);

    EXPECT_EQ(diff.changes[0].index, 100);
    EXPECT_EQ(diff.changes[0].cell, cell);
}

TEST(TextModeDiffTest, IsFull) {
    TextModeDiff diff{};

    EXPECT_FALSE(diff.is_full());

    // Fill to max
    TextCell cell{u'X', 7, 0, false};
    for (size_t i = 0; i < TextModeDiff::MaxChanges; ++i) {
        EXPECT_TRUE(diff.add_change(static_cast<uint16_t>(i), cell));
    }

    EXPECT_TRUE(diff.is_full());

    // Next add should fail
    EXPECT_FALSE(diff.add_change(999, cell));
}

TEST(TextModeDiffTest, Clear) {
    TextModeDiff diff{};

    TextCell cell{u'X', 7, 0, false};
    diff.add_change(0, cell);
    diff.cursor_changed = true;

    diff.clear();

    EXPECT_EQ(diff.changed_count, 0u);
    EXPECT_FALSE(diff.cursor_changed);
}

// ─────────────────────────────────────────────────────────────────────────────
// TextModeEventType Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(TextModeEventTypeTest, AllValues) {
    EXPECT_EQ(static_cast<int>(TextModeEventType::FullScreen), 0);
    EXPECT_EQ(static_cast<int>(TextModeEventType::Differential), 1);
    EXPECT_EQ(static_cast<int>(TextModeEventType::CursorMove), 2);
    EXPECT_EQ(static_cast<int>(TextModeEventType::ModeChange), 3);
}

// ─────────────────────────────────────────────────────────────────────────────
// ProgramState Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ProgramStateTest, ToString) {
    EXPECT_STREQ(to_string(ProgramState::Loading), "Loading");
    EXPECT_STREQ(to_string(ProgramState::Started), "Started");
    EXPECT_STREQ(to_string(ProgramState::Running), "Running");
    EXPECT_STREQ(to_string(ProgramState::Suspended), "Suspended");
    EXPECT_STREQ(to_string(ProgramState::Terminating), "Terminating");
    EXPECT_STREQ(to_string(ProgramState::Halted), "Halted");
}

// ─────────────────────────────────────────────────────────────────────────────
// TerminationReason Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(TerminationReasonTest, ToString) {
    EXPECT_STREQ(to_string(TerminationReason::NormalExit), "NormalExit");
    EXPECT_STREQ(to_string(TerminationReason::CtrlBreak), "CtrlBreak");
    EXPECT_STREQ(to_string(TerminationReason::CriticalError), "CriticalError");
    EXPECT_STREQ(to_string(TerminationReason::Exception), "Exception");
    EXPECT_STREQ(to_string(TerminationReason::ParentKill), "ParentKill");
    EXPECT_STREQ(to_string(TerminationReason::Unknown), "Unknown");
}

// ─────────────────────────────────────────────────────────────────────────────
// ProgramStartedEvent Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ProgramStartedEventTest, SetPath) {
    ProgramStartedEvent event{};

    event.set_path("C:\\GAME\\RUN.EXE");

    EXPECT_STREQ(event.path.data(), "C:\\GAME\\RUN.EXE");
}

TEST(ProgramStartedEventTest, SetPathNull) {
    ProgramStartedEvent event{};
    event.set_path("something");
    event.set_path(nullptr);

    EXPECT_EQ(event.path[0], '\0');
}

TEST(ProgramStartedEventTest, SetArguments) {
    ProgramStartedEvent event{};

    event.set_arguments("-mode fast -debug");

    EXPECT_STREQ(event.arguments.data(), "-mode fast -debug");
}

TEST(ProgramStartedEventTest, PathTruncation) {
    ProgramStartedEvent event{};

    // Create a path longer than MaxPathLength
    std::string long_path(200, 'X');
    event.set_path(long_path.c_str());

    // Should be truncated
    EXPECT_LT(std::strlen(event.path.data()), 200u);
    EXPECT_EQ(std::strlen(event.path.data()), ProgramStartedEvent::MaxPathLength - 1);
}

// ─────────────────────────────────────────────────────────────────────────────
// ProgramHaltedEvent Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ProgramHaltedEventTest, DefaultConstruction) {
    ProgramHaltedEvent event{};

    EXPECT_EQ(event.exit_code, 0);
    EXPECT_EQ(event.instructions_executed, 0u);
}

TEST(ProgramHaltedEventTest, SetPath) {
    ProgramHaltedEvent event{};

    event.set_path("C:\\GAME\\RUN.EXE");

    EXPECT_STREQ(event.path.data(), "C:\\GAME\\RUN.EXE");
}

TEST(ProgramHaltedEventTest, AllFields) {
    ProgramHaltedEvent event{};

    event.timestamp_us = 1000000;
    event.final_state = ProgramState::Halted;
    event.reason = TerminationReason::NormalExit;
    event.exit_code = 42;
    event.instructions_executed = 1000000;
    event.runtime_ms = 5000;
    event.set_path("TEST.EXE");

    EXPECT_EQ(event.timestamp_us, 1000000u);
    EXPECT_EQ(event.final_state, ProgramState::Halted);
    EXPECT_EQ(event.reason, TerminationReason::NormalExit);
    EXPECT_EQ(event.exit_code, 42);
    EXPECT_EQ(event.instructions_executed, 1000000u);
    EXPECT_EQ(event.runtime_ms, 5000u);
}

// ─────────────────────────────────────────────────────────────────────────────
// ScanCode Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ScanCodeTest, CommonKeys) {
    EXPECT_EQ(static_cast<uint8_t>(ScanCode::Escape), 0x01);
    EXPECT_EQ(static_cast<uint8_t>(ScanCode::A), 0x1E);
    EXPECT_EQ(static_cast<uint8_t>(ScanCode::Space), 0x39);
    EXPECT_EQ(static_cast<uint8_t>(ScanCode::Enter), 0x1C);
    EXPECT_EQ(static_cast<uint8_t>(ScanCode::F1), 0x3B);
}

// ─────────────────────────────────────────────────────────────────────────────
// KeyModifiers Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(KeyModifiersTest, Combine) {
    auto mods = KeyModifiers::Shift | KeyModifiers::Ctrl;

    EXPECT_TRUE(has_modifier(mods, KeyModifiers::Shift));
    EXPECT_TRUE(has_modifier(mods, KeyModifiers::Ctrl));
    EXPECT_FALSE(has_modifier(mods, KeyModifiers::Alt));
}

TEST(KeyModifiersTest, None) {
    EXPECT_FALSE(has_modifier(KeyModifiers::None, KeyModifiers::Shift));
    EXPECT_FALSE(has_modifier(KeyModifiers::None, KeyModifiers::Ctrl));
    EXPECT_FALSE(has_modifier(KeyModifiers::None, KeyModifiers::Alt));
}

TEST(KeyModifiersTest, All) {
    auto all = KeyModifiers::Shift | KeyModifiers::Ctrl | KeyModifiers::Alt;

    EXPECT_TRUE(has_modifier(all, KeyModifiers::Shift));
    EXPECT_TRUE(has_modifier(all, KeyModifiers::Ctrl));
    EXPECT_TRUE(has_modifier(all, KeyModifiers::Alt));
}

// ─────────────────────────────────────────────────────────────────────────────
// KeyboardEvent Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(KeyboardEventTest, KeyDown) {
    KeyboardEvent event{};
    event.scan_code = ScanCode::A;
    event.is_pressed = true;
    event.is_extended = false;
    event.modifiers = KeyModifiers::None;

    EXPECT_EQ(event.scan_code, ScanCode::A);
    EXPECT_TRUE(event.is_pressed);
    EXPECT_FALSE(event.is_extended);
}

TEST(KeyboardEventTest, WithModifiers) {
    KeyboardEvent event{};
    event.scan_code = ScanCode::C;
    event.is_pressed = true;
    event.modifiers = KeyModifiers::Ctrl;

    EXPECT_TRUE(has_modifier(event.modifiers, KeyModifiers::Ctrl));
}

// ─────────────────────────────────────────────────────────────────────────────
// MouseButtons Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(MouseButtonsTest, Combine) {
    auto buttons = MouseButtons::Left | MouseButtons::Right;

    EXPECT_TRUE(has_button(buttons, MouseButtons::Left));
    EXPECT_TRUE(has_button(buttons, MouseButtons::Right));
    EXPECT_FALSE(has_button(buttons, MouseButtons::Middle));
}

TEST(MouseButtonsTest, None) {
    EXPECT_FALSE(has_button(MouseButtons::None, MouseButtons::Left));
    EXPECT_FALSE(has_button(MouseButtons::None, MouseButtons::Right));
    EXPECT_FALSE(has_button(MouseButtons::None, MouseButtons::Middle));
}

// ─────────────────────────────────────────────────────────────────────────────
// MouseEvent Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(MouseEventTest, Movement) {
    MouseEvent event{};
    event.delta_x = 10;
    event.delta_y = -5;
    event.wheel_delta = 0;
    event.buttons = MouseButtons::None;

    EXPECT_EQ(event.delta_x, 10);
    EXPECT_EQ(event.delta_y, -5);
}

TEST(MouseEventTest, ButtonClick) {
    MouseEvent event{};
    event.delta_x = 0;
    event.delta_y = 0;
    event.buttons = MouseButtons::Left;
    event.changed = MouseButtons::Left;

    EXPECT_TRUE(has_button(event.buttons, MouseButtons::Left));
    EXPECT_TRUE(has_button(event.changed, MouseButtons::Left));
}

TEST(MouseEventTest, WheelScroll) {
    MouseEvent event{};
    event.wheel_delta = 3;  // Scroll up

    EXPECT_EQ(event.wheel_delta, 3);
}

// ─────────────────────────────────────────────────────────────────────────────
// EventType Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(EventTypeTest, ToString) {
    EXPECT_STREQ(to_string(EventType::TextScreen), "TextScreen");
    EXPECT_STREQ(to_string(EventType::TextDiff), "TextDiff");
    EXPECT_STREQ(to_string(EventType::ProgramStarted), "ProgramStarted");
    EXPECT_STREQ(to_string(EventType::ProgramHalted), "ProgramHalted");
    EXPECT_STREQ(to_string(EventType::Keyboard), "Keyboard");
    EXPECT_STREQ(to_string(EventType::Mouse), "Mouse");
}

TEST(EventTypeTest, AllUniqueValues) {
    // Ensure all event types have unique values
    std::vector<int> values = {
        static_cast<int>(EventType::TextScreen),
        static_cast<int>(EventType::TextDiff),
        static_cast<int>(EventType::ProgramStarted),
        static_cast<int>(EventType::ProgramHalted),
        static_cast<int>(EventType::Keyboard),
        static_cast<int>(EventType::Mouse)
    };

    std::sort(values.begin(), values.end());
    auto it = std::unique(values.begin(), values.end());

    EXPECT_EQ(it, values.end()) << "Event types should have unique values";
}
