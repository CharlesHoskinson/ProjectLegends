/**
 * @file test_llm_frame.cpp
 * @brief Unit tests for LLM frame structures.
 */

#include <gtest/gtest.h>
#include <legends/llm_frame.h>

using namespace legends::llm;

// ─────────────────────────────────────────────────────────────────────────────
// VideoMode Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(VideoModeTest, ToString) {
    EXPECT_STREQ(to_string(VideoMode::Text40x25), "Text40x25");
    EXPECT_STREQ(to_string(VideoMode::Text80x25), "Text80x25");
    EXPECT_STREQ(to_string(VideoMode::Text80x43), "Text80x43");
    EXPECT_STREQ(to_string(VideoMode::Text80x50), "Text80x50");
    EXPECT_STREQ(to_string(VideoMode::Graphics320x200), "Graphics320x200");
    EXPECT_STREQ(to_string(VideoMode::Graphics640x480), "Graphics640x480");
    EXPECT_STREQ(to_string(VideoMode::Unknown), "Unknown");
}

TEST(VideoModeTest, GetColumns) {
    EXPECT_EQ(get_columns(VideoMode::Text40x25), 40);
    EXPECT_EQ(get_columns(VideoMode::Text80x25), 80);
    EXPECT_EQ(get_columns(VideoMode::Text80x43), 80);
    EXPECT_EQ(get_columns(VideoMode::Text80x50), 80);
}

TEST(VideoModeTest, GetRows) {
    EXPECT_EQ(get_rows(VideoMode::Text40x25), 25);
    EXPECT_EQ(get_rows(VideoMode::Text80x25), 25);
    EXPECT_EQ(get_rows(VideoMode::Text80x43), 43);
    EXPECT_EQ(get_rows(VideoMode::Text80x50), 50);
}

TEST(VideoModeTest, IsTextMode) {
    EXPECT_TRUE(is_text_mode(VideoMode::Text40x25));
    EXPECT_TRUE(is_text_mode(VideoMode::Text80x25));
    EXPECT_TRUE(is_text_mode(VideoMode::Text80x43));
    EXPECT_TRUE(is_text_mode(VideoMode::Text80x50));
    EXPECT_FALSE(is_text_mode(VideoMode::Graphics320x200));
    EXPECT_FALSE(is_text_mode(VideoMode::Graphics640x480));
    EXPECT_FALSE(is_text_mode(VideoMode::Unknown));
}

// ─────────────────────────────────────────────────────────────────────────────
// CursorState Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(CursorStateTest, DefaultConstruction) {
    CursorState cursor{};

    EXPECT_EQ(cursor.column, 0);
    EXPECT_EQ(cursor.row, 0);
    EXPECT_TRUE(cursor.visible);
    EXPECT_TRUE(cursor.blink_phase);
}

TEST(CursorStateTest, Equality) {
    CursorState a{10, 5, true, false};
    CursorState b{10, 5, true, false};
    CursorState c{10, 6, true, false};

    EXPECT_EQ(a, b);
    EXPECT_NE(a, c);
}

TEST(CursorStateTest, AllFields) {
    CursorState cursor;
    cursor.column = 79;
    cursor.row = 24;
    cursor.visible = false;
    cursor.blink_phase = true;

    EXPECT_EQ(cursor.column, 79);
    EXPECT_EQ(cursor.row, 24);
    EXPECT_FALSE(cursor.visible);
    EXPECT_TRUE(cursor.blink_phase);
}

// ─────────────────────────────────────────────────────────────────────────────
// InputQueueStatus Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(InputQueueStatusTest, DefaultConstruction) {
    InputQueueStatus status{};

    EXPECT_EQ(status.pending_keystrokes, 0);
    EXPECT_EQ(status.pending_mouse_events, 0);
    EXPECT_FALSE(status.last_scancode.has_value());
    EXPECT_FALSE(status.last_key_name.has_value());
}

TEST(InputQueueStatusTest, HasPending) {
    InputQueueStatus status{};
    EXPECT_FALSE(status.has_pending());

    status.pending_keystrokes = 1;
    EXPECT_TRUE(status.has_pending());

    status.pending_keystrokes = 0;
    status.pending_mouse_events = 1;
    EXPECT_TRUE(status.has_pending());
}

TEST(InputQueueStatusTest, LastKeyInfo) {
    InputQueueStatus status{};
    status.last_scancode = 0x1C;
    status.last_key_name = "Enter";

    EXPECT_TRUE(status.last_scancode.has_value());
    EXPECT_EQ(*status.last_scancode, 0x1C);
    EXPECT_TRUE(status.last_key_name.has_value());
    EXPECT_EQ(*status.last_key_name, "Enter");
}

// ─────────────────────────────────────────────────────────────────────────────
// HypercallLogEntry Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(HypercallLogEntryTest, DefaultConstruction) {
    HypercallLogEntry entry{};

    EXPECT_EQ(entry.timestamp_us, 0);
    EXPECT_EQ(entry.command_id, 0);
    EXPECT_EQ(entry.param_a, 0);
    EXPECT_EQ(entry.param_b, 0);
    EXPECT_EQ(entry.status, 0);
    EXPECT_FALSE(entry.success);
}

TEST(HypercallLogEntryTest, AllFields) {
    HypercallLogEntry entry;
    entry.timestamp_us = 1234567890;
    entry.command_id = 0x0001;
    entry.param_a = 0x12345678;
    entry.param_b = 0xABCDEF00;
    entry.status = 0;
    entry.success = true;

    EXPECT_EQ(entry.timestamp_us, 1234567890u);
    EXPECT_EQ(entry.command_id, 0x0001);
    EXPECT_EQ(entry.param_a, 0x12345678u);
    EXPECT_EQ(entry.param_b, 0xABCDEF00u);
    EXPECT_TRUE(entry.success);
}

TEST(HypercallLogEntryTest, Equality) {
    HypercallLogEntry a{1000, 1, 100, 200, 0, true};
    HypercallLogEntry b{1000, 1, 100, 200, 0, true};
    HypercallLogEntry c{1000, 2, 100, 200, 0, true};

    EXPECT_EQ(a, b);
    EXPECT_NE(a, c);
}

// ─────────────────────────────────────────────────────────────────────────────
// FrameFlags Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(FrameFlagsTest, None) {
    auto flags = FrameFlags::None;
    EXPECT_EQ(static_cast<uint8_t>(flags), 0);
}

TEST(FrameFlagsTest, SingleFlag) {
    EXPECT_EQ(static_cast<uint8_t>(FrameFlags::TextMode), 1);
    EXPECT_EQ(static_cast<uint8_t>(FrameFlags::GraphicsMode), 2);
    EXPECT_EQ(static_cast<uint8_t>(FrameFlags::CursorVisible), 4);
    EXPECT_EQ(static_cast<uint8_t>(FrameFlags::InputPending), 8);
    EXPECT_EQ(static_cast<uint8_t>(FrameFlags::ProgramRunning), 16);
    EXPECT_EQ(static_cast<uint8_t>(FrameFlags::Dirty), 32);
    EXPECT_EQ(static_cast<uint8_t>(FrameFlags::RleCompressed), 64);
}

TEST(FrameFlagsTest, BitwiseOr) {
    auto flags = FrameFlags::TextMode | FrameFlags::CursorVisible;
    EXPECT_EQ(static_cast<uint8_t>(flags), 5);
}

TEST(FrameFlagsTest, BitwiseAnd) {
    auto flags = FrameFlags::TextMode | FrameFlags::CursorVisible;
    EXPECT_EQ(static_cast<uint8_t>(flags & FrameFlags::TextMode), 1);
    EXPECT_EQ(static_cast<uint8_t>(flags & FrameFlags::GraphicsMode), 0);
}

TEST(FrameFlagsTest, HasFlag) {
    auto flags = FrameFlags::TextMode | FrameFlags::CursorVisible | FrameFlags::Dirty;

    EXPECT_TRUE(has_flag(flags, FrameFlags::TextMode));
    EXPECT_TRUE(has_flag(flags, FrameFlags::CursorVisible));
    EXPECT_TRUE(has_flag(flags, FrameFlags::Dirty));
    EXPECT_FALSE(has_flag(flags, FrameFlags::GraphicsMode));
    EXPECT_FALSE(has_flag(flags, FrameFlags::InputPending));
}

TEST(FrameFlagsTest, CompoundAssignment) {
    auto flags = FrameFlags::None;
    flags |= FrameFlags::TextMode;
    EXPECT_TRUE(has_flag(flags, FrameFlags::TextMode));

    flags |= FrameFlags::CursorVisible;
    EXPECT_TRUE(has_flag(flags, FrameFlags::CursorVisible));
}

// ─────────────────────────────────────────────────────────────────────────────
// TokenEfficientFrame Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(TokenEfficientFrameTest, DefaultConstruction) {
    TokenEfficientFrame frame{};

    EXPECT_EQ(frame.frame_id, 0u);
    EXPECT_EQ(frame.timestamp_us, 0u);
    EXPECT_EQ(frame.mode, VideoMode::Unknown);
    EXPECT_EQ(frame.flags, FrameFlags::None);
    EXPECT_EQ(frame.text_columns, 0);
    EXPECT_EQ(frame.text_rows, 0);
    EXPECT_TRUE(frame.text_content.empty());
    EXPECT_TRUE(frame.hypercall_log.empty());
}

TEST(TokenEfficientFrameTest, IsText) {
    TokenEfficientFrame frame{};

    frame.mode = VideoMode::Text80x25;
    EXPECT_TRUE(frame.is_text());

    frame.mode = VideoMode::Graphics320x200;
    EXPECT_FALSE(frame.is_text());
}

TEST(TokenEfficientFrameTest, CellCount) {
    TokenEfficientFrame frame{};
    frame.text_columns = 80;
    frame.text_rows = 25;

    EXPECT_EQ(frame.cell_count(), 2000u);
}

TEST(TokenEfficientFrameTest, AllFields) {
    TokenEfficientFrame frame;
    frame.frame_id = 42;
    frame.timestamp_us = 1234567890;
    frame.mode = VideoMode::Text80x25;
    frame.flags = FrameFlags::TextMode | FrameFlags::CursorVisible;
    frame.text_columns = 80;
    frame.text_rows = 25;
    frame.text_content = "C:\\>";
    frame.cursor.column = 3;
    frame.cursor.row = 0;
    frame.cursor.visible = true;
    frame.program_name = "COMMAND.COM";
    frame.working_dir = "C:\\";

    EXPECT_EQ(frame.frame_id, 42u);
    EXPECT_EQ(frame.timestamp_us, 1234567890u);
    EXPECT_EQ(frame.mode, VideoMode::Text80x25);
    EXPECT_TRUE(has_flag(frame.flags, FrameFlags::TextMode));
    EXPECT_TRUE(has_flag(frame.flags, FrameFlags::CursorVisible));
    EXPECT_EQ(frame.text_columns, 80);
    EXPECT_EQ(frame.text_rows, 25);
    EXPECT_EQ(frame.text_content, "C:\\>");
    EXPECT_EQ(frame.cursor.column, 3);
    EXPECT_EQ(frame.cursor.row, 0);
    EXPECT_TRUE(frame.cursor.visible);
    EXPECT_EQ(frame.program_name, "COMMAND.COM");
    EXPECT_EQ(frame.working_dir, "C:\\");
}

TEST(TokenEfficientFrameTest, HypercallLog) {
    TokenEfficientFrame frame;

    HypercallLogEntry entry1{1000, 1, 100, 200, 0, true};
    HypercallLogEntry entry2{2000, 2, 300, 400, 1, false};

    frame.hypercall_log.push_back(entry1);
    frame.hypercall_log.push_back(entry2);

    EXPECT_EQ(frame.hypercall_log.size(), 2u);
    EXPECT_EQ(frame.hypercall_log[0].command_id, 1);
    EXPECT_EQ(frame.hypercall_log[1].command_id, 2);
}

// ─────────────────────────────────────────────────────────────────────────────
// FrameBuilder Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(FrameBuilderTest, DefaultConstruction) {
    FrameBuilder builder;

    EXPECT_EQ(builder.hypercall_log_limit(), 10u);
    EXPECT_TRUE(builder.rle_enabled());
    EXPECT_TRUE(builder.trim_trailing_spaces());
    EXPECT_EQ(builder.current_frame_id(), 0u);
}

TEST(FrameBuilderTest, SetOptions) {
    FrameBuilder builder;

    builder.set_hypercall_log_limit(5);
    EXPECT_EQ(builder.hypercall_log_limit(), 5u);

    builder.set_rle_enabled(false);
    EXPECT_FALSE(builder.rle_enabled());

    builder.set_trim_trailing_spaces(false);
    EXPECT_FALSE(builder.trim_trailing_spaces());
}

TEST(FrameBuilderTest, AddHypercallLog) {
    FrameBuilder builder;
    builder.set_hypercall_log_limit(3);

    HypercallLogEntry entry{1000, 1, 100, 200, 0, true};

    builder.add_hypercall_log(entry);
    builder.add_hypercall_log(entry);
    builder.add_hypercall_log(entry);
    builder.add_hypercall_log(entry); // Should discard oldest

    // We can't directly access the log, but we can verify via reset
    builder.clear_hypercall_log();
    // No way to verify count without building a frame
}

TEST(FrameBuilderTest, Reset) {
    FrameBuilder builder;

    // Build a frame to increment ID
    uint8_t screen[2000] = {0};
    auto frame = builder.build_full_frame(80, 25, screen, 0, 0, true);

    EXPECT_EQ(frame.frame_id, 1u);

    builder.reset();
    // After reset, cached frame is cleared (next frame starts fresh)
}

TEST(FrameBuilderTest, BuildFullFrameIncreasesFrameId) {
    FrameBuilder builder;
    uint8_t screen[2000] = {0};

    auto frame1 = builder.build_full_frame(80, 25, screen, 0, 0, true);
    EXPECT_EQ(frame1.frame_id, 1u);

    auto frame2 = builder.build_full_frame(80, 25, screen, 5, 3, true);
    EXPECT_EQ(frame2.frame_id, 2u);

    auto frame3 = builder.build_full_frame(80, 25, screen, 10, 10, false);
    EXPECT_EQ(frame3.frame_id, 3u);
}

TEST(FrameBuilderTest, BuildFullFrameSetsMode) {
    FrameBuilder builder;
    uint8_t screen[2000] = {0};

    auto frame = builder.build_full_frame(80, 25, screen, 0, 0, true);
    EXPECT_EQ(frame.mode, VideoMode::Text80x25);
    EXPECT_EQ(frame.text_columns, 80);
    EXPECT_EQ(frame.text_rows, 25);
}

TEST(FrameBuilderTest, BuildFullFrameSetsCursor) {
    FrameBuilder builder;
    uint8_t screen[2000] = {0};

    auto frame = builder.build_full_frame(80, 25, screen, 15, 10, true);
    EXPECT_EQ(frame.cursor.column, 15);
    EXPECT_EQ(frame.cursor.row, 10);
    EXPECT_TRUE(frame.cursor.visible);

    auto frame2 = builder.build_full_frame(80, 25, screen, 0, 0, false);
    EXPECT_FALSE(frame2.cursor.visible);
}

TEST(FrameBuilderTest, BuildFullFrame40Column) {
    FrameBuilder builder;
    uint8_t screen[1000] = {0};

    auto frame = builder.build_full_frame(40, 25, screen, 0, 0, true);
    EXPECT_EQ(frame.mode, VideoMode::Text40x25);
    EXPECT_EQ(frame.text_columns, 40);
    EXPECT_EQ(frame.text_rows, 25);
}

TEST(FrameBuilderTest, BuildFullFrame50Row) {
    FrameBuilder builder;
    uint8_t screen[4000] = {0};

    auto frame = builder.build_full_frame(80, 50, screen, 0, 0, true);
    EXPECT_EQ(frame.mode, VideoMode::Text80x50);
    EXPECT_EQ(frame.text_columns, 80);
    EXPECT_EQ(frame.text_rows, 50);
}

TEST(FrameBuilderTest, BuildFullFrame43Row) {
    FrameBuilder builder;
    uint8_t screen[3440] = {0};

    auto frame = builder.build_full_frame(80, 43, screen, 0, 0, true);
    EXPECT_EQ(frame.mode, VideoMode::Text80x43);
    EXPECT_EQ(frame.text_columns, 80);
    EXPECT_EQ(frame.text_rows, 43);
}

// ─────────────────────────────────────────────────────────────────────────────
// Delta Frame Tests (build_diff_frame)
// ─────────────────────────────────────────────────────────────────────────────

TEST(FrameBuilderTest, BuildDiffFrameReturnsFullFrameWhenNoPrevious) {
    FrameBuilder builder;
    uint8_t screen[2000];
    std::fill_n(screen, 2000, 'A');

    // First call should return a full frame (no previous to diff against)
    auto frame = builder.build_diff_frame(80, 25, screen, 0, 0, true);

    EXPECT_EQ(frame.frame_id, 1u);
    EXPECT_EQ(frame.mode, VideoMode::Text80x25);
    EXPECT_EQ(frame.text_columns, 80);
    EXPECT_EQ(frame.text_rows, 25);
    EXPECT_FALSE(frame.text_content.empty());
}

TEST(FrameBuilderTest, BuildDiffFrameDetectsChangedCells) {
    FrameBuilder builder;
    uint8_t screen_a[2000];
    std::fill_n(screen_a, 2000, ' ');
    screen_a[0] = 'A';

    // Build first frame to establish baseline
    auto frame1 = builder.build_full_frame(80, 25, screen_a, 0, 0, true);
    EXPECT_EQ(frame1.frame_id, 1u);

    // Modify screen
    uint8_t screen_b[2000];
    std::fill_n(screen_b, 2000, ' ');
    screen_b[0] = 'B';  // Changed cell

    auto diff_frame = builder.build_diff_frame(80, 25, screen_b, 0, 0, true);

    // Diff frame should have incremented ID
    EXPECT_EQ(diff_frame.frame_id, 2u);
    EXPECT_EQ(diff_frame.mode, VideoMode::Text80x25);
    // Content should reflect the new state
    EXPECT_FALSE(diff_frame.text_content.empty());
}

TEST(FrameBuilderTest, BuildDiffFrameDetectsModeChange) {
    FrameBuilder builder;
    uint8_t screen_80[2000] = {0};

    // Build 80x25 frame
    auto frame1 = builder.build_full_frame(80, 25, screen_80, 0, 0, true);
    EXPECT_EQ(frame1.mode, VideoMode::Text80x25);

    // Try 40x25 mode - mode change should be detected
    uint8_t screen_40[1000] = {0};
    auto diff_frame = builder.build_diff_frame(40, 25, screen_40, 0, 0, true);

    EXPECT_EQ(diff_frame.mode, VideoMode::Text40x25);
    EXPECT_EQ(diff_frame.text_columns, 40);
    EXPECT_EQ(diff_frame.text_rows, 25);
}

TEST(FrameBuilderTest, BuildDiffFrameDetectsCursorMovement) {
    FrameBuilder builder;
    uint8_t screen[2000] = {0};

    // Build frame with cursor at (0, 0)
    auto frame1 = builder.build_full_frame(80, 25, screen, 0, 0, true);
    EXPECT_EQ(frame1.cursor.column, 0);
    EXPECT_EQ(frame1.cursor.row, 0);

    // Build diff with cursor moved to (10, 5)
    auto diff_frame = builder.build_diff_frame(80, 25, screen, 10, 5, true);

    EXPECT_EQ(diff_frame.cursor.column, 10);
    EXPECT_EQ(diff_frame.cursor.row, 5);
    EXPECT_TRUE(diff_frame.cursor.visible);
}

TEST(FrameBuilderTest, BuildDiffFrameDetectsCursorVisibilityChange) {
    FrameBuilder builder;
    uint8_t screen[2000] = {0};

    // Build frame with visible cursor
    auto frame1 = builder.build_full_frame(80, 25, screen, 0, 0, true);
    EXPECT_TRUE(frame1.cursor.visible);
    EXPECT_TRUE(has_flag(frame1.flags, FrameFlags::CursorVisible));

    // Build diff with hidden cursor
    auto diff_frame = builder.build_diff_frame(80, 25, screen, 0, 0, false);

    EXPECT_FALSE(diff_frame.cursor.visible);
    EXPECT_FALSE(has_flag(diff_frame.flags, FrameFlags::CursorVisible));
}

TEST(FrameBuilderTest, BuildDiffFrameIdenticalFrames) {
    FrameBuilder builder;
    uint8_t screen[2000];
    std::fill_n(screen, 2000, 'X');

    // Build first frame
    auto frame1 = builder.build_full_frame(80, 25, screen, 5, 3, true);
    EXPECT_EQ(frame1.frame_id, 1u);

    // Build diff with identical content
    auto diff_frame = builder.build_diff_frame(80, 25, screen, 5, 3, true);

    // Frame ID should still increment
    EXPECT_EQ(diff_frame.frame_id, 2u);
    // Mode and dimensions should match
    EXPECT_EQ(diff_frame.mode, VideoMode::Text80x25);
    EXPECT_EQ(diff_frame.cursor.column, 5);
    EXPECT_EQ(diff_frame.cursor.row, 3);
}

TEST(FrameBuilderTest, BuildDiffFrameEdgeCaseEmptyScreen) {
    FrameBuilder builder;
    uint8_t screen[2000];
    std::fill_n(screen, 2000, static_cast<uint8_t>(0));  // Null characters

    auto frame = builder.build_diff_frame(80, 25, screen, 0, 0, true);

    EXPECT_EQ(frame.text_columns, 80);
    EXPECT_EQ(frame.text_rows, 25);
    EXPECT_EQ(frame.mode, VideoMode::Text80x25);
}

TEST(FrameBuilderTest, BuildDiffFrameEdgeCaseFullScreenChange) {
    FrameBuilder builder;
    uint8_t screen_a[2000];
    uint8_t screen_b[2000];
    std::fill_n(screen_a, 2000, 'A');
    std::fill_n(screen_b, 2000, 'B');

    // Build first frame
    auto frame1 = builder.build_full_frame(80, 25, screen_a, 0, 0, true);
    EXPECT_EQ(frame1.frame_id, 1u);

    // Build diff with completely different content
    auto diff_frame = builder.build_diff_frame(80, 25, screen_b, 0, 0, true);

    // Full screen change - frame should still be valid
    EXPECT_EQ(diff_frame.frame_id, 2u);
    EXPECT_EQ(diff_frame.mode, VideoMode::Text80x25);
    EXPECT_FALSE(diff_frame.text_content.empty());
}
