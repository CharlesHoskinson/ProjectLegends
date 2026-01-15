/**
 * @file test_llm_diff.cpp
 * @brief Unit tests for LLM screenshot diff utility.
 */

#include <gtest/gtest.h>
#include <legends/llm_diff.h>

using namespace legends::llm;

// ─────────────────────────────────────────────────────────────────────────────
// DiffRegion Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(DiffRegionTest, DefaultConstruction) {
    DiffRegion region{};

    EXPECT_EQ(region.x, 0);
    EXPECT_EQ(region.y, 0);
    EXPECT_EQ(region.width, 0);
    EXPECT_EQ(region.height, 0);
    EXPECT_FLOAT_EQ(region.change_ratio, 0.0f);
}

TEST(DiffRegionTest, CellCount) {
    DiffRegion region{0, 0, 10, 5, 0.5f};

    EXPECT_EQ(region.cell_count(), 50u);
}

TEST(DiffRegionTest, CellCountZero) {
    DiffRegion region{};

    EXPECT_EQ(region.cell_count(), 0u);
}

TEST(DiffRegionTest, Equality) {
    DiffRegion a{10, 5, 20, 10, 0.5f};
    DiffRegion b{10, 5, 20, 10, 0.5f};
    DiffRegion c{10, 6, 20, 10, 0.5f};

    EXPECT_EQ(a, b);
    EXPECT_NE(a, c);
}

// ─────────────────────────────────────────────────────────────────────────────
// ScreenshotDiffResult Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ScreenshotDiffResultTest, DefaultConstruction) {
    ScreenshotDiffResult result{};

    EXPECT_TRUE(result.identical);
    EXPECT_FLOAT_EQ(result.total_change_percentage, 0.0f);
    EXPECT_EQ(result.changed_cells, 0u);
    EXPECT_EQ(result.total_cells, 0u);
    EXPECT_TRUE(result.regions.empty());
    EXPECT_TRUE(result.text_diff.empty());
}

TEST(ScreenshotDiffResultTest, WithinThreshold) {
    ScreenshotDiffResult result;
    result.total_change_percentage = 5.0f;

    EXPECT_TRUE(result.within_threshold(5.0f));
    EXPECT_TRUE(result.within_threshold(10.0f));
    EXPECT_FALSE(result.within_threshold(4.0f));
}

TEST(ScreenshotDiffResultTest, LargestRegion) {
    ScreenshotDiffResult result;
    result.regions.push_back({0, 0, 5, 5, 0.5f});   // 25 cells
    result.regions.push_back({10, 0, 10, 10, 0.5f}); // 100 cells
    result.regions.push_back({0, 10, 3, 3, 0.5f});  // 9 cells

    const DiffRegion* largest = result.largest_region();
    ASSERT_NE(largest, nullptr);
    EXPECT_EQ(largest->width, 10);
    EXPECT_EQ(largest->height, 10);
}

TEST(ScreenshotDiffResultTest, LargestRegionEmpty) {
    ScreenshotDiffResult result;

    EXPECT_EQ(result.largest_region(), nullptr);
}

TEST(ScreenshotDiffResultTest, Summary) {
    ScreenshotDiffResult result;
    result.identical = false;
    result.total_change_percentage = 15.5f;
    result.changed_cells = 310;
    result.total_cells = 2000;

    std::string summary = result.summary();

    // Summary should contain key information
    EXPECT_NE(summary.find("15.5"), std::string::npos);
    EXPECT_NE(summary.find("310"), std::string::npos);
}

// ─────────────────────────────────────────────────────────────────────────────
// DiffOptions Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(DiffOptionsTest, DefaultValues) {
    DiffOptions opts{};

    EXPECT_FLOAT_EQ(opts.threshold, 0.0f);
    EXPECT_EQ(opts.min_region_size, 1);
    EXPECT_TRUE(opts.merge_adjacent);
    EXPECT_FALSE(opts.ignore_cursor);
    EXPECT_TRUE(opts.ignore_trailing_spaces);
    EXPECT_EQ(opts.context_lines, 3);
}

TEST(DiffOptionsTest, CustomValues) {
    DiffOptions opts;
    opts.threshold = 5.0f;
    opts.min_region_size = 10;
    opts.merge_adjacent = false;
    opts.ignore_cursor = true;
    opts.ignore_trailing_spaces = false;
    opts.context_lines = 5;

    EXPECT_FLOAT_EQ(opts.threshold, 5.0f);
    EXPECT_EQ(opts.min_region_size, 10);
    EXPECT_FALSE(opts.merge_adjacent);
    EXPECT_TRUE(opts.ignore_cursor);
    EXPECT_FALSE(opts.ignore_trailing_spaces);
    EXPECT_EQ(opts.context_lines, 5);
}

// ─────────────────────────────────────────────────────────────────────────────
// ScreenshotDiff Construction Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ScreenshotDiffTest, DefaultConstruction) {
    ScreenshotDiff diff;

    const auto& opts = diff.options();
    EXPECT_FLOAT_EQ(opts.threshold, 0.0f);
}

TEST(ScreenshotDiffTest, ConstructionWithOptions) {
    DiffOptions opts;
    opts.threshold = 5.0f;
    opts.min_region_size = 10;

    ScreenshotDiff diff(opts);

    EXPECT_FLOAT_EQ(diff.options().threshold, 5.0f);
    EXPECT_EQ(diff.options().min_region_size, 10);
}

TEST(ScreenshotDiffTest, SetOptions) {
    ScreenshotDiff diff;

    DiffOptions opts;
    opts.threshold = 10.0f;
    diff.set_options(opts);

    EXPECT_FLOAT_EQ(diff.options().threshold, 10.0f);
}

TEST(ScreenshotDiffTest, SetThreshold) {
    ScreenshotDiff diff;
    diff.set_threshold(7.5f);

    EXPECT_FLOAT_EQ(diff.options().threshold, 7.5f);
}

TEST(ScreenshotDiffTest, SetMinRegionSize) {
    ScreenshotDiff diff;
    diff.set_min_region_size(5);

    EXPECT_EQ(diff.options().min_region_size, 5);
}

// ─────────────────────────────────────────────────────────────────────────────
// ScreenshotDiff Compare Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ScreenshotDiffTest, CompareIdenticalFrames) {
    TokenEfficientFrame frame_a;
    frame_a.mode = VideoMode::Text80x25;
    frame_a.text_columns = 80;
    frame_a.text_rows = 25;
    frame_a.text_content = "Hello World";

    TokenEfficientFrame frame_b = frame_a;

    ScreenshotDiff diff;
    auto result = diff.compare(frame_a, frame_b);

    EXPECT_TRUE(result.identical);
    EXPECT_FLOAT_EQ(result.total_change_percentage, 0.0f);
    EXPECT_EQ(result.changed_cells, 0u);
}

TEST(ScreenshotDiffTest, CompareDifferentFrames) {
    TokenEfficientFrame frame_a;
    frame_a.mode = VideoMode::Text80x25;
    frame_a.text_columns = 80;
    frame_a.text_rows = 25;
    frame_a.text_content = "Hello World";

    TokenEfficientFrame frame_b;
    frame_b.mode = VideoMode::Text80x25;
    frame_b.text_columns = 80;
    frame_b.text_rows = 25;
    frame_b.text_content = "Hello Earth";

    ScreenshotDiff diff;
    auto result = diff.compare(frame_a, frame_b);

    EXPECT_FALSE(result.identical);
    EXPECT_GT(result.changed_cells, 0u);
}

TEST(ScreenshotDiffTest, CompareDifferentDimensions) {
    TokenEfficientFrame frame_a;
    frame_a.mode = VideoMode::Text80x25;
    frame_a.text_columns = 80;
    frame_a.text_rows = 25;

    TokenEfficientFrame frame_b;
    frame_b.mode = VideoMode::Text40x25;
    frame_b.text_columns = 40;
    frame_b.text_rows = 25;

    ScreenshotDiff diff;
    auto result = diff.compare(frame_a, frame_b);

    EXPECT_FALSE(result.identical);
    EXPECT_FLOAT_EQ(result.total_change_percentage, 100.0f);
}

TEST(ScreenshotDiffTest, AreIdentical) {
    TokenEfficientFrame frame_a;
    frame_a.text_content = "Same";
    frame_a.text_columns = 80;
    frame_a.text_rows = 25;

    TokenEfficientFrame frame_b;
    frame_b.text_content = "Same";
    frame_b.text_columns = 80;
    frame_b.text_rows = 25;

    ScreenshotDiff diff;
    EXPECT_TRUE(diff.are_identical(frame_a, frame_b));

    frame_b.text_content = "Different";
    EXPECT_FALSE(diff.are_identical(frame_a, frame_b));
}

// ─────────────────────────────────────────────────────────────────────────────
// ScreenshotDiff CompareText Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ScreenshotDiffTest, CompareTextIdentical) {
    ScreenshotDiff diff;
    auto result = diff.compare_text("Hello", "Hello", 80, 25);

    EXPECT_TRUE(result.identical);
}

TEST(ScreenshotDiffTest, CompareTextDifferent) {
    ScreenshotDiff diff;
    auto result = diff.compare_text("Hello", "World", 80, 25);

    EXPECT_FALSE(result.identical);
}

TEST(ScreenshotDiffTest, CompareTextWithThreshold) {
    ScreenshotDiff diff;
    diff.set_threshold(50.0f);  // Allow up to 50% change

    // Small change in a mostly empty screen
    std::string text_a = "A";
    std::string text_b = "B";

    auto result = diff.compare_text(text_a, text_b, 80, 25);

    // With high threshold, small changes might be considered "identical"
    // depending on implementation
}

// ─────────────────────────────────────────────────────────────────────────────
// ScreenshotDiff CompareAgainstBaseline Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ScreenshotDiffTest, CompareAgainstBaseline) {
    TokenEfficientFrame frame;
    frame.mode = VideoMode::Text80x25;
    frame.text_columns = 80;
    frame.text_rows = 25;
    frame.text_content = "Hello World";

    ScreenshotDiff diff;
    auto result = diff.compare_against_baseline(frame, "Hello World");

    EXPECT_TRUE(result.identical);
}

TEST(ScreenshotDiffTest, CompareAgainstDifferentBaseline) {
    TokenEfficientFrame frame;
    frame.mode = VideoMode::Text80x25;
    frame.text_columns = 80;
    frame.text_rows = 25;
    frame.text_content = "Hello World";

    ScreenshotDiff diff;
    auto result = diff.compare_against_baseline(frame, "Goodbye World");

    EXPECT_FALSE(result.identical);
}

// ─────────────────────────────────────────────────────────────────────────────
// Unified Diff Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ScreenshotDiffTest, GenerateUnifiedDiffIdentical) {
    TokenEfficientFrame frame_a;
    frame_a.text_content = "Hello\nWorld\n";

    TokenEfficientFrame frame_b = frame_a;

    ScreenshotDiff diff;
    std::string unified = diff.generate_unified_diff(frame_a, frame_b);

    // Should have header but no changes
    EXPECT_NE(unified.find("---"), std::string::npos);
    EXPECT_NE(unified.find("+++"), std::string::npos);
}

TEST(ScreenshotDiffTest, GenerateUnifiedDiffDifferent) {
    TokenEfficientFrame frame_a;
    frame_a.text_columns = 80;
    frame_a.text_rows = 25;
    frame_a.text_content = "Hello\nWorld\n";

    TokenEfficientFrame frame_b;
    frame_b.text_columns = 80;
    frame_b.text_rows = 25;
    frame_b.text_content = "Hello\nEarth\n";

    ScreenshotDiff diff;
    std::string unified = diff.generate_unified_diff(frame_a, frame_b);

    // Should contain diff markers
    EXPECT_NE(unified.find("-World"), std::string::npos);
    EXPECT_NE(unified.find("+Earth"), std::string::npos);
}

TEST(ScreenshotDiffTest, GenerateUnifiedDiffCustomContext) {
    TokenEfficientFrame frame_a;
    frame_a.text_content = "Line1\nLine2\nLine3\n";
    frame_a.text_columns = 80;
    frame_a.text_rows = 25;

    TokenEfficientFrame frame_b;
    frame_b.text_content = "Line1\nModified\nLine3\n";
    frame_b.text_columns = 80;
    frame_b.text_rows = 25;

    ScreenshotDiff diff;
    std::string unified = diff.generate_unified_diff(frame_a, frame_b, 1);

    // Should have diff content
    EXPECT_NE(unified.find("@@"), std::string::npos);
}

// ─────────────────────────────────────────────────────────────────────────────
// Side-by-Side Diff Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(ScreenshotDiffTest, GenerateSideBySide) {
    TokenEfficientFrame frame_a;
    frame_a.text_columns = 40;
    frame_a.text_rows = 5;
    frame_a.text_content = "Left side";

    TokenEfficientFrame frame_b;
    frame_b.text_columns = 40;
    frame_b.text_rows = 5;
    frame_b.text_content = "Right side";

    ScreenshotDiff diff;
    std::string side_by_side = diff.generate_side_by_side(frame_a, frame_b);

    // Should contain content from both frames
    EXPECT_FALSE(side_by_side.empty());
}

// ─────────────────────────────────────────────────────────────────────────────
// Utility Function Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(FramesIdenticalTest, Identical) {
    TokenEfficientFrame a;
    a.text_content = "Same content";

    TokenEfficientFrame b;
    b.text_content = "Same content";

    EXPECT_TRUE(frames_identical(a, b));
}

TEST(FramesIdenticalTest, Different) {
    TokenEfficientFrame a;
    a.text_content = "Content A";

    TokenEfficientFrame b;
    b.text_content = "Content B";

    EXPECT_FALSE(frames_identical(a, b));
}

TEST(TextIdenticalTest, Identical) {
    EXPECT_TRUE(text_identical("hello", "hello"));
}

TEST(TextIdenticalTest, Different) {
    EXPECT_FALSE(text_identical("hello", "world"));
}

TEST(TextIdenticalTest, TrailingSpaces) {
    // With ignore_trailing_spaces=true (default)
    EXPECT_TRUE(text_identical("hello   ", "hello"));
    EXPECT_TRUE(text_identical("hello", "hello   "));

    // With ignore_trailing_spaces=false
    EXPECT_FALSE(text_identical("hello   ", "hello", false));
}

TEST(CalculateChangePercentageTest, NoChange) {
    float pct = calculate_change_percentage("hello", "hello", 80, 25);
    EXPECT_FLOAT_EQ(pct, 0.0f);
}

TEST(CalculateChangePercentageTest, FullChange) {
    // Different first character
    float pct = calculate_change_percentage("a", "b", 1, 1);
    EXPECT_FLOAT_EQ(pct, 100.0f);
}

TEST(CalculateChangePercentageTest, PartialChange) {
    // 2 of 4 characters changed
    float pct = calculate_change_percentage("abcd", "abXX", 4, 1);
    EXPECT_FLOAT_EQ(pct, 50.0f);
}

// ─────────────────────────────────────────────────────────────────────────────
// VisualRegressionTest Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(VisualRegressionTestTest, DefaultConstruction) {
    VisualRegressionTest test;

    EXPECT_FALSE(test.has_baseline());
}

TEST(VisualRegressionTestTest, SetBaseline) {
    VisualRegressionTest test;

    TokenEfficientFrame baseline;
    baseline.text_content = "Baseline content";

    test.set_baseline(baseline);

    EXPECT_TRUE(test.has_baseline());
}

TEST(VisualRegressionTestTest, SetBaselineText) {
    VisualRegressionTest test;

    test.set_baseline_text("Expected content", 80, 25);

    EXPECT_TRUE(test.has_baseline());
}

TEST(VisualRegressionTestTest, ClearBaseline) {
    VisualRegressionTest test;

    TokenEfficientFrame baseline;
    test.set_baseline(baseline);
    EXPECT_TRUE(test.has_baseline());

    test.clear_baseline();
    EXPECT_FALSE(test.has_baseline());
}

TEST(VisualRegressionTestTest, MatchesBaseline) {
    VisualRegressionTest test;

    TokenEfficientFrame baseline;
    baseline.mode = VideoMode::Text80x25;
    baseline.text_columns = 80;
    baseline.text_rows = 25;
    baseline.text_content = "Expected";
    test.set_baseline(baseline);

    TokenEfficientFrame current;
    current.mode = VideoMode::Text80x25;
    current.text_columns = 80;
    current.text_rows = 25;
    current.text_content = "Expected";

    EXPECT_TRUE(test.matches_baseline(current));

    current.text_content = "Different";
    EXPECT_FALSE(test.matches_baseline(current));
}

TEST(VisualRegressionTestTest, MatchesBaselineWithThreshold) {
    VisualRegressionTest test;

    TokenEfficientFrame baseline;
    baseline.text_columns = 80;
    baseline.text_rows = 25;
    baseline.text_content = "Expected content here";
    test.set_baseline(baseline);

    TokenEfficientFrame current;
    current.text_columns = 80;
    current.text_rows = 25;
    current.text_content = "Expected content HERE";  // Small change

    // Exact match should fail
    EXPECT_FALSE(test.matches_baseline(current, 0.0f));

    // With threshold, might pass
    // (depends on implementation details)
}

TEST(VisualRegressionTestTest, DiffAgainstBaseline) {
    VisualRegressionTest test;

    TokenEfficientFrame baseline;
    baseline.mode = VideoMode::Text80x25;
    baseline.text_columns = 80;
    baseline.text_rows = 25;
    baseline.text_content = "Original";
    test.set_baseline(baseline);

    TokenEfficientFrame current;
    current.mode = VideoMode::Text80x25;
    current.text_columns = 80;
    current.text_rows = 25;
    current.text_content = "Modified";

    auto result = test.diff_against_baseline(current);

    EXPECT_FALSE(result.identical);
}
