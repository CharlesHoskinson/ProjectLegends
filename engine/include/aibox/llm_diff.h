/**
 * @file llm_diff.h
 * @brief Screenshot diff utility for visual regression testing.
 *
 * Provides tools for comparing text mode frames and identifying
 * changed regions for LLM visual regression testing.
 */

#pragma once

#include "llm_frame.h"

#include <cstdint>
#include <optional>
#include <string>
#include <vector>

namespace aibox::llm {

// ─────────────────────────────────────────────────────────────────────────────
// Diff Region
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief A rectangular region of difference.
 */
struct DiffRegion {
    uint16_t x{0};            ///< Left column (0-based)
    uint16_t y{0};            ///< Top row (0-based)
    uint16_t width{0};        ///< Width in columns
    uint16_t height{0};       ///< Height in rows
    float change_ratio{0.0f}; ///< Percentage of cells changed in region (0.0-1.0)

    /**
     * @brief Get the number of cells in this region.
     */
    [[nodiscard]] size_t cell_count() const noexcept {
        return static_cast<size_t>(width) * height;
    }

    [[nodiscard]] bool operator==(const DiffRegion& other) const noexcept {
        return x == other.x && y == other.y &&
               width == other.width && height == other.height &&
               change_ratio == other.change_ratio;
    }

    [[nodiscard]] bool operator!=(const DiffRegion& other) const noexcept {
        return !(*this == other);
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// Diff Result
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Result of comparing two frames.
 */
struct ScreenshotDiffResult {
    bool identical{true};                ///< True if no differences
    float total_change_percentage{0.0f}; ///< Overall change percentage (0-100)
    size_t changed_cells{0};             ///< Number of changed cells
    size_t total_cells{0};               ///< Total number of cells
    std::vector<DiffRegion> regions;     ///< Changed regions
    std::string text_diff;               ///< Human-readable diff

    /**
     * @brief Check if change is below threshold.
     *
     * @param threshold_percent Threshold percentage (0-100)
     * @return True if change is at or below threshold
     */
    [[nodiscard]] bool within_threshold(float threshold_percent) const noexcept {
        return total_change_percentage <= threshold_percent;
    }

    /**
     * @brief Get the largest changed region.
     */
    [[nodiscard]] const DiffRegion* largest_region() const noexcept;

    /**
     * @brief Get summary string.
     */
    [[nodiscard]] std::string summary() const;
};

// ─────────────────────────────────────────────────────────────────────────────
// Diff Options
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Options for screenshot comparison.
 */
struct DiffOptions {
    float threshold{0.0f};          ///< Ignore changes below this percentage (0-100)
    uint16_t min_region_size{1};    ///< Minimum region size to report (cells)
    bool merge_adjacent{true};      ///< Merge adjacent changed regions
    bool ignore_cursor{false};      ///< Ignore cursor position differences
    bool ignore_trailing_spaces{true}; ///< Ignore trailing space differences
    int context_lines{3};           ///< Context lines for unified diff
};

// ─────────────────────────────────────────────────────────────────────────────
// Screenshot Diff
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Utility for comparing text mode screenshots.
 *
 * Example:
 * @code
 *   ScreenshotDiff diff;
 *   diff.set_threshold(0.5f);  // Ignore < 0.5% changes
 *
 *   auto result = diff.compare(frame_a, frame_b);
 *   if (!result.identical) {
 *       std::cout << result.text_diff << std::endl;
 *   }
 * @endcode
 */
class ScreenshotDiff {
public:
    /**
     * @brief Default constructor with default options.
     */
    ScreenshotDiff() = default;

    /**
     * @brief Construct with options.
     */
    explicit ScreenshotDiff(const DiffOptions& options)
        : options_(options) {}

    /**
     * @brief Set comparison options.
     */
    void set_options(const DiffOptions& options) noexcept {
        options_ = options;
    }

    /**
     * @brief Get current options.
     */
    [[nodiscard]] const DiffOptions& options() const noexcept {
        return options_;
    }

    /**
     * @brief Set threshold for ignoring small changes.
     *
     * @param threshold_percent Percentage (0-100)
     */
    void set_threshold(float threshold_percent) noexcept {
        options_.threshold = threshold_percent;
    }

    /**
     * @brief Set minimum region size to report.
     */
    void set_min_region_size(uint16_t min_cells) noexcept {
        options_.min_region_size = min_cells;
    }

    /**
     * @brief Compare two frames.
     *
     * @param frame_a First frame
     * @param frame_b Second frame
     * @return Comparison result
     */
    [[nodiscard]] ScreenshotDiffResult compare(
        const TokenEfficientFrame& frame_a,
        const TokenEfficientFrame& frame_b
    ) const;

    /**
     * @brief Compare frame text content directly.
     *
     * @param text_a First frame text content
     * @param text_b Second frame text content
     * @param columns Number of columns
     * @param rows Number of rows
     * @return Comparison result
     */
    [[nodiscard]] ScreenshotDiffResult compare_text(
        const std::string& text_a,
        const std::string& text_b,
        uint8_t columns,
        uint8_t rows
    ) const;

    /**
     * @brief Compare frame against baseline string.
     *
     * @param frame Frame to compare
     * @param baseline_text Expected text content
     * @return Comparison result
     */
    [[nodiscard]] ScreenshotDiffResult compare_against_baseline(
        const TokenEfficientFrame& frame,
        const std::string& baseline_text
    ) const;

    /**
     * @brief Generate unified diff output.
     *
     * @param frame_a First frame
     * @param frame_b Second frame
     * @param context_lines Number of context lines (default from options)
     * @return Unified diff string
     */
    [[nodiscard]] std::string generate_unified_diff(
        const TokenEfficientFrame& frame_a,
        const TokenEfficientFrame& frame_b,
        std::optional<int> context_lines = std::nullopt
    ) const;

    /**
     * @brief Generate side-by-side diff.
     *
     * @param frame_a First frame
     * @param frame_b Second frame
     * @return Side-by-side comparison string
     */
    [[nodiscard]] std::string generate_side_by_side(
        const TokenEfficientFrame& frame_a,
        const TokenEfficientFrame& frame_b
    ) const;

    /**
     * @brief Check if two frames are identical (convenience method).
     *
     * @param frame_a First frame
     * @param frame_b Second frame
     * @return True if frames are identical
     */
    [[nodiscard]] bool are_identical(
        const TokenEfficientFrame& frame_a,
        const TokenEfficientFrame& frame_b
    ) const {
        return compare(frame_a, frame_b).identical;
    }

private:
    DiffOptions options_;

    /**
     * @brief Find connected regions of changed cells.
     */
    [[nodiscard]] std::vector<DiffRegion> find_changed_regions(
        const std::vector<bool>& changed_cells,
        uint8_t columns,
        uint8_t rows
    ) const;

    /**
     * @brief Merge adjacent regions.
     */
    [[nodiscard]] std::vector<DiffRegion> merge_regions(
        const std::vector<DiffRegion>& regions
    ) const;

    /**
     * @brief Parse text into lines with padding.
     */
    [[nodiscard]] std::vector<std::string> parse_lines(
        const std::string& text,
        uint8_t columns,
        uint8_t rows
    ) const;
};

// ─────────────────────────────────────────────────────────────────────────────
// Diff Utilities
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Quick check if two frames are identical.
 *
 * Faster than full compare() when you only need a boolean result.
 */
[[nodiscard]] bool frames_identical(
    const TokenEfficientFrame& a,
    const TokenEfficientFrame& b
) noexcept;

/**
 * @brief Quick check if two text contents are identical.
 */
[[nodiscard]] bool text_identical(
    const std::string& a,
    const std::string& b,
    bool ignore_trailing_spaces = true
) noexcept;

/**
 * @brief Calculate percentage of changed cells.
 *
 * @param a First text
 * @param b Second text
 * @param columns Number of columns
 * @param rows Number of rows
 * @return Change percentage (0-100)
 */
[[nodiscard]] float calculate_change_percentage(
    const std::string& a,
    const std::string& b,
    uint8_t columns,
    uint8_t rows
) noexcept;

// ─────────────────────────────────────────────────────────────────────────────
// Visual Regression Test Helper
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Helper for visual regression testing.
 *
 * Stores baseline frames and compares against them.
 */
class VisualRegressionTest {
public:
    /**
     * @brief Set baseline frame.
     */
    void set_baseline(const TokenEfficientFrame& frame) {
        baseline_ = frame;
    }

    /**
     * @brief Set baseline from text.
     */
    void set_baseline_text(
        const std::string& text,
        uint8_t columns = 80,
        uint8_t rows = 25
    );

    /**
     * @brief Check if current frame matches baseline.
     *
     * @param current Current frame
     * @param threshold_percent Maximum allowed change percentage
     * @return True if within threshold
     */
    [[nodiscard]] bool matches_baseline(
        const TokenEfficientFrame& current,
        float threshold_percent = 0.0f
    ) const;

    /**
     * @brief Get diff against baseline.
     */
    [[nodiscard]] ScreenshotDiffResult diff_against_baseline(
        const TokenEfficientFrame& current
    ) const;

    /**
     * @brief Check if baseline is set.
     */
    [[nodiscard]] bool has_baseline() const noexcept {
        return baseline_.has_value();
    }

    /**
     * @brief Clear baseline.
     */
    void clear_baseline() noexcept {
        baseline_.reset();
    }

private:
    std::optional<TokenEfficientFrame> baseline_;
    mutable ScreenshotDiff diff_;  ///< Mutable to allow threshold changes in const methods
};

} // namespace aibox::llm
