/**
 * @file llm_diff.cpp
 * @brief Implementation of LLM screenshot diff utility.
 */

#include <aibox/llm_diff.h>
#include <aibox/llm_serializer.h>
#include <algorithm>
#include <sstream>

namespace aibox::llm {

// ─────────────────────────────────────────────────────────────────────────────
// ScreenshotDiffResult Implementation
// ─────────────────────────────────────────────────────────────────────────────

const DiffRegion* ScreenshotDiffResult::largest_region() const noexcept {
    if (regions.empty()) {
        return nullptr;
    }

    auto it = std::max_element(regions.begin(), regions.end(),
        [](const DiffRegion& a, const DiffRegion& b) {
            return a.cell_count() < b.cell_count();
        });

    return &(*it);
}

std::string ScreenshotDiffResult::summary() const {
    std::ostringstream oss;

    if (identical) {
        oss << "Frames are identical";
    } else {
        oss << "Changed: " << changed_cells << "/" << total_cells
            << " cells (" << total_change_percentage << "%)";
        if (!regions.empty()) {
            oss << ", " << regions.size() << " region(s)";
        }
    }

    return oss.str();
}

// ─────────────────────────────────────────────────────────────────────────────
// ScreenshotDiff Implementation
// ─────────────────────────────────────────────────────────────────────────────

ScreenshotDiffResult ScreenshotDiff::compare(
    const TokenEfficientFrame& frame_a,
    const TokenEfficientFrame& frame_b
) const {
    ScreenshotDiffResult result;

    // Check dimensions match
    if (frame_a.text_columns != frame_b.text_columns ||
        frame_a.text_rows != frame_b.text_rows) {
        result.identical = false;
        result.total_change_percentage = 100.0f;
        result.text_diff = "Frame dimensions differ";
        return result;
    }

    return compare_text(
        frame_a.text_content,
        frame_b.text_content,
        frame_a.text_columns,
        frame_a.text_rows
    );
}

ScreenshotDiffResult ScreenshotDiff::compare_text(
    const std::string& text_a,
    const std::string& text_b,
    uint8_t columns,
    uint8_t rows
) const {
    ScreenshotDiffResult result;
    result.total_cells = static_cast<size_t>(columns) * rows;
    result.identical = true;

    // Parse lines
    auto lines_a = parse_lines(text_a, columns, rows);
    auto lines_b = parse_lines(text_b, columns, rows);

    // Compare cells
    std::vector<bool> changed(result.total_cells, false);

    for (size_t row = 0; row < rows; ++row) {
        const std::string& line_a = lines_a[row];
        const std::string& line_b = lines_b[row];

        for (size_t col = 0; col < columns; ++col) {
            char a = col < line_a.size() ? line_a[col] : ' ';
            char b = col < line_b.size() ? line_b[col] : ' ';

            // Handle trailing space ignoring
            if (options_.ignore_trailing_spaces) {
                // If both are spaces at end of line, consider equal
                bool a_is_trailing = (a == ' ' && col >= line_a.find_last_not_of(' ') + 1);
                bool b_is_trailing = (b == ' ' && col >= line_b.find_last_not_of(' ') + 1);
                if (a_is_trailing && b_is_trailing) {
                    continue;
                }
            }

            if (a != b) {
                changed[row * columns + col] = true;
                result.changed_cells++;
                result.identical = false;
            }
        }
    }

    // Calculate percentage
    result.total_change_percentage =
        100.0f * result.changed_cells / result.total_cells;

    // Apply threshold
    if (result.total_change_percentage <= options_.threshold) {
        result.identical = true;
        result.changed_cells = 0;
        result.total_change_percentage = 0.0f;
        return result;
    }

    // Find regions
    if (!result.identical) {
        result.regions = find_changed_regions(changed, columns, rows);

        if (options_.merge_adjacent) {
            result.regions = merge_regions(result.regions);
        }

        // Filter by minimum size
        result.regions.erase(
            std::remove_if(result.regions.begin(), result.regions.end(),
                [this](const DiffRegion& r) {
                    return r.cell_count() < options_.min_region_size;
                }),
            result.regions.end()
        );
    }

    return result;
}

ScreenshotDiffResult ScreenshotDiff::compare_against_baseline(
    const TokenEfficientFrame& frame,
    const std::string& baseline_text
) const {
    return compare_text(
        frame.text_content,
        baseline_text,
        frame.text_columns,
        frame.text_rows
    );
}

std::string ScreenshotDiff::generate_unified_diff(
    const TokenEfficientFrame& frame_a,
    const TokenEfficientFrame& frame_b,
    std::optional<int> context_lines
) const {
    int context = context_lines.value_or(options_.context_lines);

    std::ostringstream oss;
    oss << "--- Frame A\n";
    oss << "+++ Frame B\n";

    auto lines_a = parse_lines(frame_a.text_content, frame_a.text_columns, frame_a.text_rows);
    auto lines_b = parse_lines(frame_b.text_content, frame_b.text_columns, frame_b.text_rows);

    size_t max_lines = std::max(lines_a.size(), lines_b.size());

    for (size_t i = 0; i < max_lines; ++i) {
        std::string la = i < lines_a.size() ? lines_a[i] : "";
        std::string lb = i < lines_b.size() ? lines_b[i] : "";

        if (la != lb) {
            oss << "@@ -" << (i + 1) << " +" << (i + 1) << " @@\n";

            // Context before (limited)
            for (int j = std::max(0, static_cast<int>(i) - context);
                 j < static_cast<int>(i); ++j) {
                if (j < static_cast<int>(lines_a.size())) {
                    oss << " " << lines_a[j] << "\n";
                }
            }

            oss << "-" << la << "\n";
            oss << "+" << lb << "\n";
        }
    }

    return oss.str();
}

std::string ScreenshotDiff::generate_side_by_side(
    const TokenEfficientFrame& frame_a,
    const TokenEfficientFrame& frame_b
) const {
    std::ostringstream oss;

    auto lines_a = parse_lines(frame_a.text_content, frame_a.text_columns, frame_a.text_rows);
    auto lines_b = parse_lines(frame_b.text_content, frame_b.text_columns, frame_b.text_rows);

    size_t max_lines = std::max(lines_a.size(), lines_b.size());
    size_t width_a = frame_a.text_columns;

    oss << std::string(width_a, '=') << " | " << std::string(width_a, '=') << "\n";

    for (size_t i = 0; i < max_lines; ++i) {
        std::string la = i < lines_a.size() ? lines_a[i] : "";
        std::string lb = i < lines_b.size() ? lines_b[i] : "";

        // Pad to width
        while (la.length() < width_a) la += ' ';
        while (lb.length() < width_a) lb += ' ';

        char marker = (la != lb) ? '!' : ' ';
        oss << la << " " << marker << " " << lb << "\n";
    }

    return oss.str();
}

std::vector<DiffRegion> ScreenshotDiff::find_changed_regions(
    const std::vector<bool>& changed_cells,
    uint8_t columns,
    uint8_t rows
) const {
    std::vector<DiffRegion> regions;

    // Simple row-based region detection
    uint16_t region_start = UINT16_MAX;

    for (uint16_t row = 0; row < rows; ++row) {
        bool row_changed = false;
        size_t changed_in_row = 0;

        for (uint16_t col = 0; col < columns; ++col) {
            if (changed_cells[row * columns + col]) {
                row_changed = true;
                ++changed_in_row;
            }
        }

        if (row_changed && region_start == UINT16_MAX) {
            region_start = row;
        } else if (!row_changed && region_start != UINT16_MAX) {
            // End of region
            DiffRegion region;
            region.x = 0;
            region.y = region_start;
            region.width = columns;
            region.height = row - region_start;

            // Calculate change ratio
            size_t total_in_region = region.cell_count();
            size_t changed_count = 0;
            for (uint16_t r = region.y; r < region.y + region.height; ++r) {
                for (uint16_t c = 0; c < columns; ++c) {
                    if (changed_cells[r * columns + c]) {
                        ++changed_count;
                    }
                }
            }
            region.change_ratio = static_cast<float>(changed_count) / total_in_region;

            regions.push_back(region);
            region_start = UINT16_MAX;
        }
    }

    // Handle region extending to bottom
    if (region_start != UINT16_MAX) {
        DiffRegion region;
        region.x = 0;
        region.y = region_start;
        region.width = columns;
        region.height = rows - region_start;
        region.change_ratio = 1.0f;
        regions.push_back(region);
    }

    return regions;
}

std::vector<DiffRegion> ScreenshotDiff::merge_regions(
    const std::vector<DiffRegion>& regions
) const {
    if (regions.size() < 2) {
        return regions;
    }

    std::vector<DiffRegion> merged;
    merged.push_back(regions[0]);

    for (size_t i = 1; i < regions.size(); ++i) {
        DiffRegion& last = merged.back();
        const DiffRegion& current = regions[i];

        // Check if adjacent (within 1 row)
        if (current.y <= last.y + last.height + 1 &&
            current.x == last.x && current.width == last.width) {
            // Merge
            last.height = current.y + current.height - last.y;
            last.change_ratio = (last.change_ratio + current.change_ratio) / 2.0f;
        } else {
            merged.push_back(current);
        }
    }

    return merged;
}

std::vector<std::string> ScreenshotDiff::parse_lines(
    const std::string& text,
    uint8_t columns,
    uint8_t rows
) const {
    std::vector<std::string> lines;
    lines.reserve(rows);

    std::istringstream stream(text);
    std::string line;

    while (std::getline(stream, line) && lines.size() < rows) {
        // Pad to column width
        while (line.length() < columns) {
            line += ' ';
        }
        if (line.length() > columns) {
            line = line.substr(0, columns);
        }
        lines.push_back(line);
    }

    // Fill remaining rows
    while (lines.size() < rows) {
        lines.push_back(std::string(columns, ' '));
    }

    return lines;
}

// ─────────────────────────────────────────────────────────────────────────────
// Utility Functions
// ─────────────────────────────────────────────────────────────────────────────

bool frames_identical(
    const TokenEfficientFrame& a,
    const TokenEfficientFrame& b
) noexcept {
    if (a.text_columns != b.text_columns || a.text_rows != b.text_rows) {
        return false;
    }
    return a.text_content == b.text_content;
}

bool text_identical(
    const std::string& a,
    const std::string& b,
    bool ignore_trailing_spaces
) noexcept {
    if (!ignore_trailing_spaces) {
        return a == b;
    }

    // Compare line by line, ignoring trailing spaces
    std::istringstream stream_a(a);
    std::istringstream stream_b(b);
    std::string line_a, line_b;

    while (true) {
        bool has_a = static_cast<bool>(std::getline(stream_a, line_a));
        bool has_b = static_cast<bool>(std::getline(stream_b, line_b));

        if (!has_a && !has_b) {
            return true;  // Both exhausted
        }
        if (has_a != has_b) {
            return false;  // Different line counts
        }

        // Trim trailing spaces
        auto trim = [](const std::string& s) {
            auto end = s.find_last_not_of(' ');
            if (end == std::string::npos) return std::string();
            return s.substr(0, end + 1);
        };

        if (trim(line_a) != trim(line_b)) {
            return false;
        }
    }
}

float calculate_change_percentage(
    const std::string& a,
    const std::string& b,
    uint8_t columns,
    uint8_t rows
) noexcept {
    size_t total_cells = static_cast<size_t>(columns) * rows;
    if (total_cells == 0) {
        return 0.0f;
    }

    size_t changed = 0;

    // Simple character-by-character comparison
    size_t max_len = std::max(a.length(), b.length());

    for (size_t i = 0; i < max_len && i < total_cells; ++i) {
        char ca = i < a.length() ? a[i] : ' ';
        char cb = i < b.length() ? b[i] : ' ';
        if (ca != cb) {
            ++changed;
        }
    }

    return 100.0f * changed / total_cells;
}

// ─────────────────────────────────────────────────────────────────────────────
// VisualRegressionTest Implementation
// ─────────────────────────────────────────────────────────────────────────────

void VisualRegressionTest::set_baseline_text(
    const std::string& text,
    uint8_t columns,
    uint8_t rows
) {
    TokenEfficientFrame frame;
    frame.mode = VideoMode::Text80x25;  // Default
    frame.text_columns = columns;
    frame.text_rows = rows;
    frame.text_content = text;
    baseline_ = frame;
}

bool VisualRegressionTest::matches_baseline(
    const TokenEfficientFrame& current,
    float threshold_percent
) const {
    if (!baseline_) {
        return false;
    }

    diff_.set_threshold(threshold_percent);
    auto result = diff_.compare(*baseline_, current);
    return result.identical;
}

ScreenshotDiffResult VisualRegressionTest::diff_against_baseline(
    const TokenEfficientFrame& current
) const {
    if (!baseline_) {
        ScreenshotDiffResult result;
        result.identical = false;
        result.text_diff = "No baseline set";
        return result;
    }

    return diff_.compare(*baseline_, current);
}

} // namespace aibox::llm
