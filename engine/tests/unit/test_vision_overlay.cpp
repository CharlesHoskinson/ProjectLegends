/**
 * @file test_vision_overlay.cpp
 * @brief Unit tests for vision_overlay.h
 */

#include <gtest/gtest.h>
#include "aibox/vision_overlay.h"
#include "aibox/vision_framebuffer.h"

using namespace aibox::vision;

// ─────────────────────────────────────────────────────────────────────────────
// BoundingBox Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(BoundingBoxTest, DefaultValues) {
    BoundingBox box;

    EXPECT_EQ(box.id, INVALID_OVERLAY);
    EXPECT_EQ(box.x, 0);
    EXPECT_EQ(box.y, 0);
    EXPECT_EQ(box.width, 0);
    EXPECT_EQ(box.height, 0);
    EXPECT_EQ(box.color.r, 255);  // Default red
    EXPECT_EQ(box.color.g, 0);
    EXPECT_EQ(box.color.b, 0);
    EXPECT_EQ(box.color.a, 255);
    EXPECT_EQ(box.thickness, 2);
    EXPECT_FALSE(box.filled);
    EXPECT_TRUE(box.visible);
}

TEST(BoundingBoxTest, RightAndBottom) {
    BoundingBox box;
    box.x = 10;
    box.y = 20;
    box.width = 50;
    box.height = 30;

    EXPECT_EQ(box.right(), 60);
    EXPECT_EQ(box.bottom(), 50);
}

TEST(BoundingBoxTest, Area) {
    BoundingBox box;
    box.width = 100;
    box.height = 50;

    EXPECT_EQ(box.area(), 5000);
}

TEST(BoundingBoxTest, Contains) {
    BoundingBox box;
    box.x = 10;
    box.y = 20;
    box.width = 50;
    box.height = 30;

    // Inside
    EXPECT_TRUE(box.contains(10, 20));  // Top-left corner
    EXPECT_TRUE(box.contains(30, 35));  // Center
    EXPECT_TRUE(box.contains(59, 49));  // Bottom-right edge (exclusive)

    // Outside
    EXPECT_FALSE(box.contains(9, 20));   // Left of box
    EXPECT_FALSE(box.contains(60, 35));  // Right of box
    EXPECT_FALSE(box.contains(30, 19));  // Above box
    EXPECT_FALSE(box.contains(30, 50));  // Below box
}

// ─────────────────────────────────────────────────────────────────────────────
// TextLabel Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(TextLabelTest, DefaultValues) {
    TextLabel label;

    EXPECT_EQ(label.id, INVALID_OVERLAY);
    EXPECT_TRUE(label.text.empty());
    EXPECT_EQ(label.color.r, 255);  // Default white
    EXPECT_EQ(label.color.g, 255);
    EXPECT_EQ(label.color.b, 255);
    EXPECT_EQ(label.font_size, 8);
    EXPECT_TRUE(label.has_background);
    EXPECT_EQ(label.padding, 2);
}

TEST(TextLabelTest, CalculatedWidth) {
    TextLabel label;
    label.text = "Hello";
    label.font_size = 8;
    label.padding = 2;

    // 5 chars * 8 + 2 * 2 = 44
    EXPECT_EQ(label.calculated_width(), 44);
}

TEST(TextLabelTest, CalculatedHeight) {
    TextLabel label;
    label.font_size = 8;
    label.padding = 2;

    // 8 + 2 * 2 = 12
    EXPECT_EQ(label.calculated_height(), 12);
}

TEST(TextLabelTest, CalculatedWidthEmpty) {
    TextLabel label;
    label.text = "";
    label.font_size = 8;
    label.padding = 2;

    // 0 chars * 8 + 2 * 2 = 4
    EXPECT_EQ(label.calculated_width(), 4);
}

// ─────────────────────────────────────────────────────────────────────────────
// HighlightRegion Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(HighlightRegionTest, DefaultValues) {
    HighlightRegion hl;

    EXPECT_EQ(hl.id, INVALID_OVERLAY);
    EXPECT_EQ(hl.width, 0);
    EXPECT_EQ(hl.height, 0);
    EXPECT_EQ(hl.color.r, 255);  // Default semi-transparent yellow
    EXPECT_EQ(hl.color.g, 255);
    EXPECT_EQ(hl.color.b, 0);
    EXPECT_EQ(hl.color.a, 128);
}

// ─────────────────────────────────────────────────────────────────────────────
// LineOverlay Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(LineOverlayTest, DefaultValues) {
    LineOverlay line;

    EXPECT_EQ(line.id, INVALID_OVERLAY);
    EXPECT_EQ(line.x, 0);
    EXPECT_EQ(line.y, 0);
    EXPECT_EQ(line.x2, 0);
    EXPECT_EQ(line.y2, 0);
    EXPECT_EQ(line.thickness, 1);
}

TEST(LineOverlayTest, LengthHorizontal) {
    LineOverlay line;
    line.x = 0;
    line.y = 0;
    line.x2 = 100;
    line.y2 = 0;

    EXPECT_FLOAT_EQ(line.length(), 100.0f);
}

TEST(LineOverlayTest, LengthVertical) {
    LineOverlay line;
    line.x = 0;
    line.y = 0;
    line.x2 = 0;
    line.y2 = 50;

    EXPECT_FLOAT_EQ(line.length(), 50.0f);
}

TEST(LineOverlayTest, LengthDiagonal) {
    LineOverlay line;
    line.x = 0;
    line.y = 0;
    line.x2 = 3;
    line.y2 = 4;

    EXPECT_FLOAT_EQ(line.length(), 5.0f);  // 3-4-5 triangle
}

// ─────────────────────────────────────────────────────────────────────────────
// CircleOverlay Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(CircleOverlayTest, DefaultValues) {
    CircleOverlay circle;

    EXPECT_EQ(circle.id, INVALID_OVERLAY);
    EXPECT_EQ(circle.radius_x, 0);
    EXPECT_EQ(circle.radius_y, 0);
    EXPECT_EQ(circle.thickness, 2);
    EXPECT_FALSE(circle.filled);
}

TEST(CircleOverlayTest, IsCircle) {
    CircleOverlay circle;
    circle.radius_x = 50;
    circle.radius_y = 50;

    EXPECT_TRUE(circle.is_circle());

    circle.radius_y = 30;
    EXPECT_FALSE(circle.is_circle());  // Now an ellipse
}

TEST(CircleOverlayTest, RadiusGetter) {
    CircleOverlay circle;
    circle.radius_x = 50;
    circle.radius_y = 50;

    EXPECT_EQ(circle.radius(), 50);
}

// ─────────────────────────────────────────────────────────────────────────────
// Crosshair Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(CrosshairTest, DefaultValues) {
    Crosshair ch;

    EXPECT_EQ(ch.id, INVALID_OVERLAY);
    EXPECT_EQ(ch.size, 10);
    EXPECT_EQ(ch.thickness, 1);
    EXPECT_FALSE(ch.show_circle);
    EXPECT_EQ(ch.circle_radius, 5);
}

// ─────────────────────────────────────────────────────────────────────────────
// Overlay Variant Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(OverlayVariantTest, GetOverlayId) {
    BoundingBox box;
    box.id = 42;

    Overlay overlay = box;
    EXPECT_EQ(get_overlay_id(overlay), 42);
}

TEST(OverlayVariantTest, IsOverlayVisible) {
    TextLabel label;
    label.visible = true;

    Overlay overlay = label;
    EXPECT_TRUE(is_overlay_visible(overlay));

    label.visible = false;
    overlay = label;
    EXPECT_FALSE(is_overlay_visible(overlay));
}

TEST(OverlayVariantTest, GetOverlayZOrder) {
    HighlightRegion hl;
    hl.z_order = 5;

    Overlay overlay = hl;
    EXPECT_EQ(get_overlay_z_order(overlay), 5);
}

// ─────────────────────────────────────────────────────────────────────────────
// OverlayManager Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(OverlayManagerTest, InitiallyEmpty) {
    OverlayManager manager;

    EXPECT_TRUE(manager.empty());
    EXPECT_EQ(manager.count(), 0);
}

TEST(OverlayManagerTest, AddBoundingBox) {
    OverlayManager manager;

    BoundingBox box;
    box.x = 10;
    box.y = 20;
    box.width = 100;
    box.height = 50;

    OverlayId id = manager.add(box);

    EXPECT_NE(id, INVALID_OVERLAY);
    EXPECT_EQ(manager.count(), 1);
    EXPECT_FALSE(manager.empty());
}

TEST(OverlayManagerTest, AddBboxSimplified) {
    OverlayManager manager;

    OverlayId id = manager.add_bbox(10, 20, 100, 50);

    EXPECT_NE(id, INVALID_OVERLAY);
    EXPECT_EQ(manager.count(), 1);
}

TEST(OverlayManagerTest, AddBboxWithColor) {
    OverlayManager manager;

    RgbaColor green{0, 255, 0, 255};
    OverlayId id = manager.add_bbox(10, 20, 100, 50, green, 3);

    EXPECT_NE(id, INVALID_OVERLAY);

    auto overlay = manager.get(id);
    EXPECT_TRUE(overlay.has_value());

    const BoundingBox& box = std::get<BoundingBox>(*overlay);
    EXPECT_EQ(box.color.g, 255);
    EXPECT_EQ(box.thickness, 3);
}

TEST(OverlayManagerTest, AddLabel) {
    OverlayManager manager;

    OverlayId id = manager.add_label(50, 100, "Test Label");

    EXPECT_NE(id, INVALID_OVERLAY);
    EXPECT_EQ(manager.count(), 1);
}

TEST(OverlayManagerTest, AddHighlight) {
    OverlayManager manager;

    OverlayId id = manager.add_highlight(0, 0, 320, 200);

    EXPECT_NE(id, INVALID_OVERLAY);
    EXPECT_EQ(manager.count(), 1);
}

TEST(OverlayManagerTest, AddMultipleOverlays) {
    OverlayManager manager;

    OverlayId id1 = manager.add_bbox(10, 10, 50, 50);
    OverlayId id2 = manager.add_label(10, 5, "Box 1");
    OverlayId id3 = manager.add_bbox(100, 100, 80, 60);

    EXPECT_EQ(manager.count(), 3);
    EXPECT_NE(id1, id2);
    EXPECT_NE(id2, id3);
    EXPECT_NE(id1, id3);
}

TEST(OverlayManagerTest, GetOverlay) {
    OverlayManager manager;

    BoundingBox box;
    box.x = 42;
    box.y = 99;

    OverlayId id = manager.add(box);

    auto result = manager.get(id);
    EXPECT_TRUE(result.has_value());

    const BoundingBox& retrieved = std::get<BoundingBox>(*result);
    EXPECT_EQ(retrieved.x, 42);
    EXPECT_EQ(retrieved.y, 99);
}

TEST(OverlayManagerTest, GetOverlayNotFound) {
    OverlayManager manager;

    auto result = manager.get(999);
    EXPECT_FALSE(result.has_value());
}

TEST(OverlayManagerTest, Remove) {
    OverlayManager manager;

    OverlayId id = manager.add_bbox(10, 10, 50, 50);
    EXPECT_EQ(manager.count(), 1);

    bool removed = manager.remove(id);
    EXPECT_TRUE(removed);
    EXPECT_EQ(manager.count(), 0);
}

TEST(OverlayManagerTest, RemoveNotFound) {
    OverlayManager manager;

    bool removed = manager.remove(999);
    EXPECT_FALSE(removed);
}

TEST(OverlayManagerTest, RemoveMiddleOverlay) {
    OverlayManager manager;

    OverlayId id1 = manager.add_bbox(10, 10, 50, 50);
    OverlayId id2 = manager.add_bbox(100, 10, 50, 50);
    OverlayId id3 = manager.add_bbox(200, 10, 50, 50);

    EXPECT_EQ(manager.count(), 3);

    manager.remove(id2);
    EXPECT_EQ(manager.count(), 2);

    // Other overlays should still exist
    EXPECT_TRUE(manager.get(id1).has_value());
    EXPECT_FALSE(manager.get(id2).has_value());
    EXPECT_TRUE(manager.get(id3).has_value());
}

TEST(OverlayManagerTest, Clear) {
    OverlayManager manager;

    manager.add_bbox(10, 10, 50, 50);
    manager.add_bbox(100, 10, 50, 50);
    manager.add_label(10, 5, "Label");

    EXPECT_EQ(manager.count(), 3);

    manager.clear();
    EXPECT_EQ(manager.count(), 0);
    EXPECT_TRUE(manager.empty());
}

TEST(OverlayManagerTest, SetVisible) {
    OverlayManager manager;

    OverlayId id = manager.add_bbox(10, 10, 50, 50);

    bool success = manager.set_visible(id, false);
    EXPECT_TRUE(success);

    auto overlay = manager.get(id);
    EXPECT_FALSE(is_overlay_visible(*overlay));
}

TEST(OverlayManagerTest, SetVisibleNotFound) {
    OverlayManager manager;

    bool success = manager.set_visible(999, false);
    EXPECT_FALSE(success);
}

TEST(OverlayManagerTest, SetZOrder) {
    OverlayManager manager;

    OverlayId id = manager.add_bbox(10, 10, 50, 50);

    bool success = manager.set_z_order(id, 10);
    EXPECT_TRUE(success);

    auto overlay = manager.get(id);
    EXPECT_EQ(get_overlay_z_order(*overlay), 10);
}

TEST(OverlayManagerTest, ZOrderSorting) {
    OverlayManager manager;

    BoundingBox box1;
    box1.z_order = 5;
    BoundingBox box2;
    box2.z_order = 1;
    BoundingBox box3;
    box3.z_order = 10;

    manager.add(box1);
    manager.add(box2);
    manager.add(box3);

    const auto& overlays = manager.get_all();
    EXPECT_EQ(overlays.size(), 3);

    // Should be sorted by z_order ascending
    EXPECT_EQ(get_overlay_z_order(overlays[0]), 1);
    EXPECT_EQ(get_overlay_z_order(overlays[1]), 5);
    EXPECT_EQ(get_overlay_z_order(overlays[2]), 10);
}

TEST(OverlayManagerTest, Update) {
    OverlayManager manager;

    BoundingBox box;
    box.x = 10;
    box.y = 20;
    OverlayId id = manager.add(box);

    // Modify and update
    box.x = 100;
    box.y = 200;
    box.id = id;  // Preserve the ID
    bool updated = manager.update(id, box);

    EXPECT_TRUE(updated);

    auto result = manager.get(id);
    const BoundingBox& retrieved = std::get<BoundingBox>(*result);
    EXPECT_EQ(retrieved.x, 100);
    EXPECT_EQ(retrieved.y, 200);
}

TEST(OverlayManagerTest, UpdateNotFound) {
    OverlayManager manager;

    BoundingBox box;
    bool updated = manager.update(999, box);

    EXPECT_FALSE(updated);
}

// ─────────────────────────────────────────────────────────────────────────────
// Render Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(OverlayManagerTest, RenderEmpty) {
    OverlayManager manager;

    std::vector<uint8_t> buffer(320 * 200 * 4, 0);
    manager.render(Span<uint8_t>(buffer.data(), buffer.size()), 320, 200);

    // Buffer should remain all zeros (transparent)
    bool all_zero = true;
    for (size_t i = 0; i < buffer.size(); ++i) {
        if (buffer[i] != 0) {
            all_zero = false;
            break;
        }
    }
    EXPECT_TRUE(all_zero);
}

TEST(OverlayManagerTest, RenderWithBoundingBox) {
    OverlayManager manager;

    manager.add_bbox(10, 10, 50, 30, RgbaColor{255, 0, 0, 255}, 2);

    std::vector<uint8_t> buffer(320 * 200 * 4, 0);
    manager.render(Span<uint8_t>(buffer.data(), buffer.size()), 320, 200);

    // Check that some pixels were rendered (not all zero)
    bool has_content = false;
    for (size_t i = 0; i < buffer.size(); i += 4) {
        if (buffer[i] != 0 || buffer[i + 1] != 0 ||
            buffer[i + 2] != 0 || buffer[i + 3] != 0) {
            has_content = true;
            break;
        }
    }
    EXPECT_TRUE(has_content);
}

TEST(OverlayManagerTest, RenderInvisibleOverlay) {
    OverlayManager manager;

    OverlayId id = manager.add_bbox(10, 10, 50, 30);
    manager.set_visible(id, false);

    std::vector<uint8_t> buffer(320 * 200 * 4, 0);
    manager.render(Span<uint8_t>(buffer.data(), buffer.size()), 320, 200);

    // Buffer should remain all zeros (invisible overlay)
    bool all_zero = true;
    for (size_t i = 0; i < buffer.size(); ++i) {
        if (buffer[i] != 0) {
            all_zero = false;
            break;
        }
    }
    EXPECT_TRUE(all_zero);
}

// ─────────────────────────────────────────────────────────────────────────────
// Drawing Primitives Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(DrawingPrimitivesTest, SetPixelAlpha) {
    std::vector<uint8_t> buffer(100 * 100 * 4, 0);
    Span<uint8_t> buf_span(buffer.data(), buffer.size());

    set_pixel_alpha(buf_span, 100, 100, 50, 50, RgbaColor{255, 128, 64, 255});

    size_t offset = (50 * 100 + 50) * 4;
    EXPECT_EQ(buffer[offset + 0], 255);  // R
    EXPECT_EQ(buffer[offset + 1], 128);  // G
    EXPECT_EQ(buffer[offset + 2], 64);   // B
    EXPECT_EQ(buffer[offset + 3], 255);  // A
}

TEST(DrawingPrimitivesTest, SetPixelOutOfBounds) {
    std::vector<uint8_t> buffer(100 * 100 * 4, 0);
    Span<uint8_t> buf_span(buffer.data(), buffer.size());

    // These should not crash or write anywhere
    set_pixel_alpha(buf_span, 100, 100, -1, 50, RgbaColor{255, 0, 0, 255});
    set_pixel_alpha(buf_span, 100, 100, 100, 50, RgbaColor{255, 0, 0, 255});
    set_pixel_alpha(buf_span, 100, 100, 50, -1, RgbaColor{255, 0, 0, 255});
    set_pixel_alpha(buf_span, 100, 100, 50, 100, RgbaColor{255, 0, 0, 255});

    // Buffer should still be all zeros
    bool all_zero = true;
    for (size_t i = 0; i < buffer.size(); ++i) {
        if (buffer[i] != 0) {
            all_zero = false;
            break;
        }
    }
    EXPECT_TRUE(all_zero);
}

TEST(DrawingPrimitivesTest, DrawHLine) {
    std::vector<uint8_t> buffer(100 * 100 * 4, 0);
    Span<uint8_t> buf_span(buffer.data(), buffer.size());

    draw_hline(buf_span, 100, 100, 10, 30, 50, RgbaColor{255, 0, 0, 255});

    // Check pixels on the line
    for (int x = 10; x < 30; ++x) {
        size_t offset = (50 * 100 + x) * 4;
        EXPECT_EQ(buffer[offset + 0], 255) << "R at x=" << x;
        EXPECT_EQ(buffer[offset + 3], 255) << "A at x=" << x;
    }

    // Check pixels before and after line
    size_t before = (50 * 100 + 9) * 4;
    size_t after = (50 * 100 + 30) * 4;
    EXPECT_EQ(buffer[before], 0);
    EXPECT_EQ(buffer[after], 0);
}

TEST(DrawingPrimitivesTest, DrawVLine) {
    std::vector<uint8_t> buffer(100 * 100 * 4, 0);
    Span<uint8_t> buf_span(buffer.data(), buffer.size());

    draw_vline(buf_span, 100, 100, 50, 10, 30, RgbaColor{0, 255, 0, 255});

    // Check pixels on the line
    for (int y = 10; y < 30; ++y) {
        size_t offset = (y * 100 + 50) * 4;
        EXPECT_EQ(buffer[offset + 1], 255) << "G at y=" << y;
        EXPECT_EQ(buffer[offset + 3], 255) << "A at y=" << y;
    }
}

TEST(DrawingPrimitivesTest, DrawRect) {
    std::vector<uint8_t> buffer(100 * 100 * 4, 0);
    Span<uint8_t> buf_span(buffer.data(), buffer.size());

    draw_rect(buf_span, 100, 100, 20, 20, 30, 20, RgbaColor{0, 0, 255, 255}, 1);

    // Check top edge
    for (int x = 20; x < 50; ++x) {
        size_t offset = (20 * 100 + x) * 4;
        EXPECT_EQ(buffer[offset + 2], 255) << "B at top x=" << x;
    }

    // Check bottom edge
    for (int x = 20; x < 50; ++x) {
        size_t offset = (39 * 100 + x) * 4;
        EXPECT_EQ(buffer[offset + 2], 255) << "B at bottom x=" << x;
    }

    // Check left edge
    for (int y = 20; y < 40; ++y) {
        size_t offset = (y * 100 + 20) * 4;
        EXPECT_EQ(buffer[offset + 2], 255) << "B at left y=" << y;
    }
}

TEST(DrawingPrimitivesTest, FillRect) {
    std::vector<uint8_t> buffer(100 * 100 * 4, 0);
    Span<uint8_t> buf_span(buffer.data(), buffer.size());

    // Use fully opaque color to get exact values (no alpha blending)
    fill_rect(buf_span, 100, 100, 20, 20, 10, 10, RgbaColor{255, 128, 64, 255});

    // Check all pixels in the rectangle
    for (int y = 20; y < 30; ++y) {
        for (int x = 20; x < 30; ++x) {
            size_t offset = (y * 100 + x) * 4;
            EXPECT_EQ(buffer[offset + 0], 255) << "R at (" << x << "," << y << ")";
            EXPECT_EQ(buffer[offset + 1], 128) << "G at (" << x << "," << y << ")";
            EXPECT_EQ(buffer[offset + 2], 64) << "B at (" << x << "," << y << ")";
            EXPECT_EQ(buffer[offset + 3], 255) << "A at (" << x << "," << y << ")";
        }
    }
}

TEST(DrawingPrimitivesTest, DrawLine) {
    std::vector<uint8_t> buffer(100 * 100 * 4, 0);
    Span<uint8_t> buf_span(buffer.data(), buffer.size());

    // Diagonal line from (10, 10) to (20, 20)
    draw_line(buf_span, 100, 100, 10, 10, 20, 20, RgbaColor{255, 255, 255, 255}, 1);

    // Check that start and end points are set
    size_t start_offset = (10 * 100 + 10) * 4;
    size_t end_offset = (20 * 100 + 20) * 4;

    EXPECT_EQ(buffer[start_offset + 0], 255);  // R
    EXPECT_EQ(buffer[end_offset + 0], 255);    // R
}

TEST(DrawingPrimitivesTest, DrawCircle) {
    std::vector<uint8_t> buffer(100 * 100 * 4, 0);
    Span<uint8_t> buf_span(buffer.data(), buffer.size());

    draw_circle(buf_span, 100, 100, 50, 50, 10, RgbaColor{255, 0, 255, 255}, 1);

    // Check that some pixels on the circle are set
    // Top of circle (center_y - radius)
    size_t top_offset = (40 * 100 + 50) * 4;
    EXPECT_EQ(buffer[top_offset + 0], 255);  // R

    // Bottom of circle (center_y + radius)
    size_t bottom_offset = (60 * 100 + 50) * 4;
    EXPECT_EQ(buffer[bottom_offset + 0], 255);  // R
}

TEST(DrawingPrimitivesTest, FillCircle) {
    std::vector<uint8_t> buffer(100 * 100 * 4, 0);
    Span<uint8_t> buf_span(buffer.data(), buffer.size());

    // Use fully opaque color to get exact values (no alpha blending)
    fill_circle(buf_span, 100, 100, 50, 50, 5, RgbaColor{0, 255, 0, 255});

    // Check center pixel
    size_t center_offset = (50 * 100 + 50) * 4;
    EXPECT_EQ(buffer[center_offset + 1], 255);  // G
    EXPECT_EQ(buffer[center_offset + 3], 255);  // A
}

// ─────────────────────────────────────────────────────────────────────────────
// Composite Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(CompositeTest, CompositeOntoRGB24) {
    // Create overlay buffer with a red pixel
    std::vector<uint8_t> overlay(10 * 10 * 4, 0);
    size_t center = (5 * 10 + 5) * 4;
    overlay[center + 0] = 255;  // R
    overlay[center + 1] = 0;    // G
    overlay[center + 2] = 0;    // B
    overlay[center + 3] = 255;  // A (fully opaque)

    // Create screenshot buffer (RGB24)
    std::vector<uint8_t> output(10 * 10 * 3, 128);  // Gray background

    OverlayManager::composite(
        Span<const uint8_t>(overlay.data(), overlay.size()),
        Span<uint8_t>(output.data(), output.size()),
        10, 10, PixelFormat::RGB24);

    // Check that red pixel was composited
    size_t out_offset = (5 * 10 + 5) * 3;
    EXPECT_EQ(output[out_offset + 0], 255);  // R
    EXPECT_EQ(output[out_offset + 1], 0);    // G
    EXPECT_EQ(output[out_offset + 2], 0);    // B
}

TEST(CompositeTest, CompositeWithAlphaBlending) {
    // Create overlay buffer with semi-transparent red pixel
    std::vector<uint8_t> overlay(10 * 10 * 4, 0);
    size_t center = (5 * 10 + 5) * 4;
    overlay[center + 0] = 255;  // R
    overlay[center + 1] = 0;    // G
    overlay[center + 2] = 0;    // B
    overlay[center + 3] = 128;  // A (50% transparent)

    // Create screenshot buffer (RGB24) with white background
    std::vector<uint8_t> output(10 * 10 * 3, 255);

    OverlayManager::composite(
        Span<const uint8_t>(overlay.data(), overlay.size()),
        Span<uint8_t>(output.data(), output.size()),
        10, 10, PixelFormat::RGB24);

    // Check that pixel was blended (should be pinkish)
    size_t out_offset = (5 * 10 + 5) * 3;
    // Blended: 255 * 0.5 + 255 * 0.5 = ~255 for R
    // Blended: 0 * 0.5 + 255 * 0.5 = ~127 for G/B
    EXPECT_GE(output[out_offset + 0], 250);   // R (close to 255)
    EXPECT_GE(output[out_offset + 1], 120);   // G (blended)
    EXPECT_LE(output[out_offset + 1], 135);
}

TEST(CompositeTest, CompositeOntoRGBA32) {
    std::vector<uint8_t> overlay(10 * 10 * 4, 0);
    size_t center = (5 * 10 + 5) * 4;
    overlay[center + 0] = 0;    // R
    overlay[center + 1] = 255;  // G
    overlay[center + 2] = 0;    // B
    overlay[center + 3] = 255;  // A

    std::vector<uint8_t> output(10 * 10 * 4, 100);

    OverlayManager::composite(
        Span<const uint8_t>(overlay.data(), overlay.size()),
        Span<uint8_t>(output.data(), output.size()),
        10, 10, PixelFormat::RGBA32);

    size_t out_offset = (5 * 10 + 5) * 4;
    EXPECT_EQ(output[out_offset + 0], 0);    // R
    EXPECT_EQ(output[out_offset + 1], 255);  // G
    EXPECT_EQ(output[out_offset + 2], 0);    // B
}
