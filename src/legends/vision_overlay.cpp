/**
 * @file vision_overlay.cpp
 * @brief Implementation of overlay system for visual annotations.
 */

// GCC 15 has false positives with std::variant containing std::string
#if defined(__GNUC__) && __GNUC__ >= 15
#pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
#endif

#include "legends/vision_overlay.h"
#include <algorithm>
#include <cmath>

namespace legends::vision {

// ─────────────────────────────────────────────────────────────────────────────
// LineOverlay Implementation
// ─────────────────────────────────────────────────────────────────────────────

float LineOverlay::length() const noexcept {
    float dx = static_cast<float>(x2 - x);
    float dy = static_cast<float>(y2 - y);
    return std::sqrt(dx * dx + dy * dy);
}

// ─────────────────────────────────────────────────────────────────────────────
// OverlayManager Implementation
// ─────────────────────────────────────────────────────────────────────────────

OverlayId OverlayManager::add_bbox(
    int16_t x, int16_t y,
    int16_t width, int16_t height,
    RgbaColor color,
    uint8_t thickness
) {
    BoundingBox box;
    box.x = x;
    box.y = y;
    box.width = width;
    box.height = height;
    box.color = color;
    box.thickness = thickness;
    return add(box);
}

OverlayId OverlayManager::add_label(
    int16_t x, int16_t y,
    const std::string& text,
    RgbaColor color,
    uint8_t font_size
) {
    TextLabel label;
    label.x = x;
    label.y = y;
    label.text = text;
    label.color = color;
    label.font_size = font_size;
    return add(label);
}

OverlayId OverlayManager::add_highlight(
    int16_t x, int16_t y,
    int16_t width, int16_t height,
    RgbaColor color
) {
    HighlightRegion hl;
    hl.x = x;
    hl.y = y;
    hl.width = width;
    hl.height = height;
    hl.color = color;
    return add(hl);
}

bool OverlayManager::update(OverlayId id, const Overlay& overlay) {
    for (auto& existing : overlays_) {
        if (get_overlay_id(existing) == id) {
            existing = overlay;
            // Preserve the ID
            std::visit([id](auto& o) { o.id = id; }, existing);
            sort_by_z_order();
            return true;
        }
    }
    return false;
}

bool OverlayManager::remove(OverlayId id) {
    auto it = std::remove_if(overlays_.begin(), overlays_.end(),
        [id](const Overlay& o) { return get_overlay_id(o) == id; });

    if (it != overlays_.end()) {
        overlays_.erase(it, overlays_.end());
        return true;
    }
    return false;
}

void OverlayManager::clear() noexcept {
    overlays_.clear();
}

std::optional<Overlay> OverlayManager::get(OverlayId id) const {
    for (const auto& overlay : overlays_) {
        if (get_overlay_id(overlay) == id) {
            return overlay;
        }
    }
    return std::nullopt;
}

bool OverlayManager::set_visible(OverlayId id, bool visible) {
    for (auto& overlay : overlays_) {
        if (get_overlay_id(overlay) == id) {
            std::visit([visible](auto& o) { o.visible = visible; }, overlay);
            return true;
        }
    }
    return false;
}

bool OverlayManager::set_z_order(OverlayId id, uint8_t z_order) {
    for (auto& overlay : overlays_) {
        if (get_overlay_id(overlay) == id) {
            std::visit([z_order](auto& o) { o.z_order = z_order; }, overlay);
            sort_by_z_order();
            return true;
        }
    }
    return false;
}

void OverlayManager::sort_by_z_order() {
    std::stable_sort(overlays_.begin(), overlays_.end(),
        [](const Overlay& a, const Overlay& b) {
            return get_overlay_z_order(a) < get_overlay_z_order(b);
        });
}

void OverlayManager::render(
    Span<uint8_t> buffer,
    uint16_t width,
    uint16_t height
) const {
    // Clear buffer to transparent
    std::fill(buffer.begin(), buffer.end(), static_cast<uint8_t>(0));

    // Render each overlay in z-order
    for (const auto& overlay : overlays_) {
        if (!is_overlay_visible(overlay)) {
            continue;
        }

        std::visit([&](const auto& o) {
            using T = std::decay_t<decltype(o)>;
            if constexpr (std::is_same_v<T, BoundingBox>) {
                render_bbox(buffer, width, height, o);
            } else if constexpr (std::is_same_v<T, TextLabel>) {
                render_label(buffer, width, height, o);
            } else if constexpr (std::is_same_v<T, HighlightRegion>) {
                render_highlight(buffer, width, height, o);
            } else if constexpr (std::is_same_v<T, LineOverlay>) {
                render_line(buffer, width, height, o);
            } else if constexpr (std::is_same_v<T, CircleOverlay>) {
                render_circle(buffer, width, height, o);
            } else if constexpr (std::is_same_v<T, Crosshair>) {
                render_crosshair(buffer, width, height, o);
            }
        }, overlay);
    }
}

void OverlayManager::render_bbox(
    Span<uint8_t> buf, uint16_t w, uint16_t h,
    const BoundingBox& box
) const {
    if (box.filled) {
        // Fill the interior
        RgbaColor fill_color = box.color;
        fill_color.a = box.fill_alpha;
        fill_rect(buf, w, h, box.x, box.y, box.width, box.height, fill_color);
    }

    // Draw border
    draw_rect(buf, w, h, box.x, box.y, box.width, box.height, box.color, box.thickness);
}

void OverlayManager::render_label(
    Span<uint8_t> buf, uint16_t w, uint16_t h,
    const TextLabel& label
) const {
    int16_t label_w = label.calculated_width();
    int16_t label_h = label.calculated_height();

    // Draw background
    if (label.has_background) {
        fill_rect(buf, w, h, label.x, label.y, label_w, label_h, label.background);
    }

    // Draw text (simplified - just draws colored rectangles for now)
    // A full implementation would need font rendering
    int16_t char_x = label.x + label.padding;
    int16_t char_y = label.y + label.padding;

    for (size_t i = 0; i < label.text.length(); ++i) {
        // Simple placeholder: draw a small rectangle for each character
        fill_rect(buf, w, h,
            char_x, char_y,
            static_cast<int16_t>(label.font_size - 2),
            static_cast<int16_t>(label.font_size - 2),
            label.color);
        char_x += label.font_size;
    }
}

void OverlayManager::render_highlight(
    Span<uint8_t> buf, uint16_t w, uint16_t h,
    const HighlightRegion& hl
) const {
    fill_rect(buf, w, h, hl.x, hl.y, hl.width, hl.height, hl.color);
}

void OverlayManager::render_line(
    Span<uint8_t> buf, uint16_t w, uint16_t h,
    const LineOverlay& line
) const {
    draw_line(buf, w, h, line.x, line.y, line.x2, line.y2, line.color, line.thickness);
}

void OverlayManager::render_circle(
    Span<uint8_t> buf, uint16_t w, uint16_t h,
    const CircleOverlay& circle
) const {
    if (circle.filled) {
        fill_circle(buf, w, h, circle.x, circle.y, circle.radius_x, circle.color);
    } else {
        draw_circle(buf, w, h, circle.x, circle.y, circle.radius_x, circle.color, circle.thickness);
    }
}

void OverlayManager::render_crosshair(
    Span<uint8_t> buf, uint16_t w, uint16_t h,
    const Crosshair& ch
) const {
    // Horizontal line
    draw_hline(buf, w, h,
        static_cast<int16_t>(ch.x - ch.size),
        static_cast<int16_t>(ch.x + ch.size),
        ch.y, ch.color);

    // Vertical line
    draw_vline(buf, w, h, ch.x,
        static_cast<int16_t>(ch.y - ch.size),
        static_cast<int16_t>(ch.y + ch.size),
        ch.color);

    // Optional circle
    if (ch.show_circle) {
        draw_circle(buf, w, h, ch.x, ch.y, ch.circle_radius, ch.color, ch.thickness);
    }
}

void OverlayManager::composite(
    Span<const uint8_t> overlay_buffer,
    Span<uint8_t> output_buffer,
    uint16_t width,
    uint16_t height,
    PixelFormat output_format
) {
    size_t out_bpp = bytes_per_pixel(output_format);
    (void)out_bpp;  // Reserved for future format-aware compositing
    size_t num_pixels = static_cast<size_t>(width) * height;

    for (size_t i = 0; i < num_pixels; ++i) {
        // Get overlay pixel (RGBA)
        uint8_t ov_r = overlay_buffer[i * 4 + 0];
        uint8_t ov_g = overlay_buffer[i * 4 + 1];
        uint8_t ov_b = overlay_buffer[i * 4 + 2];
        uint8_t ov_a = overlay_buffer[i * 4 + 3];

        if (ov_a == 0) {
            continue;  // Fully transparent, skip
        }

        // Get output pixel
        uint8_t out_r, out_g, out_b;
        switch (output_format) {
            case PixelFormat::RGB24:
                out_r = output_buffer[i * 3 + 0];
                out_g = output_buffer[i * 3 + 1];
                out_b = output_buffer[i * 3 + 2];
                break;
            case PixelFormat::RGBA32:
                out_r = output_buffer[i * 4 + 0];
                out_g = output_buffer[i * 4 + 1];
                out_b = output_buffer[i * 4 + 2];
                break;
            case PixelFormat::BGR24:
                out_b = output_buffer[i * 3 + 0];
                out_g = output_buffer[i * 3 + 1];
                out_r = output_buffer[i * 3 + 2];
                break;
            case PixelFormat::BGRA32:
                out_b = output_buffer[i * 4 + 0];
                out_g = output_buffer[i * 4 + 1];
                out_r = output_buffer[i * 4 + 2];
                break;
            default:
                continue;  // Unsupported format
        }

        // Alpha blend
        float alpha = ov_a / 255.0f;
        float inv_alpha = 1.0f - alpha;

        uint8_t blend_r = static_cast<uint8_t>(ov_r * alpha + out_r * inv_alpha);
        uint8_t blend_g = static_cast<uint8_t>(ov_g * alpha + out_g * inv_alpha);
        uint8_t blend_b = static_cast<uint8_t>(ov_b * alpha + out_b * inv_alpha);

        // Write back
        switch (output_format) {
            case PixelFormat::RGB24:
                output_buffer[i * 3 + 0] = blend_r;
                output_buffer[i * 3 + 1] = blend_g;
                output_buffer[i * 3 + 2] = blend_b;
                break;
            case PixelFormat::RGBA32:
                output_buffer[i * 4 + 0] = blend_r;
                output_buffer[i * 4 + 1] = blend_g;
                output_buffer[i * 4 + 2] = blend_b;
                break;
            case PixelFormat::BGR24:
                output_buffer[i * 3 + 0] = blend_b;
                output_buffer[i * 3 + 1] = blend_g;
                output_buffer[i * 3 + 2] = blend_r;
                break;
            case PixelFormat::BGRA32:
                output_buffer[i * 4 + 0] = blend_b;
                output_buffer[i * 4 + 1] = blend_g;
                output_buffer[i * 4 + 2] = blend_r;
                break;
            default:
                break;
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Drawing Primitives
// ─────────────────────────────────────────────────────────────────────────────

void set_pixel_alpha(
    Span<uint8_t> buffer,
    uint16_t width, uint16_t height,
    int16_t x, int16_t y,
    RgbaColor color
) noexcept {
    if (x < 0 || y < 0 || x >= width || y >= height) {
        return;
    }

    size_t offset = (static_cast<size_t>(y) * width + x) * 4;
    if (offset + 3 >= buffer.size()) {
        return;
    }

    if (color.a == 255) {
        // Fully opaque, just write
        buffer[offset + 0] = color.r;
        buffer[offset + 1] = color.g;
        buffer[offset + 2] = color.b;
        buffer[offset + 3] = color.a;
    } else if (color.a > 0) {
        // Alpha blend with existing
        float alpha = color.a / 255.0f;
        float inv_alpha = 1.0f - alpha;
        float existing_alpha = buffer[offset + 3] / 255.0f;

        buffer[offset + 0] = static_cast<uint8_t>(color.r * alpha + buffer[offset + 0] * inv_alpha);
        buffer[offset + 1] = static_cast<uint8_t>(color.g * alpha + buffer[offset + 1] * inv_alpha);
        buffer[offset + 2] = static_cast<uint8_t>(color.b * alpha + buffer[offset + 2] * inv_alpha);
        buffer[offset + 3] = static_cast<uint8_t>((alpha + existing_alpha * inv_alpha) * 255);
    }
}

void draw_hline(
    Span<uint8_t> buffer,
    uint16_t width, uint16_t height,
    int16_t x1, int16_t x2, int16_t y,
    RgbaColor color
) noexcept {
    if (x1 > x2) std::swap(x1, x2);

    for (int16_t x = x1; x < x2; ++x) {
        set_pixel_alpha(buffer, width, height, x, y, color);
    }
}

void draw_vline(
    Span<uint8_t> buffer,
    uint16_t width, uint16_t height,
    int16_t x, int16_t y1, int16_t y2,
    RgbaColor color
) noexcept {
    if (y1 > y2) std::swap(y1, y2);

    for (int16_t y = y1; y < y2; ++y) {
        set_pixel_alpha(buffer, width, height, x, y, color);
    }
}

void draw_rect(
    Span<uint8_t> buffer,
    uint16_t width, uint16_t height,
    int16_t x, int16_t y,
    int16_t w, int16_t h,
    RgbaColor color,
    uint8_t thickness
) noexcept {
    for (uint8_t t = 0; t < thickness; ++t) {
        // Top edge
        draw_hline(buffer, width, height,
            x, static_cast<int16_t>(x + w),
            static_cast<int16_t>(y + t), color);

        // Bottom edge
        draw_hline(buffer, width, height,
            x, static_cast<int16_t>(x + w),
            static_cast<int16_t>(y + h - 1 - t), color);

        // Left edge
        draw_vline(buffer, width, height,
            static_cast<int16_t>(x + t), y,
            static_cast<int16_t>(y + h), color);

        // Right edge
        draw_vline(buffer, width, height,
            static_cast<int16_t>(x + w - 1 - t), y,
            static_cast<int16_t>(y + h), color);
    }
}

void fill_rect(
    Span<uint8_t> buffer,
    uint16_t width, uint16_t height,
    int16_t x, int16_t y,
    int16_t w, int16_t h,
    RgbaColor color
) noexcept {
    for (int16_t dy = 0; dy < h; ++dy) {
        for (int16_t dx = 0; dx < w; ++dx) {
            set_pixel_alpha(buffer, width, height,
                static_cast<int16_t>(x + dx),
                static_cast<int16_t>(y + dy),
                color);
        }
    }
}

void draw_line(
    Span<uint8_t> buffer,
    uint16_t width, uint16_t height,
    int16_t x1, int16_t y1,
    int16_t x2, int16_t y2,
    RgbaColor color,
    uint8_t thickness
) noexcept {
    // Bresenham's line algorithm
    int dx = std::abs(x2 - x1);
    int dy = std::abs(y2 - y1);
    int sx = x1 < x2 ? 1 : -1;
    int sy = y1 < y2 ? 1 : -1;
    int err = dx - dy;

    while (true) {
        // Draw thick point
        if (thickness == 1) {
            set_pixel_alpha(buffer, width, height, x1, y1, color);
        } else {
            int16_t half = thickness / 2;
            fill_rect(buffer, width, height,
                static_cast<int16_t>(x1 - half),
                static_cast<int16_t>(y1 - half),
                thickness, thickness, color);
        }

        if (x1 == x2 && y1 == y2) break;

        int e2 = 2 * err;
        if (e2 > -dy) {
            err -= dy;
            x1 = static_cast<int16_t>(x1 + sx);
        }
        if (e2 < dx) {
            err += dx;
            y1 = static_cast<int16_t>(y1 + sy);
        }
    }
}

void draw_circle(
    Span<uint8_t> buffer,
    uint16_t width, uint16_t height,
    int16_t cx, int16_t cy,
    int16_t radius,
    RgbaColor color,
    uint8_t thickness
) noexcept {
    // Midpoint circle algorithm
    int16_t x = radius;
    int16_t y = 0;
    int16_t err = 0;

    while (x >= y) {
        // Draw 8 octants
        set_pixel_alpha(buffer, width, height, cx + x, cy + y, color);
        set_pixel_alpha(buffer, width, height, cx + y, cy + x, color);
        set_pixel_alpha(buffer, width, height, cx - y, cy + x, color);
        set_pixel_alpha(buffer, width, height, cx - x, cy + y, color);
        set_pixel_alpha(buffer, width, height, cx - x, cy - y, color);
        set_pixel_alpha(buffer, width, height, cx - y, cy - x, color);
        set_pixel_alpha(buffer, width, height, cx + y, cy - x, color);
        set_pixel_alpha(buffer, width, height, cx + x, cy - y, color);

        if (err <= 0) {
            ++y;
            err += 2 * y + 1;
        }
        if (err > 0) {
            --x;
            err -= 2 * x + 1;
        }
    }

    // For thickness > 1, draw additional circles
    for (uint8_t t = 1; t < thickness; ++t) {
        draw_circle(buffer, width, height, cx, cy,
            static_cast<int16_t>(radius - t), color, 1);
    }
}

void fill_circle(
    Span<uint8_t> buffer,
    uint16_t width, uint16_t height,
    int16_t cx, int16_t cy,
    int16_t radius,
    RgbaColor color
) noexcept {
    for (int16_t y = -radius; y <= radius; ++y) {
        for (int16_t x = -radius; x <= radius; ++x) {
            if (x * x + y * y <= radius * radius) {
                set_pixel_alpha(buffer, width, height,
                    static_cast<int16_t>(cx + x),
                    static_cast<int16_t>(cy + y),
                    color);
            }
        }
    }
}

}  // namespace legends::vision
