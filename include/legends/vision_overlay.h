/**
 * @file vision_overlay.h
 * @brief Overlay system for visual annotations.
 *
 * Provides a non-destructive overlay system for drawing bounding boxes,
 * labels, and other annotations on screenshots for computer vision applications.
 */

#pragma once

#include "vision_framebuffer.h"
#include "vision_capture.h"

#include <cstdint>
#include <optional>
#include <string>
#include <variant>
#include <vector>

namespace legends::vision {

// ─────────────────────────────────────────────────────────────────────────────
// Overlay Identifier
// ─────────────────────────────────────────────────────────────────────────────

/// Overlay identifier type
using OverlayId = uint32_t;

/// Invalid overlay ID constant
constexpr OverlayId INVALID_OVERLAY = 0;

// ─────────────────────────────────────────────────────────────────────────────
// Base Overlay Properties
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Base overlay properties shared by all overlay types.
 */
struct OverlayBase {
    OverlayId id{INVALID_OVERLAY};  ///< Unique identifier
    int16_t x{0};                   ///< X position
    int16_t y{0};                   ///< Y position
    uint8_t z_order{0};             ///< Render order (higher = on top)
    bool visible{true};             ///< Whether overlay is visible
};

// ─────────────────────────────────────────────────────────────────────────────
// Overlay Types
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Bounding box overlay for object detection.
 */
struct BoundingBox : OverlayBase {
    int16_t width{0};                         ///< Box width
    int16_t height{0};                        ///< Box height
    RgbaColor color{255, 0, 0, 255};          ///< Border color (default: red)
    uint8_t thickness{2};                     ///< Border thickness in pixels
    bool filled{false};                       ///< Fill interior
    uint8_t fill_alpha{64};                   ///< Alpha for filled boxes

    /**
     * @brief Get right edge X coordinate.
     */
    [[nodiscard]] int16_t right() const noexcept { return x + width; }

    /**
     * @brief Get bottom edge Y coordinate.
     */
    [[nodiscard]] int16_t bottom() const noexcept { return y + height; }

    /**
     * @brief Get area in pixels.
     */
    [[nodiscard]] int32_t area() const noexcept {
        return static_cast<int32_t>(width) * height;
    }

    /**
     * @brief Check if point is inside box.
     */
    [[nodiscard]] bool contains(int16_t px, int16_t py) const noexcept {
        return px >= x && px < x + width && py >= y && py < y + height;
    }
};

/**
 * @brief Text label overlay.
 */
struct TextLabel : OverlayBase {
    std::string text;                              ///< Label text
    RgbaColor color{255, 255, 255, 255};           ///< Text color (default: white)
    RgbaColor background{0, 0, 0, 180};            ///< Background color (semi-transparent black)
    uint8_t font_size{8};                          ///< Character height in pixels
    bool has_background{true};                     ///< Draw background rectangle
    int8_t padding{2};                             ///< Padding around text

    /**
     * @brief Calculate label width in pixels.
     */
    [[nodiscard]] int16_t calculated_width() const noexcept {
        return static_cast<int16_t>(text.length() * font_size + padding * 2);
    }

    /**
     * @brief Calculate label height in pixels.
     */
    [[nodiscard]] int16_t calculated_height() const noexcept {
        return font_size + padding * 2;
    }
};

/**
 * @brief Highlight region overlay (semi-transparent rectangle).
 */
struct HighlightRegion : OverlayBase {
    int16_t width{0};                              ///< Region width
    int16_t height{0};                             ///< Region height
    RgbaColor color{255, 255, 0, 128};             ///< Highlight color (default: semi-transparent yellow)
};

/**
 * @brief Line overlay for connecting elements.
 */
struct LineOverlay : OverlayBase {
    int16_t x2{0};                                 ///< End X coordinate
    int16_t y2{0};                                 ///< End Y coordinate
    RgbaColor color{0, 255, 0, 255};               ///< Line color (default: green)
    uint8_t thickness{1};                          ///< Line thickness

    /**
     * @brief Get line length.
     */
    [[nodiscard]] float length() const noexcept;
};

/**
 * @brief Circle/ellipse overlay.
 */
struct CircleOverlay : OverlayBase {
    int16_t radius_x{0};                           ///< Horizontal radius
    int16_t radius_y{0};                           ///< Vertical radius
    RgbaColor color{255, 0, 255, 255};             ///< Circle color (default: magenta)
    uint8_t thickness{2};                          ///< Border thickness
    bool filled{false};                            ///< Fill interior

    /**
     * @brief Check if this is a circle (equal radii).
     */
    [[nodiscard]] bool is_circle() const noexcept {
        return radius_x == radius_y;
    }

    /**
     * @brief Get radius for circular shapes.
     */
    [[nodiscard]] int16_t radius() const noexcept {
        return radius_x;
    }
};

/**
 * @brief Crosshair marker overlay.
 */
struct Crosshair : OverlayBase {
    int16_t size{10};                              ///< Size of crosshair arms
    RgbaColor color{0, 255, 255, 255};             ///< Crosshair color (default: cyan)
    uint8_t thickness{1};                          ///< Line thickness
    bool show_circle{false};                       ///< Show circle around center
    int16_t circle_radius{5};                      ///< Circle radius if shown
};

// ─────────────────────────────────────────────────────────────────────────────
// Overlay Variant
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Overlay variant type containing any overlay type.
 */
using Overlay = std::variant<
    BoundingBox,
    TextLabel,
    HighlightRegion,
    LineOverlay,
    CircleOverlay,
    Crosshair
>;

/**
 * @brief Get overlay ID from variant.
 */
[[nodiscard]] inline OverlayId get_overlay_id(const Overlay& overlay) noexcept {
    return std::visit([](const auto& o) { return o.id; }, overlay);
}

/**
 * @brief Get overlay visibility from variant.
 */
[[nodiscard]] inline bool is_overlay_visible(const Overlay& overlay) noexcept {
    return std::visit([](const auto& o) { return o.visible; }, overlay);
}

/**
 * @brief Get overlay z-order from variant.
 */
[[nodiscard]] inline uint8_t get_overlay_z_order(const Overlay& overlay) noexcept {
    return std::visit([](const auto& o) { return o.z_order; }, overlay);
}

// ─────────────────────────────────────────────────────────────────────────────
// Overlay Manager
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Manages a collection of overlays for rendering.
 *
 * Provides overlay creation, modification, removal, and rendering to
 * an RGBA buffer that can be composited onto screenshots.
 *
 * Example:
 * @code
 *   OverlayManager manager;
 *
 *   // Add bounding box for detected object
 *   BoundingBox box;
 *   box.x = 100;
 *   box.y = 50;
 *   box.width = 80;
 *   box.height = 60;
 *   box.color = {255, 0, 0, 255};  // Red
 *   OverlayId box_id = manager.add(box);
 *
 *   // Add label above box
 *   TextLabel label;
 *   label.x = 100;
 *   label.y = 40;
 *   label.text = "Enemy";
 *   manager.add(label);
 *
 *   // Render overlays to buffer
 *   std::vector<uint8_t> overlay_buffer(320 * 200 * 4);
 *   manager.render(overlay_buffer, 320, 200);
 * @endcode
 */
class OverlayManager {
public:
    OverlayManager() = default;

    /**
     * @brief Add an overlay.
     *
     * @param overlay Overlay to add
     * @return Assigned overlay ID
     */
    template<typename T>
    OverlayId add(T overlay) {
        overlay.id = next_id_++;
        overlays_.push_back(std::move(overlay));
        sort_by_z_order();
        return get_overlay_id(overlays_.back());
    }

    /**
     * @brief Add a bounding box with simplified parameters.
     */
    OverlayId add_bbox(
        int16_t x, int16_t y,
        int16_t width, int16_t height,
        RgbaColor color = {255, 0, 0, 255},
        uint8_t thickness = 2
    );

    /**
     * @brief Add a text label with simplified parameters.
     */
    OverlayId add_label(
        int16_t x, int16_t y,
        const std::string& text,
        RgbaColor color = {255, 255, 255, 255},
        uint8_t font_size = 8
    );

    /**
     * @brief Add a highlight region with simplified parameters.
     */
    OverlayId add_highlight(
        int16_t x, int16_t y,
        int16_t width, int16_t height,
        RgbaColor color = {255, 255, 0, 128}
    );

    /**
     * @brief Update an existing overlay.
     *
     * @param id Overlay ID
     * @param overlay New overlay data
     * @return True if updated, false if not found
     */
    bool update(OverlayId id, const Overlay& overlay);

    /**
     * @brief Remove an overlay by ID.
     *
     * @param id Overlay ID
     * @return True if removed, false if not found
     */
    bool remove(OverlayId id);

    /**
     * @brief Remove all overlays.
     */
    void clear() noexcept;

    /**
     * @brief Get overlay by ID.
     *
     * @param id Overlay ID
     * @return Overlay if found, nullopt otherwise
     */
    [[nodiscard]] std::optional<Overlay> get(OverlayId id) const;

    /**
     * @brief Get all overlays (sorted by z-order).
     */
    [[nodiscard]] const std::vector<Overlay>& get_all() const noexcept {
        return overlays_;
    }

    /**
     * @brief Get number of overlays.
     */
    [[nodiscard]] size_t count() const noexcept {
        return overlays_.size();
    }

    /**
     * @brief Check if any overlays exist.
     */
    [[nodiscard]] bool empty() const noexcept {
        return overlays_.empty();
    }

    /**
     * @brief Set visibility for an overlay.
     */
    bool set_visible(OverlayId id, bool visible);

    /**
     * @brief Set z-order for an overlay.
     */
    bool set_z_order(OverlayId id, uint8_t z_order);

    /**
     * @brief Render all overlays to an RGBA buffer.
     *
     * @param buffer Output buffer (must be width * height * 4 bytes)
     * @param width Buffer width
     * @param height Buffer height
     */
    void render(
        Span<uint8_t> buffer,
        uint16_t width,
        uint16_t height
    ) const;

    /**
     * @brief Composite overlay buffer onto a screenshot.
     *
     * @param overlay_buffer Rendered overlay buffer (RGBA32)
     * @param output_buffer Screenshot buffer to composite onto
     * @param width Image width
     * @param height Image height
     * @param output_format Format of output buffer
     */
    static void composite(
        Span<const uint8_t> overlay_buffer,
        Span<uint8_t> output_buffer,
        uint16_t width,
        uint16_t height,
        PixelFormat output_format
    );

private:
    void sort_by_z_order();

    // Rendering helpers
    void render_bbox(Span<uint8_t> buf, uint16_t w, uint16_t h, const BoundingBox& box) const;
    void render_label(Span<uint8_t> buf, uint16_t w, uint16_t h, const TextLabel& label) const;
    void render_highlight(Span<uint8_t> buf, uint16_t w, uint16_t h, const HighlightRegion& hl) const;
    void render_line(Span<uint8_t> buf, uint16_t w, uint16_t h, const LineOverlay& line) const;
    void render_circle(Span<uint8_t> buf, uint16_t w, uint16_t h, const CircleOverlay& circle) const;
    void render_crosshair(Span<uint8_t> buf, uint16_t w, uint16_t h, const Crosshair& ch) const;

    std::vector<Overlay> overlays_;
    OverlayId next_id_{1};
};

// ─────────────────────────────────────────────────────────────────────────────
// Drawing Primitives
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Set pixel in RGBA buffer with alpha blending.
 *
 * @param buffer RGBA buffer
 * @param width Buffer width
 * @param height Buffer height
 * @param x X coordinate
 * @param y Y coordinate
 * @param color Color with alpha
 */
void set_pixel_alpha(
    Span<uint8_t> buffer,
    uint16_t width, uint16_t height,
    int16_t x, int16_t y,
    RgbaColor color
) noexcept;

/**
 * @brief Draw horizontal line.
 */
void draw_hline(
    Span<uint8_t> buffer,
    uint16_t width, uint16_t height,
    int16_t x1, int16_t x2, int16_t y,
    RgbaColor color
) noexcept;

/**
 * @brief Draw vertical line.
 */
void draw_vline(
    Span<uint8_t> buffer,
    uint16_t width, uint16_t height,
    int16_t x, int16_t y1, int16_t y2,
    RgbaColor color
) noexcept;

/**
 * @brief Draw rectangle outline.
 */
void draw_rect(
    Span<uint8_t> buffer,
    uint16_t width, uint16_t height,
    int16_t x, int16_t y,
    int16_t w, int16_t h,
    RgbaColor color,
    uint8_t thickness = 1
) noexcept;

/**
 * @brief Fill rectangle.
 */
void fill_rect(
    Span<uint8_t> buffer,
    uint16_t width, uint16_t height,
    int16_t x, int16_t y,
    int16_t w, int16_t h,
    RgbaColor color
) noexcept;

/**
 * @brief Draw line between two points (Bresenham).
 */
void draw_line(
    Span<uint8_t> buffer,
    uint16_t width, uint16_t height,
    int16_t x1, int16_t y1,
    int16_t x2, int16_t y2,
    RgbaColor color,
    uint8_t thickness = 1
) noexcept;

/**
 * @brief Draw circle outline (midpoint algorithm).
 */
void draw_circle(
    Span<uint8_t> buffer,
    uint16_t width, uint16_t height,
    int16_t cx, int16_t cy,
    int16_t radius,
    RgbaColor color,
    uint8_t thickness = 1
) noexcept;

/**
 * @brief Fill circle.
 */
void fill_circle(
    Span<uint8_t> buffer,
    uint16_t width, uint16_t height,
    int16_t cx, int16_t cy,
    int16_t radius,
    RgbaColor color
) noexcept;

} // namespace legends::vision
