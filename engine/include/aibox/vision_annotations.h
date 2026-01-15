/**
 * @file vision_annotations.h
 * @brief Annotation formats for computer vision (YOLO, COCO).
 *
 * Provides structures and utilities for exporting detection results
 * in standard formats compatible with popular computer vision frameworks.
 */

#pragma once

#include <cstdint>
#include <optional>
#include <string>
#include <vector>

namespace aibox::vision {

// ─────────────────────────────────────────────────────────────────────────────
// Bounding Box Types
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Bounding box in normalized coordinates (0-1).
 *
 * YOLO format uses center-based normalized coordinates.
 */
struct NormalizedBBox {
    float center_x{0.0f};   ///< Center X (0-1)
    float center_y{0.0f};   ///< Center Y (0-1)
    float width{0.0f};      ///< Width (0-1)
    float height{0.0f};     ///< Height (0-1)

    /**
     * @brief Check if valid (all values in range).
     */
    [[nodiscard]] bool is_valid() const noexcept {
        return center_x >= 0.0f && center_x <= 1.0f &&
               center_y >= 0.0f && center_y <= 1.0f &&
               width >= 0.0f && width <= 1.0f &&
               height >= 0.0f && height <= 1.0f;
    }

    /**
     * @brief Get area (0-1).
     */
    [[nodiscard]] float area() const noexcept {
        return width * height;
    }
};

/**
 * @brief Bounding box in pixel coordinates (x, y, width, height).
 *
 * Top-left origin format used by COCO and most APIs.
 */
struct PixelBBox {
    int32_t x{0};       ///< Left edge
    int32_t y{0};       ///< Top edge
    int32_t width{0};   ///< Width
    int32_t height{0};  ///< Height

    /**
     * @brief Get right edge.
     */
    [[nodiscard]] int32_t right() const noexcept { return x + width; }

    /**
     * @brief Get bottom edge.
     */
    [[nodiscard]] int32_t bottom() const noexcept { return y + height; }

    /**
     * @brief Get center X.
     */
    [[nodiscard]] float center_x() const noexcept {
        return x + width / 2.0f;
    }

    /**
     * @brief Get center Y.
     */
    [[nodiscard]] float center_y() const noexcept {
        return y + height / 2.0f;
    }

    /**
     * @brief Get area in pixels.
     */
    [[nodiscard]] int64_t area() const noexcept {
        return static_cast<int64_t>(width) * height;
    }

    /**
     * @brief Convert to normalized coordinates.
     *
     * @param img_width Image width
     * @param img_height Image height
     * @return Normalized bounding box (YOLO format)
     */
    [[nodiscard]] NormalizedBBox normalize(int32_t img_width, int32_t img_height) const noexcept {
        if (img_width <= 0 || img_height <= 0) return {};
        return {
            (x + width / 2.0f) / img_width,
            (y + height / 2.0f) / img_height,
            static_cast<float>(width) / img_width,
            static_cast<float>(height) / img_height
        };
    }

    /**
     * @brief Create from normalized coordinates.
     *
     * @param norm Normalized bounding box
     * @param img_width Image width
     * @param img_height Image height
     * @return Pixel bounding box
     */
    [[nodiscard]] static PixelBBox from_normalized(
        const NormalizedBBox& norm,
        int32_t img_width,
        int32_t img_height
    ) noexcept {
        float w = norm.width * img_width;
        float h = norm.height * img_height;
        return {
            static_cast<int32_t>(norm.center_x * img_width - w / 2),
            static_cast<int32_t>(norm.center_y * img_height - h / 2),
            static_cast<int32_t>(w),
            static_cast<int32_t>(h)
        };
    }

    /**
     * @brief Clamp to image bounds.
     */
    [[nodiscard]] PixelBBox clamp(int32_t img_width, int32_t img_height) const noexcept {
        int32_t x1 = std::max<int32_t>(0, x);
        int32_t y1 = std::max<int32_t>(0, y);
        int32_t x2 = std::min<int32_t>(img_width, x + width);
        int32_t y2 = std::min<int32_t>(img_height, y + height);
        return {x1, y1, x2 - x1, y2 - y1};
    }

    /**
     * @brief Calculate IoU (Intersection over Union) with another box.
     */
    [[nodiscard]] float iou(const PixelBBox& other) const noexcept;

    [[nodiscard]] bool operator==(const PixelBBox& other) const noexcept {
        return x == other.x && y == other.y &&
               width == other.width && height == other.height;
    }

    [[nodiscard]] bool operator!=(const PixelBBox& other) const noexcept {
        return !(*this == other);
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// Detection Result
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Object detection result.
 */
struct Detection {
    int32_t class_id{0};             ///< Class ID (0-indexed)
    std::string class_name;          ///< Human-readable class name
    float confidence{0.0f};          ///< Detection confidence (0-1)
    PixelBBox bbox;                  ///< Bounding box in pixels
    std::optional<std::vector<int32_t>> mask_rle;  ///< RLE-encoded mask (for segmentation)

    /**
     * @brief Check if detection is valid.
     */
    [[nodiscard]] bool is_valid() const noexcept {
        return class_id >= 0 && confidence >= 0.0f && confidence <= 1.0f &&
               bbox.width > 0 && bbox.height > 0;
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// YOLO Annotation Format
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief YOLO annotation format handler.
 *
 * YOLO format: Each line is "<class_id> <center_x> <center_y> <width> <height>"
 * All coordinates are normalized (0-1).
 *
 * Example:
 * @code
 *   YoloAnnotation yolo;
 *   yolo.add({0, "person", 0.95f, {100, 50, 80, 120}});
 *   yolo.add({1, "car", 0.87f, {200, 100, 150, 100}});
 *
 *   std::string txt = yolo.export_txt(640, 480);
 *   // Output:
 *   // 0 0.218750 0.229167 0.125000 0.250000
 *   // 1 0.429688 0.312500 0.234375 0.208333
 * @endcode
 */
class YoloAnnotation {
public:
    /**
     * @brief Add a detection.
     */
    void add(const Detection& det);

    /**
     * @brief Add multiple detections.
     */
    void add_all(const std::vector<Detection>& dets);

    /**
     * @brief Clear all detections.
     */
    void clear() noexcept {
        detections_.clear();
    }

    /**
     * @brief Get number of detections.
     */
    [[nodiscard]] size_t count() const noexcept {
        return detections_.size();
    }

    /**
     * @brief Get all detections.
     */
    [[nodiscard]] const std::vector<Detection>& detections() const noexcept {
        return detections_;
    }

    /**
     * @brief Export to YOLO format string.
     *
     * Format: <class_id> <center_x> <center_y> <width> <height> [confidence]
     *
     * @param image_width Image width for normalization
     * @param image_height Image height for normalization
     * @param include_confidence Include confidence score (non-standard)
     * @return YOLO format text
     */
    [[nodiscard]] std::string export_txt(
        int32_t image_width,
        int32_t image_height,
        bool include_confidence = false
    ) const;

    /**
     * @brief Parse from YOLO format string.
     *
     * @param txt YOLO format text
     * @param image_width Image width for denormalization
     * @param image_height Image height for denormalization
     * @return Parsed annotation
     */
    [[nodiscard]] static YoloAnnotation parse_txt(
        const std::string& txt,
        int32_t image_width,
        int32_t image_height
    );

private:
    std::vector<Detection> detections_;
};

// ─────────────────────────────────────────────────────────────────────────────
// COCO Annotation Format
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief COCO image metadata.
 */
struct CocoImage {
    int32_t id{0};
    std::string file_name;
    int32_t width{0};
    int32_t height{0};
};

/**
 * @brief COCO category definition.
 */
struct CocoCategory {
    int32_t id{0};
    std::string name;
    std::string supercategory;
};

/**
 * @brief COCO annotation entry.
 */
struct CocoAnnotationEntry {
    int32_t id{0};
    int32_t image_id{0};
    int32_t category_id{0};
    std::vector<int32_t> bbox;   ///< [x, y, width, height]
    float area{0.0f};
    std::vector<std::vector<float>> segmentation;  ///< Polygon points
    int32_t iscrowd{0};
    float score{0.0f};           ///< For detection results
};

/**
 * @brief COCO annotation format handler.
 *
 * Supports full COCO format with images, categories, and annotations.
 *
 * Example:
 * @code
 *   CocoAnnotation coco;
 *
 *   // Add image metadata
 *   coco.add_image({1, "frame_001.png", 640, 480});
 *
 *   // Add categories
 *   coco.add_category({0, "person", "human"});
 *   coco.add_category({1, "car", "vehicle"});
 *
 *   // Add detections
 *   coco.add_detection({0, "person", 0.95f, {100, 50, 80, 120}}, 1);
 *
 *   std::string json = coco.export_json();
 * @endcode
 */
class CocoAnnotation {
public:
    /**
     * @brief Add image metadata.
     */
    void add_image(const CocoImage& img);

    /**
     * @brief Add category definition.
     */
    void add_category(const CocoCategory& cat);

    /**
     * @brief Add annotation entry directly.
     */
    void add_annotation(const CocoAnnotationEntry& ann);

    /**
     * @brief Add detection as annotation.
     *
     * @param det Detection result
     * @param image_id Associated image ID
     */
    void add_detection(const Detection& det, int32_t image_id);

    /**
     * @brief Clear all data.
     */
    void clear() noexcept {
        images_.clear();
        categories_.clear();
        annotations_.clear();
        next_annotation_id_ = 1;
    }

    /**
     * @brief Get images.
     */
    [[nodiscard]] const std::vector<CocoImage>& images() const noexcept {
        return images_;
    }

    /**
     * @brief Get categories.
     */
    [[nodiscard]] const std::vector<CocoCategory>& categories() const noexcept {
        return categories_;
    }

    /**
     * @brief Get annotations.
     */
    [[nodiscard]] const std::vector<CocoAnnotationEntry>& annotations() const noexcept {
        return annotations_;
    }

    /**
     * @brief Export to COCO JSON format.
     *
     * @return JSON string with full COCO structure
     */
    [[nodiscard]] std::string export_json() const;

    /**
     * @brief Export detection results only (for inference output).
     *
     * @param image_id Image ID to export results for
     * @return JSON array of detection results
     */
    [[nodiscard]] std::string export_results_json(int32_t image_id) const;

    /**
     * @brief Parse from COCO JSON.
     *
     * @param json COCO format JSON string
     * @return Parsed annotation (simplified parsing)
     */
    [[nodiscard]] static CocoAnnotation parse_json(const std::string& json);

private:
    std::vector<CocoImage> images_;
    std::vector<CocoCategory> categories_;
    std::vector<CocoAnnotationEntry> annotations_;
    int32_t next_annotation_id_{1};
};

// ─────────────────────────────────────────────────────────────────────────────
// RLE Encoding for Segmentation Masks
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Run-Length Encoding utilities for segmentation masks.
 */
class RleEncoder {
public:
    /**
     * @brief Encode binary mask to RLE.
     *
     * COCO RLE format: counts of alternating 0s and 1s, starting with 0s.
     *
     * @param mask Binary mask (true = foreground)
     * @param width Mask width
     * @param height Mask height
     * @return RLE counts
     */
    [[nodiscard]] static std::vector<int32_t> encode(
        const std::vector<bool>& mask,
        int32_t width,
        int32_t height
    );

    /**
     * @brief Decode RLE to binary mask.
     *
     * @param rle RLE counts
     * @param width Mask width
     * @param height Mask height
     * @return Binary mask
     */
    [[nodiscard]] static std::vector<bool> decode(
        const std::vector<int32_t>& rle,
        int32_t width,
        int32_t height
    );

    /**
     * @brief Calculate area from RLE (sum of foreground pixels).
     *
     * @param rle RLE counts
     * @return Foreground pixel count
     */
    [[nodiscard]] static int64_t area(const std::vector<int32_t>& rle) noexcept;

    /**
     * @brief Convert RLE to string representation.
     */
    [[nodiscard]] static std::string to_string(const std::vector<int32_t>& rle);

    /**
     * @brief Parse RLE from string.
     */
    [[nodiscard]] static std::vector<int32_t> from_string(const std::string& str);
};

// ─────────────────────────────────────────────────────────────────────────────
// Utility Functions
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Apply Non-Maximum Suppression to detections.
 *
 * @param detections Input detections
 * @param iou_threshold IoU threshold for suppression (default: 0.5)
 * @return Filtered detections
 */
[[nodiscard]] std::vector<Detection> nms(
    const std::vector<Detection>& detections,
    float iou_threshold = 0.5f
);

/**
 * @brief Filter detections by confidence threshold.
 *
 * @param detections Input detections
 * @param min_confidence Minimum confidence threshold
 * @return Filtered detections
 */
[[nodiscard]] std::vector<Detection> filter_by_confidence(
    const std::vector<Detection>& detections,
    float min_confidence
);

/**
 * @brief Filter detections by class ID.
 *
 * @param detections Input detections
 * @param class_ids Class IDs to keep
 * @return Filtered detections
 */
[[nodiscard]] std::vector<Detection> filter_by_class(
    const std::vector<Detection>& detections,
    const std::vector<int32_t>& class_ids
);

} // namespace aibox::vision
