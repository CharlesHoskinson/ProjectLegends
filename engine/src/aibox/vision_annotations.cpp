/**
 * @file vision_annotations.cpp
 * @brief Implementation of annotation formats for computer vision (YOLO, COCO).
 */

#include "aibox/vision_annotations.h"
#include <algorithm>
#include <cmath>
#include <iomanip>
#include <sstream>

namespace aibox::vision {

// ─────────────────────────────────────────────────────────────────────────────
// PixelBBox Implementation
// ─────────────────────────────────────────────────────────────────────────────

float PixelBBox::iou(const PixelBBox& other) const noexcept {
    // Calculate intersection
    int32_t x1 = std::max(x, other.x);
    int32_t y1 = std::max(y, other.y);
    int32_t x2 = std::min(right(), other.right());
    int32_t y2 = std::min(bottom(), other.bottom());

    if (x1 >= x2 || y1 >= y2) {
        return 0.0f;  // No intersection
    }

    int64_t intersection = static_cast<int64_t>(x2 - x1) * (y2 - y1);

    // Calculate union
    int64_t area1 = area();
    int64_t area2 = other.area();
    int64_t union_area = area1 + area2 - intersection;

    if (union_area <= 0) {
        return 0.0f;
    }

    return static_cast<float>(intersection) / static_cast<float>(union_area);
}

// ─────────────────────────────────────────────────────────────────────────────
// YoloAnnotation Implementation
// ─────────────────────────────────────────────────────────────────────────────

void YoloAnnotation::add(const Detection& det) {
    detections_.push_back(det);
}

void YoloAnnotation::add_all(const std::vector<Detection>& dets) {
    detections_.insert(detections_.end(), dets.begin(), dets.end());
}

std::string YoloAnnotation::export_txt(
    int32_t image_width,
    int32_t image_height,
    bool include_confidence
) const {
    std::ostringstream oss;
    oss << std::fixed << std::setprecision(6);

    for (const auto& det : detections_) {
        NormalizedBBox norm = det.bbox.normalize(image_width, image_height);

        oss << det.class_id << " "
            << norm.center_x << " "
            << norm.center_y << " "
            << norm.width << " "
            << norm.height;

        if (include_confidence) {
            oss << " " << det.confidence;
        }

        oss << "\n";
    }

    return oss.str();
}

YoloAnnotation YoloAnnotation::parse_txt(
    const std::string& txt,
    int32_t image_width,
    int32_t image_height
) {
    YoloAnnotation result;
    std::istringstream iss(txt);
    std::string line;

    while (std::getline(iss, line)) {
        if (line.empty()) continue;

        std::istringstream line_ss(line);
        Detection det;
        NormalizedBBox norm;

        line_ss >> det.class_id >> norm.center_x >> norm.center_y
                >> norm.width >> norm.height;

        // Optional confidence
        if (line_ss >> det.confidence) {
            // Got confidence
        } else {
            det.confidence = 1.0f;
        }

        det.bbox = PixelBBox::from_normalized(norm, image_width, image_height);
        result.add(det);
    }

    return result;
}

// ─────────────────────────────────────────────────────────────────────────────
// CocoAnnotation Implementation
// ─────────────────────────────────────────────────────────────────────────────

void CocoAnnotation::add_image(const CocoImage& img) {
    images_.push_back(img);
}

void CocoAnnotation::add_category(const CocoCategory& cat) {
    categories_.push_back(cat);
}

void CocoAnnotation::add_annotation(const CocoAnnotationEntry& ann) {
    annotations_.push_back(ann);
}

void CocoAnnotation::add_detection(const Detection& det, int32_t image_id) {
    CocoAnnotationEntry entry;
    entry.id = next_annotation_id_++;
    entry.image_id = image_id;
    entry.category_id = det.class_id;
    entry.bbox = {det.bbox.x, det.bbox.y, det.bbox.width, det.bbox.height};
    entry.area = static_cast<float>(det.bbox.area());
    entry.score = det.confidence;
    entry.iscrowd = 0;

    annotations_.push_back(entry);
}

std::string CocoAnnotation::export_json() const {
    std::ostringstream oss;
    oss << std::fixed << std::setprecision(2);

    oss << "{\n";

    // Images array
    oss << "  \"images\": [\n";
    for (size_t i = 0; i < images_.size(); ++i) {
        const auto& img = images_[i];
        oss << "    {\n";
        oss << "      \"id\": " << img.id << ",\n";
        oss << "      \"file_name\": \"" << img.file_name << "\",\n";
        oss << "      \"width\": " << img.width << ",\n";
        oss << "      \"height\": " << img.height << "\n";
        oss << "    }";
        if (i < images_.size() - 1) oss << ",";
        oss << "\n";
    }
    oss << "  ],\n";

    // Categories array
    oss << "  \"categories\": [\n";
    for (size_t i = 0; i < categories_.size(); ++i) {
        const auto& cat = categories_[i];
        oss << "    {\n";
        oss << "      \"id\": " << cat.id << ",\n";
        oss << "      \"name\": \"" << cat.name << "\",\n";
        oss << "      \"supercategory\": \"" << cat.supercategory << "\"\n";
        oss << "    }";
        if (i < categories_.size() - 1) oss << ",";
        oss << "\n";
    }
    oss << "  ],\n";

    // Annotations array
    oss << "  \"annotations\": [\n";
    for (size_t i = 0; i < annotations_.size(); ++i) {
        const auto& ann = annotations_[i];
        oss << "    {\n";
        oss << "      \"id\": " << ann.id << ",\n";
        oss << "      \"image_id\": " << ann.image_id << ",\n";
        oss << "      \"category_id\": " << ann.category_id << ",\n";
        oss << "      \"bbox\": [" << ann.bbox[0] << ", " << ann.bbox[1] << ", "
            << ann.bbox[2] << ", " << ann.bbox[3] << "],\n";
        oss << "      \"area\": " << ann.area << ",\n";
        oss << "      \"iscrowd\": " << ann.iscrowd << ",\n";
        oss << "      \"score\": " << ann.score << "\n";
        oss << "    }";
        if (i < annotations_.size() - 1) oss << ",";
        oss << "\n";
    }
    oss << "  ]\n";

    oss << "}\n";

    return oss.str();
}

std::string CocoAnnotation::export_results_json(int32_t image_id) const {
    std::ostringstream oss;
    oss << std::fixed << std::setprecision(2);

    oss << "[\n";

    bool first = true;
    for (const auto& ann : annotations_) {
        if (ann.image_id != image_id) continue;

        if (!first) oss << ",\n";
        first = false;

        oss << "  {\n";
        oss << "    \"image_id\": " << ann.image_id << ",\n";
        oss << "    \"category_id\": " << ann.category_id << ",\n";
        oss << "    \"bbox\": [" << ann.bbox[0] << ", " << ann.bbox[1] << ", "
            << ann.bbox[2] << ", " << ann.bbox[3] << "],\n";
        oss << "    \"score\": " << ann.score << "\n";
        oss << "  }";
    }

    oss << "\n]\n";

    return oss.str();
}

CocoAnnotation CocoAnnotation::parse_json(const std::string& json) {
    // Simplified JSON parsing - a full implementation would use a proper JSON library
    // This is a basic implementation for demonstration purposes
    CocoAnnotation result;

    // For now, return empty result
    // A real implementation would parse the JSON structure
    return result;
}

// ─────────────────────────────────────────────────────────────────────────────
// RleEncoder Implementation
// ─────────────────────────────────────────────────────────────────────────────

std::vector<int32_t> RleEncoder::encode(
    const std::vector<bool>& mask,
    int32_t width,
    int32_t height
) {
    std::vector<int32_t> rle;
    if (mask.empty()) return rle;

    bool current_value = false;  // Start with zeros
    int32_t count = 0;

    for (bool val : mask) {
        if (val == current_value) {
            ++count;
        } else {
            rle.push_back(count);
            count = 1;
            current_value = val;
        }
    }

    // Push final count
    rle.push_back(count);

    return rle;
}

std::vector<bool> RleEncoder::decode(
    const std::vector<int32_t>& rle,
    int32_t width,
    int32_t height
) {
    std::vector<bool> mask;
    mask.reserve(static_cast<size_t>(width) * height);

    bool current_value = false;  // Start with zeros
    for (int32_t count : rle) {
        for (int32_t i = 0; i < count; ++i) {
            mask.push_back(current_value);
        }
        current_value = !current_value;
    }

    return mask;
}

int64_t RleEncoder::area(const std::vector<int32_t>& rle) noexcept {
    int64_t total = 0;

    // Sum odd-indexed counts (ones)
    for (size_t i = 1; i < rle.size(); i += 2) {
        total += rle[i];
    }

    return total;
}

std::string RleEncoder::to_string(const std::vector<int32_t>& rle) {
    std::ostringstream oss;
    for (size_t i = 0; i < rle.size(); ++i) {
        if (i > 0) oss << " ";
        oss << rle[i];
    }
    return oss.str();
}

std::vector<int32_t> RleEncoder::from_string(const std::string& str) {
    std::vector<int32_t> rle;
    std::istringstream iss(str);
    int32_t val;
    while (iss >> val) {
        rle.push_back(val);
    }
    return rle;
}

// ─────────────────────────────────────────────────────────────────────────────
// Utility Functions
// ─────────────────────────────────────────────────────────────────────────────

std::vector<Detection> nms(
    const std::vector<Detection>& detections,
    float iou_threshold
) {
    if (detections.empty()) return {};

    // Sort by confidence (descending)
    std::vector<Detection> sorted = detections;
    std::sort(sorted.begin(), sorted.end(),
        [](const Detection& a, const Detection& b) {
            return a.confidence > b.confidence;
        });

    std::vector<Detection> result;
    std::vector<bool> suppressed(sorted.size(), false);

    for (size_t i = 0; i < sorted.size(); ++i) {
        if (suppressed[i]) continue;

        result.push_back(sorted[i]);

        // Suppress overlapping boxes
        for (size_t j = i + 1; j < sorted.size(); ++j) {
            if (suppressed[j]) continue;

            float iou = sorted[i].bbox.iou(sorted[j].bbox);
            if (iou > iou_threshold) {
                suppressed[j] = true;
            }
        }
    }

    return result;
}

std::vector<Detection> filter_by_confidence(
    const std::vector<Detection>& detections,
    float min_confidence
) {
    std::vector<Detection> result;
    result.reserve(detections.size());

    for (const auto& det : detections) {
        if (det.confidence >= min_confidence) {
            result.push_back(det);
        }
    }

    return result;
}

std::vector<Detection> filter_by_class(
    const std::vector<Detection>& detections,
    const std::vector<int32_t>& class_ids
) {
    if (class_ids.empty()) return {};

    std::vector<Detection> result;
    result.reserve(detections.size());

    for (const auto& det : detections) {
        if (std::find(class_ids.begin(), class_ids.end(), det.class_id) != class_ids.end()) {
            result.push_back(det);
        }
    }

    return result;
}

}  // namespace aibox::vision
