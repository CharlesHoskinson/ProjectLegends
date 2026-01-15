/**
 * @file test_vision_annotations.cpp
 * @brief Unit tests for vision_annotations.h
 */

#include <gtest/gtest.h>
#include "aibox/vision_annotations.h"
#include <cmath>
#include <sstream>

using namespace aibox::vision;

// ─────────────────────────────────────────────────────────────────────────────
// NormalizedBBox Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(NormalizedBBoxTest, DefaultConstruction) {
    NormalizedBBox bbox;

    EXPECT_FLOAT_EQ(bbox.center_x, 0.0f);
    EXPECT_FLOAT_EQ(bbox.center_y, 0.0f);
    EXPECT_FLOAT_EQ(bbox.width, 0.0f);
    EXPECT_FLOAT_EQ(bbox.height, 0.0f);
}

TEST(NormalizedBBoxTest, IsValidInRange) {
    NormalizedBBox bbox{0.5f, 0.5f, 0.3f, 0.2f};
    EXPECT_TRUE(bbox.is_valid());
}

TEST(NormalizedBBoxTest, IsValidAtBoundaries) {
    NormalizedBBox bbox{0.0f, 0.0f, 1.0f, 1.0f};
    EXPECT_TRUE(bbox.is_valid());
}

TEST(NormalizedBBoxTest, IsValidOutOfRangeNegative) {
    NormalizedBBox bbox{-0.1f, 0.5f, 0.3f, 0.2f};
    EXPECT_FALSE(bbox.is_valid());
}

TEST(NormalizedBBoxTest, IsValidOutOfRangeGreaterThanOne) {
    NormalizedBBox bbox{0.5f, 0.5f, 1.1f, 0.2f};
    EXPECT_FALSE(bbox.is_valid());
}

TEST(NormalizedBBoxTest, Area) {
    NormalizedBBox bbox{0.5f, 0.5f, 0.4f, 0.5f};
    EXPECT_FLOAT_EQ(bbox.area(), 0.2f);
}

// ─────────────────────────────────────────────────────────────────────────────
// PixelBBox Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(PixelBBoxTest, DefaultConstruction) {
    PixelBBox bbox;

    EXPECT_EQ(bbox.x, 0);
    EXPECT_EQ(bbox.y, 0);
    EXPECT_EQ(bbox.width, 0);
    EXPECT_EQ(bbox.height, 0);
}

TEST(PixelBBoxTest, RightAndBottom) {
    PixelBBox bbox{10, 20, 100, 50};

    EXPECT_EQ(bbox.right(), 110);
    EXPECT_EQ(bbox.bottom(), 70);
}

TEST(PixelBBoxTest, CenterX) {
    PixelBBox bbox{10, 20, 100, 50};

    EXPECT_FLOAT_EQ(bbox.center_x(), 60.0f);
}

TEST(PixelBBoxTest, CenterY) {
    PixelBBox bbox{10, 20, 100, 50};

    EXPECT_FLOAT_EQ(bbox.center_y(), 45.0f);
}

TEST(PixelBBoxTest, Area) {
    PixelBBox bbox{10, 20, 100, 50};

    EXPECT_EQ(bbox.area(), 5000);
}

TEST(PixelBBoxTest, NormalizeBasic) {
    PixelBBox bbox{0, 0, 100, 100};
    NormalizedBBox norm = bbox.normalize(200, 200);

    EXPECT_FLOAT_EQ(norm.center_x, 0.25f);  // 50 / 200
    EXPECT_FLOAT_EQ(norm.center_y, 0.25f);  // 50 / 200
    EXPECT_FLOAT_EQ(norm.width, 0.5f);      // 100 / 200
    EXPECT_FLOAT_EQ(norm.height, 0.5f);     // 100 / 200
}

TEST(PixelBBoxTest, NormalizeMode13h) {
    // Typical Mode 13h detection
    PixelBBox bbox{100, 50, 80, 120};
    NormalizedBBox norm = bbox.normalize(320, 200);

    EXPECT_NEAR(norm.center_x, 0.4375f, 0.001f);   // (100 + 40) / 320
    EXPECT_NEAR(norm.center_y, 0.55f, 0.001f);     // (50 + 60) / 200
    EXPECT_NEAR(norm.width, 0.25f, 0.001f);        // 80 / 320
    EXPECT_NEAR(norm.height, 0.6f, 0.001f);        // 120 / 200
}

TEST(PixelBBoxTest, NormalizeZeroDimensions) {
    PixelBBox bbox{10, 20, 100, 50};

    NormalizedBBox norm1 = bbox.normalize(0, 200);
    EXPECT_FLOAT_EQ(norm1.center_x, 0.0f);

    NormalizedBBox norm2 = bbox.normalize(320, 0);
    EXPECT_FLOAT_EQ(norm2.center_y, 0.0f);
}

TEST(PixelBBoxTest, FromNormalized) {
    NormalizedBBox norm{0.5f, 0.5f, 0.25f, 0.3f};
    PixelBBox bbox = PixelBBox::from_normalized(norm, 320, 200);

    // center_x = 0.5 * 320 = 160
    // center_y = 0.5 * 200 = 100
    // width = 0.25 * 320 = 80
    // height = 0.3 * 200 = 60
    // x = 160 - 40 = 120
    // y = 100 - 30 = 70

    EXPECT_EQ(bbox.x, 120);
    EXPECT_EQ(bbox.y, 70);
    EXPECT_EQ(bbox.width, 80);
    EXPECT_EQ(bbox.height, 60);
}

TEST(PixelBBoxTest, Clamp) {
    PixelBBox bbox{-10, -5, 50, 30};
    PixelBBox clamped = bbox.clamp(320, 200);

    EXPECT_EQ(clamped.x, 0);
    EXPECT_EQ(clamped.y, 0);
    EXPECT_EQ(clamped.width, 40);   // 50 - 10
    EXPECT_EQ(clamped.height, 25);  // 30 - 5
}

TEST(PixelBBoxTest, ClampRightEdge) {
    PixelBBox bbox{300, 180, 50, 30};
    PixelBBox clamped = bbox.clamp(320, 200);

    EXPECT_EQ(clamped.x, 300);
    EXPECT_EQ(clamped.y, 180);
    EXPECT_EQ(clamped.width, 20);   // 320 - 300
    EXPECT_EQ(clamped.height, 20);  // 200 - 180
}

TEST(PixelBBoxTest, IouIdentical) {
    PixelBBox bbox{10, 20, 100, 50};
    float iou = bbox.iou(bbox);

    EXPECT_FLOAT_EQ(iou, 1.0f);
}

TEST(PixelBBoxTest, IouNoOverlap) {
    PixelBBox bbox1{0, 0, 50, 50};
    PixelBBox bbox2{100, 100, 50, 50};
    float iou = bbox1.iou(bbox2);

    EXPECT_FLOAT_EQ(iou, 0.0f);
}

TEST(PixelBBoxTest, IouPartialOverlap) {
    PixelBBox bbox1{0, 0, 100, 100};
    PixelBBox bbox2{50, 50, 100, 100};

    float iou = bbox1.iou(bbox2);

    // Intersection: 50x50 = 2500
    // Union: 10000 + 10000 - 2500 = 17500
    // IoU = 2500 / 17500 = ~0.143
    EXPECT_NEAR(iou, 0.143f, 0.01f);
}

TEST(PixelBBoxTest, Equality) {
    PixelBBox a{10, 20, 100, 50};
    PixelBBox b{10, 20, 100, 50};
    PixelBBox c{10, 20, 100, 51};

    EXPECT_TRUE(a == b);
    EXPECT_FALSE(a == c);
    EXPECT_FALSE(a != b);
    EXPECT_TRUE(a != c);
}

// ─────────────────────────────────────────────────────────────────────────────
// Detection Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(DetectionTest, DefaultConstruction) {
    Detection det;

    EXPECT_EQ(det.class_id, 0);
    EXPECT_TRUE(det.class_name.empty());
    EXPECT_FLOAT_EQ(det.confidence, 0.0f);
    EXPECT_EQ(det.bbox.x, 0);
    EXPECT_FALSE(det.mask_rle.has_value());
}

TEST(DetectionTest, IsValidBasic) {
    Detection det;
    det.class_id = 0;
    det.confidence = 0.95f;
    det.bbox = {10, 20, 100, 50};

    EXPECT_TRUE(det.is_valid());
}

TEST(DetectionTest, IsValidNegativeClassId) {
    Detection det;
    det.class_id = -1;
    det.confidence = 0.95f;
    det.bbox = {10, 20, 100, 50};

    EXPECT_FALSE(det.is_valid());
}

TEST(DetectionTest, IsValidInvalidConfidence) {
    Detection det;
    det.class_id = 0;
    det.confidence = 1.5f;  // > 1.0
    det.bbox = {10, 20, 100, 50};

    EXPECT_FALSE(det.is_valid());
}

TEST(DetectionTest, IsValidNegativeConfidence) {
    Detection det;
    det.class_id = 0;
    det.confidence = -0.5f;
    det.bbox = {10, 20, 100, 50};

    EXPECT_FALSE(det.is_valid());
}

TEST(DetectionTest, IsValidZeroDimensionBbox) {
    Detection det;
    det.class_id = 0;
    det.confidence = 0.95f;
    det.bbox = {10, 20, 0, 50};  // Zero width

    EXPECT_FALSE(det.is_valid());
}

// ─────────────────────────────────────────────────────────────────────────────
// YoloAnnotation Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(YoloAnnotationTest, InitiallyEmpty) {
    YoloAnnotation yolo;
    EXPECT_EQ(yolo.count(), 0);
}

TEST(YoloAnnotationTest, AddDetection) {
    YoloAnnotation yolo;

    Detection det;
    det.class_id = 0;
    det.class_name = "person";
    det.confidence = 0.95f;
    det.bbox = {100, 50, 80, 120};

    yolo.add(det);
    EXPECT_EQ(yolo.count(), 1);
}

TEST(YoloAnnotationTest, AddAllDetections) {
    YoloAnnotation yolo;

    std::vector<Detection> dets;
    dets.push_back({0, "person", 0.95f, {100, 50, 80, 120}});
    dets.push_back({1, "car", 0.87f, {200, 100, 150, 100}});

    yolo.add_all(dets);
    EXPECT_EQ(yolo.count(), 2);
}

TEST(YoloAnnotationTest, Clear) {
    YoloAnnotation yolo;

    yolo.add({0, "person", 0.95f, {100, 50, 80, 120}});
    EXPECT_EQ(yolo.count(), 1);

    yolo.clear();
    EXPECT_EQ(yolo.count(), 0);
}

TEST(YoloAnnotationTest, ExportTxt) {
    YoloAnnotation yolo;

    // Add a detection at center of 320x200 image
    Detection det;
    det.class_id = 0;
    det.bbox = {120, 70, 80, 60};  // center = (160, 100)

    yolo.add(det);

    std::string txt = yolo.export_txt(320, 200);

    // Expected: "0 0.500000 0.500000 0.250000 0.300000"
    // center_x = 160/320 = 0.5
    // center_y = 100/200 = 0.5
    // width = 80/320 = 0.25
    // height = 60/200 = 0.3

    EXPECT_TRUE(txt.find("0 0.5") != std::string::npos);
}

TEST(YoloAnnotationTest, ExportTxtWithConfidence) {
    YoloAnnotation yolo;

    Detection det;
    det.class_id = 1;
    det.confidence = 0.87f;
    det.bbox = {0, 0, 100, 100};

    yolo.add(det);

    std::string txt = yolo.export_txt(200, 200, true);

    // Should include confidence value
    EXPECT_TRUE(txt.find("0.87") != std::string::npos ||
                txt.find("0.870") != std::string::npos);
}

TEST(YoloAnnotationTest, ExportTxtMultiple) {
    YoloAnnotation yolo;

    yolo.add({0, "person", 0.95f, {0, 0, 64, 40}});
    yolo.add({1, "car", 0.87f, {160, 100, 64, 40}});

    std::string txt = yolo.export_txt(320, 200);

    // Should have 2 lines
    int line_count = 0;
    for (char c : txt) {
        if (c == '\n') ++line_count;
    }
    EXPECT_EQ(line_count, 2);
}

TEST(YoloAnnotationTest, ParseTxt) {
    std::string txt = "0 0.5 0.5 0.25 0.3\n1 0.25 0.25 0.1 0.2\n";

    YoloAnnotation yolo = YoloAnnotation::parse_txt(txt, 320, 200);

    EXPECT_EQ(yolo.count(), 2);

    const auto& dets = yolo.detections();
    EXPECT_EQ(dets[0].class_id, 0);
    EXPECT_EQ(dets[1].class_id, 1);
}

TEST(YoloAnnotationTest, GetDetections) {
    YoloAnnotation yolo;

    yolo.add({0, "person", 0.95f, {100, 50, 80, 120}});
    yolo.add({1, "car", 0.87f, {200, 100, 150, 100}});

    const auto& dets = yolo.detections();
    EXPECT_EQ(dets.size(), 2);
    EXPECT_EQ(dets[0].class_name, "person");
    EXPECT_EQ(dets[1].class_name, "car");
}

// ─────────────────────────────────────────────────────────────────────────────
// CocoAnnotation Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(CocoAnnotationTest, InitiallyEmpty) {
    CocoAnnotation coco;

    EXPECT_TRUE(coco.images().empty());
    EXPECT_TRUE(coco.categories().empty());
    EXPECT_TRUE(coco.annotations().empty());
}

TEST(CocoAnnotationTest, AddImage) {
    CocoAnnotation coco;

    coco.add_image({1, "frame_001.png", 320, 200});

    EXPECT_EQ(coco.images().size(), 1);
    EXPECT_EQ(coco.images()[0].id, 1);
    EXPECT_EQ(coco.images()[0].file_name, "frame_001.png");
}

TEST(CocoAnnotationTest, AddCategory) {
    CocoAnnotation coco;

    coco.add_category({0, "person", "human"});
    coco.add_category({1, "car", "vehicle"});

    EXPECT_EQ(coco.categories().size(), 2);
    EXPECT_EQ(coco.categories()[0].name, "person");
    EXPECT_EQ(coco.categories()[1].name, "car");
}

TEST(CocoAnnotationTest, AddAnnotation) {
    CocoAnnotation coco;

    CocoAnnotationEntry entry;
    entry.id = 1;
    entry.image_id = 1;
    entry.category_id = 0;
    entry.bbox = {100, 50, 80, 120};
    entry.area = 9600.0f;

    coco.add_annotation(entry);

    EXPECT_EQ(coco.annotations().size(), 1);
}

TEST(CocoAnnotationTest, AddDetection) {
    CocoAnnotation coco;

    coco.add_image({1, "frame_001.png", 320, 200});

    Detection det;
    det.class_id = 0;
    det.class_name = "person";
    det.confidence = 0.95f;
    det.bbox = {100, 50, 80, 120};

    coco.add_detection(det, 1);

    EXPECT_EQ(coco.annotations().size(), 1);
    EXPECT_EQ(coco.annotations()[0].image_id, 1);
    EXPECT_EQ(coco.annotations()[0].category_id, 0);
}

TEST(CocoAnnotationTest, Clear) {
    CocoAnnotation coco;

    coco.add_image({1, "frame.png", 320, 200});
    coco.add_category({0, "person", "human"});
    coco.add_detection({0, "person", 0.95f, {100, 50, 80, 120}}, 1);

    coco.clear();

    EXPECT_TRUE(coco.images().empty());
    EXPECT_TRUE(coco.categories().empty());
    EXPECT_TRUE(coco.annotations().empty());
}

TEST(CocoAnnotationTest, ExportJson) {
    CocoAnnotation coco;

    coco.add_image({1, "frame_001.png", 320, 200});
    coco.add_category({0, "person", "human"});
    coco.add_detection({0, "person", 0.95f, {100, 50, 80, 120}}, 1);

    std::string json = coco.export_json();

    // Should contain key COCO elements
    EXPECT_TRUE(json.find("\"images\"") != std::string::npos);
    EXPECT_TRUE(json.find("\"categories\"") != std::string::npos);
    EXPECT_TRUE(json.find("\"annotations\"") != std::string::npos);
    EXPECT_TRUE(json.find("frame_001.png") != std::string::npos);
    EXPECT_TRUE(json.find("\"person\"") != std::string::npos);
}

TEST(CocoAnnotationTest, ExportResultsJson) {
    CocoAnnotation coco;

    coco.add_image({1, "frame.png", 320, 200});
    coco.add_detection({0, "person", 0.95f, {100, 50, 80, 120}}, 1);

    std::string json = coco.export_results_json(1);

    // Results format is an array of detection objects
    EXPECT_TRUE(json.find("\"image_id\"") != std::string::npos);
    EXPECT_TRUE(json.find("\"category_id\"") != std::string::npos);
    EXPECT_TRUE(json.find("\"score\"") != std::string::npos);
}

// ─────────────────────────────────────────────────────────────────────────────
// RleEncoder Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(RleEncoderTest, EncodeAllZeros) {
    std::vector<bool> mask(100, false);

    auto rle = RleEncoder::encode(mask, 10, 10);

    // All zeros: should be [100]
    EXPECT_EQ(rle.size(), 1);
    EXPECT_EQ(rle[0], 100);
}

TEST(RleEncoderTest, EncodeAllOnes) {
    std::vector<bool> mask(100, true);

    auto rle = RleEncoder::encode(mask, 10, 10);

    // All ones: should be [0, 100]
    EXPECT_EQ(rle.size(), 2);
    EXPECT_EQ(rle[0], 0);
    EXPECT_EQ(rle[1], 100);
}

TEST(RleEncoderTest, EncodeAlternating) {
    std::vector<bool> mask = {false, true, false, true, false, true};

    auto rle = RleEncoder::encode(mask, 6, 1);

    // [1, 1, 1, 1, 1, 1]
    EXPECT_EQ(rle.size(), 6);
    for (int32_t val : rle) {
        EXPECT_EQ(val, 1);
    }
}

TEST(RleEncoderTest, DecodeBasic) {
    std::vector<int32_t> rle = {3, 5, 2};  // 3 zeros, 5 ones, 2 zeros

    auto mask = RleEncoder::decode(rle, 10, 1);

    EXPECT_EQ(mask.size(), 10);
    EXPECT_FALSE(mask[0]);
    EXPECT_FALSE(mask[1]);
    EXPECT_FALSE(mask[2]);
    EXPECT_TRUE(mask[3]);
    EXPECT_TRUE(mask[4]);
    EXPECT_TRUE(mask[5]);
    EXPECT_TRUE(mask[6]);
    EXPECT_TRUE(mask[7]);
    EXPECT_FALSE(mask[8]);
    EXPECT_FALSE(mask[9]);
}

TEST(RleEncoderTest, AreaFromRle) {
    std::vector<int32_t> rle = {10, 50, 40};  // 10 zeros, 50 ones, 40 zeros

    int64_t area = RleEncoder::area(rle);

    EXPECT_EQ(area, 50);  // Sum of ones
}

TEST(RleEncoderTest, AreaAllZeros) {
    std::vector<int32_t> rle = {100};

    int64_t area = RleEncoder::area(rle);

    EXPECT_EQ(area, 0);
}

TEST(RleEncoderTest, RoundTrip) {
    // Create a random-ish mask
    std::vector<bool> original(100, false);
    for (size_t i = 20; i < 50; ++i) {
        original[i] = true;
    }
    for (size_t i = 70; i < 90; ++i) {
        original[i] = true;
    }

    auto rle = RleEncoder::encode(original, 10, 10);
    auto decoded = RleEncoder::decode(rle, 10, 10);

    EXPECT_EQ(original.size(), decoded.size());
    for (size_t i = 0; i < original.size(); ++i) {
        EXPECT_EQ(original[i], decoded[i]) << "Mismatch at index " << i;
    }
}

TEST(RleEncoderTest, ToString) {
    std::vector<int32_t> rle = {10, 20, 30};

    std::string str = RleEncoder::to_string(rle);

    EXPECT_TRUE(str.find("10") != std::string::npos);
    EXPECT_TRUE(str.find("20") != std::string::npos);
    EXPECT_TRUE(str.find("30") != std::string::npos);
}

TEST(RleEncoderTest, FromString) {
    std::string str = "10 20 30";

    auto rle = RleEncoder::from_string(str);

    EXPECT_EQ(rle.size(), 3);
    EXPECT_EQ(rle[0], 10);
    EXPECT_EQ(rle[1], 20);
    EXPECT_EQ(rle[2], 30);
}

// ─────────────────────────────────────────────────────────────────────────────
// Utility Function Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(UtilityFunctionTest, NmsEmpty) {
    std::vector<Detection> dets;

    auto filtered = nms(dets, 0.5f);

    EXPECT_TRUE(filtered.empty());
}

TEST(UtilityFunctionTest, NmsSingleDetection) {
    std::vector<Detection> dets = {
        {0, "person", 0.95f, {100, 50, 80, 120}}
    };

    auto filtered = nms(dets, 0.5f);

    EXPECT_EQ(filtered.size(), 1);
}

TEST(UtilityFunctionTest, NmsNoOverlap) {
    std::vector<Detection> dets = {
        {0, "person", 0.95f, {0, 0, 50, 50}},
        {0, "person", 0.90f, {100, 100, 50, 50}}
    };

    auto filtered = nms(dets, 0.5f);

    // No overlap, both should remain
    EXPECT_EQ(filtered.size(), 2);
}

TEST(UtilityFunctionTest, NmsHighOverlap) {
    std::vector<Detection> dets = {
        {0, "person", 0.95f, {100, 100, 100, 100}},
        {0, "person", 0.90f, {105, 105, 100, 100}}  // High overlap
    };

    auto filtered = nms(dets, 0.3f);

    // High overlap, only highest confidence should remain
    EXPECT_EQ(filtered.size(), 1);
    EXPECT_FLOAT_EQ(filtered[0].confidence, 0.95f);
}

TEST(UtilityFunctionTest, FilterByConfidence) {
    std::vector<Detection> dets = {
        {0, "person", 0.95f, {0, 0, 50, 50}},
        {0, "person", 0.30f, {100, 0, 50, 50}},
        {0, "person", 0.70f, {200, 0, 50, 50}}
    };

    auto filtered = filter_by_confidence(dets, 0.5f);

    EXPECT_EQ(filtered.size(), 2);
    for (const auto& det : filtered) {
        EXPECT_GE(det.confidence, 0.5f);
    }
}

TEST(UtilityFunctionTest, FilterByConfidenceAllPass) {
    std::vector<Detection> dets = {
        {0, "person", 0.95f, {0, 0, 50, 50}},
        {0, "person", 0.90f, {100, 0, 50, 50}}
    };

    auto filtered = filter_by_confidence(dets, 0.5f);

    EXPECT_EQ(filtered.size(), 2);
}

TEST(UtilityFunctionTest, FilterByConfidenceNonePass) {
    std::vector<Detection> dets = {
        {0, "person", 0.30f, {0, 0, 50, 50}},
        {0, "person", 0.40f, {100, 0, 50, 50}}
    };

    auto filtered = filter_by_confidence(dets, 0.5f);

    EXPECT_TRUE(filtered.empty());
}

TEST(UtilityFunctionTest, FilterByClass) {
    std::vector<Detection> dets = {
        {0, "person", 0.95f, {0, 0, 50, 50}},
        {1, "car", 0.90f, {100, 0, 50, 50}},
        {0, "person", 0.85f, {200, 0, 50, 50}},
        {2, "bike", 0.80f, {300, 0, 50, 50}}
    };

    auto filtered = filter_by_class(dets, {0, 2});  // Only person and bike

    EXPECT_EQ(filtered.size(), 3);
    for (const auto& det : filtered) {
        EXPECT_TRUE(det.class_id == 0 || det.class_id == 2);
    }
}

TEST(UtilityFunctionTest, FilterByClassEmpty) {
    std::vector<Detection> dets = {
        {0, "person", 0.95f, {0, 0, 50, 50}}
    };

    auto filtered = filter_by_class(dets, {});

    EXPECT_TRUE(filtered.empty());
}

// ─────────────────────────────────────────────────────────────────────────────
// Edge Cases
// ─────────────────────────────────────────────────────────────────────────────

TEST(EdgeCaseTest, NormalizeTinyBox) {
    PixelBBox bbox{0, 0, 1, 1};
    NormalizedBBox norm = bbox.normalize(320, 200);

    EXPECT_GT(norm.width, 0.0f);
    EXPECT_GT(norm.height, 0.0f);
}

TEST(EdgeCaseTest, IouSameBox) {
    PixelBBox bbox{50, 50, 100, 100};
    float iou = bbox.iou(bbox);

    EXPECT_FLOAT_EQ(iou, 1.0f);
}

TEST(EdgeCaseTest, IouAdjacentBoxes) {
    PixelBBox bbox1{0, 0, 50, 50};
    PixelBBox bbox2{50, 0, 50, 50};  // Adjacent (touching)

    float iou = bbox1.iou(bbox2);

    EXPECT_FLOAT_EQ(iou, 0.0f);  // No overlap
}

TEST(EdgeCaseTest, YoloEmptyExport) {
    YoloAnnotation yolo;

    std::string txt = yolo.export_txt(320, 200);

    EXPECT_TRUE(txt.empty());
}

TEST(EdgeCaseTest, RleEmptyMask) {
    std::vector<bool> mask;

    auto rle = RleEncoder::encode(mask, 0, 0);

    EXPECT_TRUE(rle.empty());
}
