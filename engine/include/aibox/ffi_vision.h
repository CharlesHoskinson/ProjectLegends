/**
 * @file ffi_vision.h
 * @brief C FFI API for vision model integration.
 *
 * Provides a C-compatible API for screenshot capture, overlay management,
 * and annotation export for external language bindings (Rust, Python, etc.).
 */

#pragma once

#include "ffi_core.h"
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

// ─────────────────────────────────────────────────────────────────────────────
// Result Codes (use unified aibox_error_t from ffi_core.h)
// ─────────────────────────────────────────────────────────────────────────────

/* Vision functions use the unified aibox_error_t from ffi_core.h.
 * Vision-specific error codes are in the 300-399 range:
 *   AIBOX_ERR_VISION_NO_FRAMEBUFFER    = 300
 *   AIBOX_ERR_VISION_NOT_DIRTY         = 301
 *   AIBOX_ERR_VISION_INVALID_FORMAT    = 302
 *   AIBOX_ERR_VISION_OVERLAY_NOT_FOUND = 303
 *
 * Common error codes also apply:
 *   AIBOX_ERR_NOT_INITIALIZED          = 3
 *   AIBOX_ERR_INVALID_PARAM            = 1
 *   AIBOX_ERR_BUFFER_TOO_SMALL         = 6
 *   AIBOX_ERR_OUT_OF_MEMORY            = 7
 */

/* Backward compatibility typedefs */
typedef aibox_error_t VisionResult;
#define VISION_OK                      AIBOX_OK
#define VISION_ERROR_NOT_INITIALIZED   AIBOX_ERR_NOT_INITIALIZED
#define VISION_ERROR_INVALID_PARAM     AIBOX_ERR_INVALID_PARAM
#define VISION_ERROR_BUFFER_TOO_SMALL  AIBOX_ERR_BUFFER_TOO_SMALL
#define VISION_ERROR_NO_FRAMEBUFFER    AIBOX_ERR_VISION_NO_FRAMEBUFFER
#define VISION_ERROR_NOT_DIRTY         AIBOX_ERR_VISION_NOT_DIRTY
#define VISION_ERROR_INVALID_FORMAT    AIBOX_ERR_VISION_INVALID_FORMAT
#define VISION_ERROR_ALLOCATION        AIBOX_ERR_OUT_OF_MEMORY
#define VISION_ERROR_OVERLAY_NOT_FOUND AIBOX_ERR_VISION_OVERLAY_NOT_FOUND
#define VISION_ERROR_INTERNAL          AIBOX_ERR_INTERNAL

// ─────────────────────────────────────────────────────────────────────────────
// Pixel Formats
// ─────────────────────────────────────────────────────────────────────────────

/** @brief Output pixel formats. */
typedef enum {
    VISION_FORMAT_INDEXED8 = 0,   /**< Raw indexed (no palette applied) */
    VISION_FORMAT_RGB24 = 1,      /**< 24-bit RGB */
    VISION_FORMAT_RGBA32 = 2,     /**< 32-bit RGBA */
    VISION_FORMAT_BGR24 = 3,      /**< 24-bit BGR (Windows BMP order) */
    VISION_FORMAT_BGRA32 = 4,     /**< 32-bit BGRA */
    VISION_FORMAT_GRAYSCALE8 = 5  /**< 8-bit grayscale */
} VisionPixelFormat;

/** @brief Scaling modes. */
typedef enum {
    VISION_SCALE_NATIVE = 0,          /**< No scaling (1:1) */
    VISION_SCALE_NEAREST = 1,         /**< Nearest neighbor (pixelated) */
    VISION_SCALE_BILINEAR = 2,        /**< Bilinear interpolation */
    VISION_SCALE_ASPECT_CORRECT = 3   /**< Correct DOS aspect ratio */
} VisionScaleMode;

// ─────────────────────────────────────────────────────────────────────────────
// Data Structures
// ─────────────────────────────────────────────────────────────────────────────

/** @brief VGA mode information. */
typedef struct {
    uint16_t width;           /**< Screen width in pixels */
    uint16_t height;          /**< Screen height in pixels */
    uint8_t bits_per_pixel;   /**< Bits per pixel (8, 4, 2, 1) */
    uint8_t is_text_mode;     /**< Non-zero if text mode */
    uint8_t is_planar;        /**< Non-zero if planar mode */
    uint8_t text_columns;     /**< Text columns (if text mode) */
    uint8_t text_rows;        /**< Text rows (if text mode) */
    uint8_t reserved[3];      /**< Reserved for alignment */
} VisionModeInfo;

/** @brief RGB color (24-bit). */
typedef struct {
    uint8_t r;  /**< Red component */
    uint8_t g;  /**< Green component */
    uint8_t b;  /**< Blue component */
} VisionRgbColor;

/** @brief RGBA color (32-bit). */
typedef struct {
    uint8_t r;  /**< Red component */
    uint8_t g;  /**< Green component */
    uint8_t b;  /**< Blue component */
    uint8_t a;  /**< Alpha component */
} VisionRgbaColor;

/** @brief Capture configuration. */
typedef struct {
    VisionPixelFormat format;     /**< Output pixel format */
    VisionScaleMode scale_mode;   /**< Scaling mode */
    uint8_t scale_factor;         /**< Integer scale factor (1, 2, 4) */
    uint16_t target_width;        /**< Target width (0 = auto) */
    uint16_t target_height;       /**< Target height (0 = auto) */
    uint8_t include_overlay;      /**< Include overlay in output */
    uint8_t flip_vertical;        /**< Flip for OpenGL texture upload */
    uint8_t reserved[2];          /**< Reserved for alignment */
} VisionCaptureConfig;

/** @brief Screenshot result metadata. */
typedef struct {
    uint16_t width;               /**< Output width */
    uint16_t height;              /**< Output height */
    VisionPixelFormat format;     /**< Pixel format */
    uint8_t reserved;             /**< Reserved for alignment */
    uint64_t capture_time_us;     /**< Capture timestamp (microseconds) */
    uint64_t frame_number;        /**< DOSBox frame counter */
    size_t pixel_data_size;       /**< Size of pixel data in bytes */
} VisionScreenshotInfo;

/** @brief Bounding box (pixel coordinates). */
typedef struct {
    int32_t x;      /**< Left edge */
    int32_t y;      /**< Top edge */
    int32_t width;  /**< Width */
    int32_t height; /**< Height */
} VisionBBox;

/** @brief Detection result. */
typedef struct {
    int32_t class_id;       /**< Class ID (0-indexed) */
    float confidence;       /**< Detection confidence (0-1) */
    VisionBBox bbox;        /**< Bounding box */
} VisionDetection;

// ─────────────────────────────────────────────────────────────────────────────
// Overlay Handle
// ─────────────────────────────────────────────────────────────────────────────

/** @brief Overlay identifier. */
typedef uint32_t VisionOverlayId;

/** @brief Invalid overlay ID constant. */
#define VISION_INVALID_OVERLAY ((VisionOverlayId)0)

// ─────────────────────────────────────────────────────────────────────────────
// Initialization
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Initialize the vision subsystem.
 *
 * Must be called before any other vision functions.
 * Safe to call multiple times (idempotent).
 *
 * @return VISION_OK on success
 */
VisionResult vision_init(void);

/**
 * @brief Shutdown the vision subsystem.
 *
 * Releases all resources. Safe to call even if not initialized.
 */
void vision_shutdown(void);

/**
 * @brief Check if vision subsystem is initialized.
 *
 * @return Non-zero if initialized
 */
int vision_is_initialized(void);

// ─────────────────────────────────────────────────────────────────────────────
// Mode and Palette Query
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Get current VGA mode information.
 *
 * @param[out] info Mode information output
 * @return VISION_OK on success
 */
VisionResult vision_get_mode(VisionModeInfo* info);

/**
 * @brief Get VGA palette (256 RGB colors).
 *
 * @param[out] palette_out Output buffer for 256 RGB colors (768 bytes)
 * @param buffer_size Size of output buffer (must be >= 768)
 * @return VISION_OK on success
 */
VisionResult vision_get_palette(VisionRgbColor* palette_out, size_t buffer_size);

/**
 * @brief Get raw indexed framebuffer data.
 *
 * Returns the raw VGA framebuffer without palette application.
 *
 * @param[out] buffer_out Output buffer
 * @param buffer_size Size of output buffer
 * @param[out] actual_size Actual size of framebuffer data
 * @return VISION_OK on success
 */
VisionResult vision_get_indexed_pixels(
    uint8_t* buffer_out,
    size_t buffer_size,
    size_t* actual_size
);

// ─────────────────────────────────────────────────────────────────────────────
// Screenshot Capture
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Configure capture settings.
 *
 * @param config Capture configuration
 * @return VISION_OK on success
 */
VisionResult vision_configure_capture(const VisionCaptureConfig* config);

/**
 * @brief Get current capture configuration.
 *
 * @param[out] config Configuration output
 * @return VISION_OK on success
 */
VisionResult vision_get_capture_config(VisionCaptureConfig* config);

/**
 * @brief Calculate required buffer size for capture.
 *
 * @param[out] size Required buffer size in bytes
 * @return VISION_OK on success
 */
VisionResult vision_get_capture_buffer_size(size_t* size);

/**
 * @brief Capture current frame.
 *
 * @param[out] pixel_buffer Output buffer for pixel data
 * @param buffer_size Size of output buffer
 * @param[out] info Screenshot metadata
 * @return VISION_OK on success
 */
VisionResult vision_capture(
    uint8_t* pixel_buffer,
    size_t buffer_size,
    VisionScreenshotInfo* info
);

/**
 * @brief Capture frame only if framebuffer changed.
 *
 * @param[out] pixel_buffer Output buffer for pixel data
 * @param buffer_size Size of output buffer
 * @param[out] info Screenshot metadata
 * @return VISION_OK on success, VISION_ERROR_NOT_DIRTY if unchanged
 */
VisionResult vision_capture_if_dirty(
    uint8_t* pixel_buffer,
    size_t buffer_size,
    VisionScreenshotInfo* info
);

// ─────────────────────────────────────────────────────────────────────────────
// Overlay Management
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Add a bounding box overlay.
 *
 * @param x Left edge X coordinate
 * @param y Top edge Y coordinate
 * @param width Box width
 * @param height Box height
 * @param color Border color
 * @param thickness Border thickness in pixels
 * @param[out] id_out Assigned overlay ID
 * @return VISION_OK on success
 */
VisionResult vision_add_bbox(
    int16_t x, int16_t y,
    int16_t width, int16_t height,
    VisionRgbaColor color,
    uint8_t thickness,
    VisionOverlayId* id_out
);

/**
 * @brief Add a text label overlay.
 *
 * @param x X coordinate
 * @param y Y coordinate
 * @param text Label text (null-terminated)
 * @param color Text color
 * @param font_size Font size in pixels
 * @param[out] id_out Assigned overlay ID
 * @return VISION_OK on success
 */
VisionResult vision_add_label(
    int16_t x, int16_t y,
    const char* text,
    VisionRgbaColor color,
    uint8_t font_size,
    VisionOverlayId* id_out
);

/**
 * @brief Add a highlight region overlay.
 *
 * @param x Left edge X coordinate
 * @param y Top edge Y coordinate
 * @param width Region width
 * @param height Region height
 * @param color Highlight color (semi-transparent recommended)
 * @param[out] id_out Assigned overlay ID
 * @return VISION_OK on success
 */
VisionResult vision_add_highlight(
    int16_t x, int16_t y,
    int16_t width, int16_t height,
    VisionRgbaColor color,
    VisionOverlayId* id_out
);

/**
 * @brief Add a line overlay.
 *
 * @param x1 Start X coordinate
 * @param y1 Start Y coordinate
 * @param x2 End X coordinate
 * @param y2 End Y coordinate
 * @param color Line color
 * @param thickness Line thickness
 * @param[out] id_out Assigned overlay ID
 * @return VISION_OK on success
 */
VisionResult vision_add_line(
    int16_t x1, int16_t y1,
    int16_t x2, int16_t y2,
    VisionRgbaColor color,
    uint8_t thickness,
    VisionOverlayId* id_out
);

/**
 * @brief Add a circle overlay.
 *
 * @param cx Center X coordinate
 * @param cy Center Y coordinate
 * @param radius Circle radius
 * @param color Circle color
 * @param thickness Border thickness
 * @param filled Fill interior if non-zero
 * @param[out] id_out Assigned overlay ID
 * @return VISION_OK on success
 */
VisionResult vision_add_circle(
    int16_t cx, int16_t cy,
    int16_t radius,
    VisionRgbaColor color,
    uint8_t thickness,
    uint8_t filled,
    VisionOverlayId* id_out
);

/**
 * @brief Add a crosshair marker overlay.
 *
 * @param x Center X coordinate
 * @param y Center Y coordinate
 * @param size Crosshair arm size
 * @param color Crosshair color
 * @param[out] id_out Assigned overlay ID
 * @return VISION_OK on success
 */
VisionResult vision_add_crosshair(
    int16_t x, int16_t y,
    int16_t size,
    VisionRgbaColor color,
    VisionOverlayId* id_out
);

/**
 * @brief Remove an overlay by ID.
 *
 * @param id Overlay ID to remove
 * @return VISION_OK on success, VISION_ERROR_OVERLAY_NOT_FOUND if not found
 */
VisionResult vision_remove_overlay(VisionOverlayId id);

/**
 * @brief Set overlay visibility.
 *
 * @param id Overlay ID
 * @param visible Non-zero for visible
 * @return VISION_OK on success
 */
VisionResult vision_set_overlay_visible(VisionOverlayId id, int visible);

/**
 * @brief Clear all overlays.
 *
 * @return VISION_OK on success
 */
VisionResult vision_clear_overlays(void);

/**
 * @brief Get number of overlays.
 *
 * @return Number of overlays
 */
size_t vision_get_overlay_count(void);

// ─────────────────────────────────────────────────────────────────────────────
// Annotation Export
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Add a detection for annotation export.
 *
 * @param detection Detection to add
 * @param class_name Human-readable class name (optional, can be NULL)
 * @return VISION_OK on success
 */
VisionResult vision_add_detection(
    const VisionDetection* detection,
    const char* class_name
);

/**
 * @brief Clear all detections.
 *
 * @return VISION_OK on success
 */
VisionResult vision_clear_detections(void);

/**
 * @brief Get number of detections.
 *
 * @return Number of detections
 */
size_t vision_get_detection_count(void);

/**
 * @brief Export detections as YOLO format.
 *
 * YOLO format: <class_id> <center_x> <center_y> <width> <height>
 * All coordinates normalized (0-1).
 *
 * @param image_width Image width for normalization
 * @param image_height Image height for normalization
 * @param include_confidence Include confidence score (non-standard)
 * @param[out] buffer_out Output buffer for text
 * @param buffer_size Size of output buffer
 * @param[out] actual_size Actual output size
 * @return VISION_OK on success
 */
VisionResult vision_export_yolo(
    int32_t image_width,
    int32_t image_height,
    int include_confidence,
    char* buffer_out,
    size_t buffer_size,
    size_t* actual_size
);

/**
 * @brief Export detections as COCO JSON format.
 *
 * @param image_id Image ID for the annotation
 * @param image_filename Image filename (optional, can be NULL)
 * @param image_width Image width
 * @param image_height Image height
 * @param[out] buffer_out Output buffer for JSON
 * @param buffer_size Size of output buffer
 * @param[out] actual_size Actual output size
 * @return VISION_OK on success
 */
VisionResult vision_export_coco(
    int32_t image_id,
    const char* image_filename,
    int32_t image_width,
    int32_t image_height,
    char* buffer_out,
    size_t buffer_size,
    size_t* actual_size
);

// ─────────────────────────────────────────────────────────────────────────────
// Utility Functions
// ─────────────────────────────────────────────────────────────────────────────

/**
 * @brief Get bytes per pixel for a format.
 *
 * @param format Pixel format
 * @return Bytes per pixel (1, 3, or 4)
 */
size_t vision_bytes_per_pixel(VisionPixelFormat format);

/**
 * @brief Calculate IoU (Intersection over Union) between two boxes.
 *
 * @param a First bounding box
 * @param b Second bounding box
 * @return IoU value (0-1)
 */
float vision_iou(const VisionBBox* a, const VisionBBox* b);

/**
 * @brief Apply Non-Maximum Suppression to detections.
 *
 * Filters overlapping detections based on IoU threshold.
 *
 * @param iou_threshold IoU threshold for suppression (default: 0.5)
 * @return VISION_OK on success
 */
VisionResult vision_apply_nms(float iou_threshold);

/**
 * @brief Filter detections by confidence threshold.
 *
 * Removes detections below the threshold.
 *
 * @param min_confidence Minimum confidence threshold
 * @return VISION_OK on success
 */
VisionResult vision_filter_by_confidence(float min_confidence);

/**
 * @brief Get last error message.
 *
 * @return Error message string (static, do not free)
 */
const char* vision_get_last_error(void);

/**
 * @brief Get vision API version.
 *
 * @return Version string (e.g., "1.0.0")
 */
const char* vision_get_version(void);

#ifdef __cplusplus
}
#endif

#endif /* AIBOX_FFI_VISION_H */
