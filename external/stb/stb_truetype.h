// stb_truetype.h - v1.26 - public domain - Sean Barrett
// STUB for ProjectLegends compilation - replace with real stb_truetype.h for runtime use
#ifndef STB_INCLUDE_STB_TRUETYPE_H
#define STB_INCLUDE_STB_TRUETYPE_H

#include <stdlib.h>

typedef struct { int dummy; } stbtt_fontinfo;

#ifdef __cplusplus
extern "C" {
#endif

static inline int stbtt_InitFont(stbtt_fontinfo *info, const unsigned char *data, int offset) {
    (void)info; (void)data; (void)offset;
    return 0; // stub: always fails
}

static inline float stbtt_ScaleForPixelHeight(const stbtt_fontinfo *info, float pixels) {
    (void)info; (void)pixels;
    return 0.0f;
}

static inline void stbtt_GetFontVMetrics(const stbtt_fontinfo *info, int *ascent, int *descent, int *lineGap) {
    (void)info;
    if (ascent) *ascent = 0;
    if (descent) *descent = 0;
    if (lineGap) *lineGap = 0;
}

static inline unsigned char* stbtt_GetCodepointBitmap(const stbtt_fontinfo *info, float scale_x, float scale_y,
    int codepoint, int *width, int *height, int *xoff, int *yoff) {
    (void)info; (void)scale_x; (void)scale_y; (void)codepoint;
    if (width) *width = 0;
    if (height) *height = 0;
    if (xoff) *xoff = 0;
    if (yoff) *yoff = 0;
    return NULL;
}

static inline void stbtt_FreeBitmap(unsigned char *bitmap, void *userdata) {
    (void)userdata;
    free(bitmap);
}

static inline int stbtt_FindGlyphIndex(const stbtt_fontinfo *info, int unicode_codepoint) {
    (void)info; (void)unicode_codepoint;
    return 0;
}

static inline void stbtt_GetCodepointHMetrics(const stbtt_fontinfo *info, int codepoint, int *advanceWidth, int *leftSideBearing) {
    (void)info; (void)codepoint;
    if (advanceWidth) *advanceWidth = 0;
    if (leftSideBearing) *leftSideBearing = 0;
}

#ifdef __cplusplus
}
#endif

#endif // STB_INCLUDE_STB_TRUETYPE_H
