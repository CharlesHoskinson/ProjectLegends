// SPDX-License-Identifier: GPL-2.0-or-later
// Stub implementations for VideoCodec when the full ZMBV codec (and its zlib
// dependency) is unavailable (e.g. unit-test builds without C_SSHOT).
// These stubs allow the test binary to link; the real implementations live in
// zmbv.cpp, guarded by #if (C_SSHOT).

#include "config.h"

#if !(C_SSHOT)

#include "zmbv/zmbv.h"
#include <cstring>

void Msg(const char [], ...) {}

VideoCodec::VideoCodec()
    : VectorCount(0), oldframe(nullptr), newframe(nullptr),
      buf1(nullptr), buf2(nullptr), work(nullptr), bufsize(0),
      blockcount(0), blocks(nullptr), workUsed(0), workPos(0),
      palsize(0), height(0), width(0), pitch(0),
      format(ZMBV_FORMAT_NONE), pixelsize(0) {
    std::memset(&compress, 0, sizeof(compress));
    std::memset(palette, 0, sizeof(palette));
    std::memset(&zstream, 0, sizeof(zstream));
}

bool VideoCodec::SetupCompress(int, int)   { return true; }
bool VideoCodec::SetupDecompress(int, int) { return true; }
zmbv_format_t VideoCodec::BPPFormat(int bpp) {
    switch (bpp) {
        case 8:  return ZMBV_FORMAT_8BPP;
        case 15: return ZMBV_FORMAT_15BPP;
        case 16: return ZMBV_FORMAT_16BPP;
        case 24: return ZMBV_FORMAT_24BPP;
        case 32: return ZMBV_FORMAT_32BPP;
        default: return ZMBV_FORMAT_NONE;
    }
}
int VideoCodec::NeededSize(int _width, int _height, zmbv_format_t) {
    // Return a generous buffer estimate (header + raw frame + overhead)
    return _width * _height * 4 + 1024;
}

void VideoCodec::CompressLines(int, void *[]) {}
bool VideoCodec::PrepareCompressFrame(int, zmbv_format_t, char *, void *, int) { return true; }
int  VideoCodec::FinishCompressFrame()    { return 64; } // pretend we wrote 64 bytes
bool VideoCodec::DecompressFrame(void *, int) { return true; }
void VideoCodec::Output_UpsideDown_24(void *) {}

#endif // !(C_SSHOT)
