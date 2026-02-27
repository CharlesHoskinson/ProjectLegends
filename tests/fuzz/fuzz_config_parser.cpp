// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// libFuzzer target for ConfigParser.
// Exercises all parsing paths with arbitrary input.

#include "app/config_parser.h"

#ifdef _WIN32
#  ifndef WIN32_LEAN_AND_MEAN
#    define WIN32_LEAN_AND_MEAN
#  endif
#  include <windows.h>
#endif

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <string>

// ConfigParser only supports loadFile(), so we write the fuzz input to a
// temporary file and load it.  The file is created once per process in /tmp
// (or the platform equivalent) and overwritten for each fuzz iteration.

static const char* getTempPath() {
#if defined(_WIN32)
    static char buf[MAX_PATH + 1] = {};
    if (buf[0] == '\0') {
        char tmpdir[MAX_PATH];
        GetTempPathA(MAX_PATH, tmpdir);
        snprintf(buf, sizeof(buf), "%sfuzz_config_parser.conf", tmpdir);
    }
    return buf;
#else
    return "/tmp/fuzz_config_parser.conf";
#endif
}

extern "C" int LLVMFuzzerTestOneInput(const uint8_t* data, size_t size) {
    // Write fuzz input to temp file
    const char* path = getTempPath();
    std::FILE* f = std::fopen(path, "wb");
    if (!f) return 0;
    std::fwrite(data, 1, size, f);
    std::fclose(f);

    // Parse the config file — must not crash
    legends::ConfigParser parser;
    parser.loadFile(path);

    // Exercise all accessor paths (must not crash regardless of input)
    parser.hasSection("dosbox");
    parser.hasSection("cpu");
    parser.hasSection("render");
    parser.hasKey("dosbox", "machine");
    parser.hasKey("cpu", "cycles");
    parser.hasKey("render", "fullscreen");

    parser.get("dosbox", "machine", "vga");
    parser.get("cpu", "cycles", "0");
    parser.get("render", "renderer", "software");

    parser.getInt("cpu", "cycles", 0);
    parser.getInt("dosbox", "memsize", 640);

    parser.getBool("render", "fullscreen", false);
    parser.getBool("dosbox", "autoexec", false);

    parser.getLoadedPath();

    // Clean up temp file to avoid leaking disk space across iterations
    std::remove(path);

    return 0;
}
