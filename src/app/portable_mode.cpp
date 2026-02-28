// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors

#include "app/portable_mode.h"

#include <filesystem>

#if defined(_WIN32)
#  ifndef WIN32_LEAN_AND_MEAN
#    define WIN32_LEAN_AND_MEAN
#  endif
#  include <windows.h>
#elif defined(__APPLE__)
#  include <mach-o/dyld.h>
#else
#  include <unistd.h>
#  include <climits>
#endif

namespace legends {

std::string getExecutableDir() {
#if defined(_WIN32)
    char buf[MAX_PATH];
    DWORD len = GetModuleFileNameA(nullptr, buf, MAX_PATH);
    if (len == 0 || len >= MAX_PATH) return {};
    std::filesystem::path p(buf);
    return p.parent_path().string();
#elif defined(__APPLE__)
    char buf[PATH_MAX];
    uint32_t size = sizeof(buf);
    if (_NSGetExecutablePath(buf, &size) != 0) return {};
    char resolved[PATH_MAX];
    if (!realpath(buf, resolved)) return {};
    std::filesystem::path p(resolved);
    return p.parent_path().string();
#else
    char buf[PATH_MAX];
    ssize_t len = readlink("/proc/self/exe", buf, sizeof(buf) - 1);
    if (len <= 0) return {};
    buf[len] = '\0';
    std::filesystem::path p(buf);
    return p.parent_path().string();
#endif
}

bool isPortableMode() {
    std::string dir = getExecutableDir();
    if (dir.empty()) return false;
    return std::filesystem::exists(std::filesystem::path(dir) / "portable.txt");
}

std::string getPortableBaseDir() {
    return getExecutableDir();
}

} // namespace legends
