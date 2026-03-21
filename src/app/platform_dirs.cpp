// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Platform-specific directory resolution implementation.

#include "app/platform_dirs.h"

#include <cstdlib>

#if defined(_WIN32)
#  ifndef WIN32_LEAN_AND_MEAN
#    define WIN32_LEAN_AND_MEAN
#  endif
#  include <windows.h>
#  include <shlobj.h>
#  pragma comment(lib, "shell32.lib")
#  pragma comment(lib, "ole32.lib")
#endif

namespace legends {

#if defined(_WIN32)

// ── Windows ──────────────────────────────────────────────────────────────────

static std::string getKnownFolderPath(const KNOWNFOLDERID& folder_id) {
    PWSTR path = nullptr;
    HRESULT hr = SHGetKnownFolderPath(folder_id, 0, nullptr, &path);
    if (SUCCEEDED(hr) && path) {
        // Scope guard ensures CoTaskMemFree is always called, even if
        // std::string allocation throws std::bad_alloc.
        struct CoTaskMemGuard {
            PWSTR ptr;
            ~CoTaskMemGuard() { if (ptr) CoTaskMemFree(ptr); }
        } guard{path};

        // Convert wide string to UTF-8
        int len = WideCharToMultiByte(CP_UTF8, 0, path, -1, nullptr, 0, nullptr, nullptr);
        if (len > 0) {
            std::string result(static_cast<size_t>(len - 1), '\0');
            WideCharToMultiByte(CP_UTF8, 0, path, -1, result.data(), len, nullptr, nullptr);
            return result;
        }
    }
    return {};
}

std::string getConfigDir() {
    std::string base = getKnownFolderPath(FOLDERID_RoamingAppData);
    if (base.empty()) return {};
    return base + "\\ProjectLegends";
}

std::string getDataDir() {
    std::string base = getKnownFolderPath(FOLDERID_RoamingAppData);
    if (base.empty()) return {};
    return base + "\\ProjectLegends";
}

std::string getCacheDir() {
    std::string base = getKnownFolderPath(FOLDERID_LocalAppData);
    if (base.empty()) return {};
    return base + "\\ProjectLegends";
}

#elif defined(__APPLE__)

// ── macOS ────────────────────────────────────────────────────────────────────

static std::string getHomeDir() {
    const char* home = std::getenv("HOME");
    return home ? std::string(home) : std::string();
}

std::string getConfigDir() {
    std::string home = getHomeDir();
    if (home.empty()) return {};
    return home + "/Library/Preferences/ProjectLegends";
}

std::string getDataDir() {
    std::string home = getHomeDir();
    if (home.empty()) return {};
    return home + "/Library/Application Support/ProjectLegends";
}

std::string getCacheDir() {
    std::string home = getHomeDir();
    if (home.empty()) return {};
    return home + "/Library/Caches/ProjectLegends";
}

#else

// ── Linux / POSIX ────────────────────────────────────────────────────────────

static std::string getHomeDir() {
    const char* home = std::getenv("HOME");
    return home ? std::string(home) : std::string();
}

static std::string xdgDir(const char* env_var, const char* fallback_suffix) {
    const char* val = std::getenv(env_var);
    if (val && val[0] != '\0') {
        return std::string(val) + "/projectlegends";
    }
    std::string home = getHomeDir();
    if (home.empty()) return {};
    return home + fallback_suffix + "/projectlegends";
}

std::string getConfigDir() {
    return xdgDir("XDG_CONFIG_HOME", "/.config");
}

std::string getDataDir() {
    return xdgDir("XDG_DATA_HOME", "/.local/share");
}

std::string getCacheDir() {
    return xdgDir("XDG_CACHE_HOME", "/.cache");
}

#endif

std::string getLogDir() {
    std::string cache = getCacheDir();
    if (cache.empty()) return {};
#if defined(_WIN32)
    return cache + "\\logs";
#else
    return cache + "/logs";
#endif
}

} // namespace legends
