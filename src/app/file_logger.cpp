// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Structured JSON file logger implementation.

#include "app/file_logger.h"

#include <chrono>
#include <cstring>
#include <ctime>
#include <filesystem>

#if defined(_WIN32)
#  ifndef WIN32_LEAN_AND_MEAN
#    define WIN32_LEAN_AND_MEAN
#  endif
#  include <windows.h>
#  include <aclapi.h>
#  include <sddl.h>
#else
#  include <sys/stat.h>
#endif

namespace legends {

const char* logLevelToString(LogLevel level) {
    switch (level) {
        case LogLevel::Debug:   return "DEBUG";
        case LogLevel::Info:    return "INFO";
        case LogLevel::Warning: return "WARNING";
        case LogLevel::Error:   return "ERROR";
        case LogLevel::Fatal:   return "FATAL";
    }
    return "UNKNOWN";
}

LogLevel parseLogLevel(const char* str) {
    if (!str) return LogLevel::Info;
    if (std::strcmp(str, "debug") == 0 || std::strcmp(str, "DEBUG") == 0)
        return LogLevel::Debug;
    if (std::strcmp(str, "info") == 0 || std::strcmp(str, "INFO") == 0)
        return LogLevel::Info;
    if (std::strcmp(str, "warning") == 0 || std::strcmp(str, "WARNING") == 0 ||
        std::strcmp(str, "warn") == 0 || std::strcmp(str, "WARN") == 0)
        return LogLevel::Warning;
    if (std::strcmp(str, "error") == 0 || std::strcmp(str, "ERROR") == 0)
        return LogLevel::Error;
    if (std::strcmp(str, "fatal") == 0 || std::strcmp(str, "FATAL") == 0)
        return LogLevel::Fatal;
    return LogLevel::Info;
}

FileLogger::FileLogger() = default;

FileLogger::~FileLogger() {
    close();
}

bool FileLogger::open(const std::string& path) {
    std::lock_guard<std::mutex> lock(mutex_);

    if (file_) {
        std::fclose(file_);
        file_ = nullptr;
    }

    // Create parent directories
    std::filesystem::path p(path);
    auto parent = p.parent_path();
    if (!parent.empty()) {
        std::error_code ec;
        std::filesystem::create_directories(parent, ec);
        if (ec) return false;
    }

    file_ = std::fopen(path.c_str(), "ab");
    if (!file_) return false;

    path_ = path;

    // Determine current size
    std::fseek(file_, 0, SEEK_END);
    current_size_ = static_cast<size_t>(std::ftell(file_));

    // Set restrictive permissions
    setFilePermissions(path);

    return true;
}

void FileLogger::close() {
    std::lock_guard<std::mutex> lock(mutex_);
    if (file_) {
        std::fclose(file_);
        file_ = nullptr;
    }
    current_size_ = 0;
}

void FileLogger::log(LogLevel level, const char* message) {
    if (level < min_level_) return;
    if (!message) return;

    std::lock_guard<std::mutex> lock(mutex_);
    if (!file_) return;

    rotateIfNeeded();

    // Timestamp: ISO 8601
    auto now = std::chrono::system_clock::now();
    auto time_t_now = std::chrono::system_clock::to_time_t(now);
    auto ms = std::chrono::duration_cast<std::chrono::milliseconds>(
        now.time_since_epoch()) % 1000;

    struct tm tm_buf;
#if defined(_WIN32)
    gmtime_s(&tm_buf, &time_t_now);
#else
    gmtime_r(&time_t_now, &tm_buf);
#endif

    char ts[32];
    std::strftime(ts, sizeof(ts), "%Y-%m-%dT%H:%M:%S", &tm_buf);

    // Escape message for JSON: escape backslash, double-quote, and control chars
    std::string escaped;
    escaped.reserve(std::strlen(message) + 16);
    for (const char* p = message; *p; ++p) {
        switch (*p) {
            case '"':  escaped += "\\\""; break;
            case '\\': escaped += "\\\\"; break;
            case '\n': escaped += "\\n";  break;
            case '\r': escaped += "\\r";  break;
            case '\t': escaped += "\\t";  break;
            default:
                if (static_cast<unsigned char>(*p) < 0x20) {
                    char buf[8];
                    std::snprintf(buf, sizeof(buf), "\\u%04x",
                                  static_cast<unsigned char>(*p));
                    escaped += buf;
                } else {
                    escaped += *p;
                }
                break;
        }
    }

    int written = std::fprintf(file_,
        "{\"ts\":\"%s.%03dZ\",\"level\":\"%s\",\"msg\":\"%s\"}\n",
        ts, static_cast<int>(ms.count()),
        logLevelToString(level), escaped.c_str());

    if (written > 0) {
        current_size_ += static_cast<size_t>(written);
    }
}

void FileLogger::flush() {
    std::lock_guard<std::mutex> lock(mutex_);
    if (file_) {
        std::fflush(file_);
    }
}

void FileLogger::engineLogCallback(int level, const char* message, void* userdata) {
    auto* logger = static_cast<FileLogger*>(userdata);
    if (!logger) return;

    LogLevel ll = LogLevel::Info;
    if (level >= 3)      ll = LogLevel::Error;
    else if (level >= 2) ll = LogLevel::Warning;
    else if (level >= 1) ll = LogLevel::Debug;

    logger->log(ll, message);
}

void FileLogger::rotateIfNeeded() {
    // Caller holds mutex_
    if (current_size_ < kMaxFileSize) return;
    performRotation();
}

void FileLogger::performRotation() {
    // Caller holds mutex_
    if (file_) {
        std::fclose(file_);
        file_ = nullptr;
    }

    // Rotate: .4 → delete, .3 → .4, .2 → .3, .1 → .2, current → .1
    std::error_code ec;
    std::string oldest = rotatedPath(kMaxFiles - 1);
    std::filesystem::remove(oldest, ec);
    if (ec) {
        std::fprintf(stderr, "Warning: log rotation: failed to remove %s: %s\n",
                     oldest.c_str(), ec.message().c_str());
    }

    for (int i = kMaxFiles - 2; i >= 1; --i) {
        std::string src = rotatedPath(i);
        std::string dst = rotatedPath(i + 1);
        std::filesystem::rename(src, dst, ec);
        // Ignore ENOENT — file may not exist yet
    }

    // Current → .1
    std::filesystem::rename(path_, rotatedPath(1), ec);
    if (ec) {
        std::fprintf(stderr, "Warning: log rotation: failed to rename %s → %s: %s\n",
                     path_.c_str(), rotatedPath(1).c_str(), ec.message().c_str());
    }

    // Reopen fresh file
    file_ = std::fopen(path_.c_str(), "wb");
    current_size_ = 0;

    if (file_) {
        setFilePermissions(path_);
    } else {
        std::fprintf(stderr, "Warning: log rotation: failed to reopen %s\n",
                     path_.c_str());
    }
}

std::string FileLogger::rotatedPath(int index) const {
    return path_ + "." + std::to_string(index);
}

void FileLogger::setFilePermissions(const std::string& filepath) {
#if defined(_WIN32)
    // Windows: restrict ACL to current user only
    PSID owner_sid = nullptr;
    HANDLE token = nullptr;
    if (!OpenProcessToken(GetCurrentProcess(), TOKEN_QUERY, &token)) return;

    DWORD size = 0;
    GetTokenInformation(token, TokenUser, nullptr, 0, &size);
    if (size == 0) { CloseHandle(token); return; }

    auto buffer = std::make_unique<uint8_t[]>(size);
    if (!GetTokenInformation(token, TokenUser, buffer.get(), size, &size)) {
        CloseHandle(token);
        return;
    }
    CloseHandle(token);

    auto* user = reinterpret_cast<TOKEN_USER*>(buffer.get());
    owner_sid = user->User.Sid;

    EXPLICIT_ACCESS_W ea = {};
    ea.grfAccessPermissions = GENERIC_READ | GENERIC_WRITE;
    ea.grfAccessMode = SET_ACCESS;
    ea.grfInheritance = NO_INHERITANCE;
    ea.Trustee.TrusteeForm = TRUSTEE_IS_SID;
    ea.Trustee.ptstrName = static_cast<LPWSTR>(static_cast<void*>(owner_sid));

    PACL acl = nullptr;
    if (SetEntriesInAclW(1, &ea, nullptr, &acl) == ERROR_SUCCESS) {
        // Convert UTF-8 filepath to UTF-16 using MultiByteToWideChar for
        // correct handling of non-ASCII characters (the previous
        // std::wstring(begin,end) constructor only works for ASCII).
        int wlen = MultiByteToWideChar(CP_UTF8, 0, filepath.c_str(),
                                       static_cast<int>(filepath.size()),
                                       nullptr, 0);
        std::wstring wpath(static_cast<size_t>(wlen), L'\0');
        MultiByteToWideChar(CP_UTF8, 0, filepath.c_str(),
                            static_cast<int>(filepath.size()),
                            wpath.data(), wlen);
        SetNamedSecurityInfoW(
            const_cast<wchar_t*>(wpath.c_str()),
            SE_FILE_OBJECT,
            DACL_SECURITY_INFORMATION | PROTECTED_DACL_SECURITY_INFORMATION,
            nullptr, nullptr, acl, nullptr);
        LocalFree(acl);
    }
#else
    // Unix: 0600 — owner read/write only
    chmod(filepath.c_str(), S_IRUSR | S_IWUSR);
#endif
}

} // namespace legends
