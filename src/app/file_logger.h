// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Structured JSON file logger with rotation.

#pragma once

#include <cstdio>
#include <mutex>
#include <string>

namespace legends {

enum class LogLevel { Debug, Info, Warning, Error, Fatal };

[[nodiscard]] const char* logLevelToString(LogLevel level);
[[nodiscard]] LogLevel    parseLogLevel(const char* str);

class FileLogger {
public:
    FileLogger();
    ~FileLogger();

    FileLogger(const FileLogger&)            = delete;
    FileLogger& operator=(const FileLogger&) = delete;

    [[nodiscard]] bool open(const std::string& path);
    void close();
    void log(LogLevel level, const char* message);
    void flush();

    void setMinLevel(LogLevel level) { min_level_ = level; }
    [[nodiscard]] bool isOpen() const { return file_ != nullptr; }

    static void engineLogCallback(int level, const char* message, void* userdata);

private:
    static constexpr size_t kMaxFileSize = 10 * 1024 * 1024; // 10 MB
    static constexpr int    kMaxFiles    = 5;

    void        rotateIfNeeded();
    void        performRotation();
    [[nodiscard]] std::string rotatedPath(int index) const;
    void        setFilePermissions(const std::string& filepath);

    std::mutex  mutex_;
    std::FILE*  file_         = nullptr;
    std::string path_;
    size_t      current_size_ = 0;
    LogLevel    min_level_    = LogLevel::Info;
};

} // namespace legends
