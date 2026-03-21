// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Shared test fixture for temporary file creation and cleanup.

#ifndef LEGENDS_TEST_UTILS_TEMP_FILE_FIXTURE_H
#define LEGENDS_TEST_UTILS_TEMP_FILE_FIXTURE_H

#include <gtest/gtest.h>

#include <cstdio>
#include <filesystem>
#include <fstream>
#include <string>
#include <vector>

namespace legends {
namespace test_utils {

// ═══════════════════════════════════════════════════════════════════════════════
// TempFileFixture: Base class that provides writeTempFile() + auto-cleanup
// ═══════════════════════════════════════════════════════════════════════════════

class TempFileFixture : public ::testing::Test {
protected:
    void TearDown() override {
        for (auto& f : temp_files_) {
            std::filesystem::remove(f);
        }
    }

    /// Write content to a temporary file and return its path.
    /// The file is automatically cleaned up in TearDown().
    std::string writeTempFile(const std::string& content,
                              const std::string& prefix = "test_tmp") {
        auto path = std::filesystem::temp_directory_path() /
                    (prefix + "_" + std::to_string(counter_++) + ".conf");
        std::ofstream out(path, std::ios::binary);
        out << content;
        out.close();
        auto s = path.string();
        temp_files_.push_back(s);
        return s;
    }

private:
    std::vector<std::string> temp_files_;
    static inline int counter_ = 0;
};

// ═══════════════════════════════════════════════════════════════════════════════
// ScopedTempDir: RAII class that creates a temp directory in the constructor
// and removes it (recursively) in the destructor.
// ═══════════════════════════════════════════════════════════════════════════════

class ScopedTempDir {
public:
    explicit ScopedTempDir(const std::string& prefix = "test_dir") {
        static int dir_counter = 0;
        path_ = std::filesystem::temp_directory_path() /
                (prefix + "_" + std::to_string(dir_counter++));
        std::filesystem::create_directories(path_);
    }

    ~ScopedTempDir() {
        std::error_code ec;
        std::filesystem::remove_all(path_, ec);
    }

    // Non-copyable, movable
    ScopedTempDir(const ScopedTempDir&) = delete;
    ScopedTempDir& operator=(const ScopedTempDir&) = delete;
    ScopedTempDir(ScopedTempDir&& other) noexcept : path_(std::move(other.path_)) {
        other.path_.clear();
    }
    ScopedTempDir& operator=(ScopedTempDir&& other) noexcept {
        if (this != &other) {
            std::error_code ec;
            if (!path_.empty()) std::filesystem::remove_all(path_, ec);
            path_ = std::move(other.path_);
            other.path_.clear();
        }
        return *this;
    }

    const std::filesystem::path& path() const { return path_; }
    std::string string() const { return path_.string(); }

private:
    std::filesystem::path path_;
};

} // namespace test_utils
} // namespace legends

#endif // LEGENDS_TEST_UTILS_TEMP_FILE_FIXTURE_H
