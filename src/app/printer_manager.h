// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Printer capture manager — manages output directory and file naming.

#pragma once

#include <cstdint>
#include <string>

namespace legends {

class PrinterManager {
public:
    /// Set output directory for printer captures.
    void setOutputDirectory(const std::string& dir);
    const std::string& outputDirectory() const { return output_dir_; }

    /// Generate next output filename (sequential numbering).
    std::string generateFilename(const std::string& extension = "prn") const;

    /// Get full path for next output file.
    std::string nextOutputPath(const std::string& extension = "prn") const;

    /// Mark that a file was written (increment counter).
    void fileWritten();

    /// Get number of files written this session.
    uint32_t filesWritten() const { return files_written_; }

    /// Check if output directory is configured and valid.
    bool isConfigured() const;

    /// Enable/disable printer capture.
    void setEnabled(bool enabled) { enabled_ = enabled; }
    bool isEnabled() const { return enabled_; }

private:
    std::string output_dir_;
    uint32_t files_written_ = 0;
    bool enabled_ = false;
};

} // namespace legends
