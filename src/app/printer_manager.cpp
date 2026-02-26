// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// Printer capture manager implementation.

#include "app/printer_manager.h"

#include <iomanip>
#include <sstream>

namespace legends {

void PrinterManager::setOutputDirectory(const std::string& dir) {
    output_dir_ = dir;
}

std::string PrinterManager::generateFilename(const std::string& extension) const {
    std::ostringstream oss;
    oss << "print_"
        << std::setw(4) << std::setfill('0') << files_written_;
    if (!extension.empty()) {
        oss << '.' << extension;
    }
    return oss.str();
}

std::string PrinterManager::nextOutputPath(const std::string& extension) const {
    return output_dir_ + "/" + generateFilename(extension);
}

void PrinterManager::fileWritten() {
    ++files_written_;
}

bool PrinterManager::isConfigured() const {
    return !output_dir_.empty();
}

} // namespace legends
