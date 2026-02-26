// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// CLI argument parser for the interactive emulator.
// REQ-CLI-001: Command-line arguments

#pragma once

#include <cstdint>
#include <string>

namespace legends {

/// Parsed command-line options.
struct CLIOptions {
    std::string conf_path;                  // --conf <path>
    bool        fullscreen     = false;     // --fullscreen
    uint32_t    cycles         = 0;         // --cycles <n> (0 = auto)
    std::string machine_type   = "vga";     // --machine <type>
    uint32_t    memsize_kb     = 640;       // --memsize <kb>
    std::string profile        = "interactive"; // --profile <name>
    bool        log_enabled    = false;     // --log
    std::string program;                    // positional [program]

    bool        show_version   = false;     // --version (action)
    bool        show_help      = false;     // --help (action)

    bool        machine_type_explicit = false; // true if --machine was given

    bool        parse_ok       = true;      // false if parse error
    std::string error_message;              // set on parse failure

    /// Parse argc/argv. Returns true on success.
    /// On failure, sets parse_ok = false and error_message.
    bool parse(int argc, char** argv);

    /// Print usage/help text to stdout.
    static void printUsage(const char* program_name);

    /// Print version to stdout.
    static void printVersion();
};

} // namespace legends
