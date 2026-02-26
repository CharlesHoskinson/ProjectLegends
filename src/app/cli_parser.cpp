// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// CLI argument parser implementation.

#include "app/cli_parser.h"
#include <legends/legends_version.h>

#include <climits>
#include <cstdio>
#include <cstdlib>
#include <cstring>

namespace legends {

bool CLIOptions::parse(int argc, char** argv) {
    parse_ok = true;
    error_message.clear();

    // Guard against null argv with positive argc
    if (argc > 0 && argv == nullptr) {
        parse_ok = false;
        error_message = "argv is null";
        return false;
    }

    for (int i = 1; i < argc; ++i) {
        const char* arg = argv[i];

        if (std::strcmp(arg, "--version") == 0) {
            show_version = true;
            return true;
        }
        if (std::strcmp(arg, "--help") == 0 || std::strcmp(arg, "-h") == 0) {
            show_help = true;
            return true;
        }
        if (std::strcmp(arg, "--fullscreen") == 0) {
            fullscreen = true;
            continue;
        }
        if (std::strcmp(arg, "--log") == 0) {
            log_enabled = true;
            continue;
        }
        if (std::strcmp(arg, "--conf") == 0) {
            if (i + 1 >= argc) {
                parse_ok = false;
                error_message = "--conf requires a path argument";
                return false;
            }
            conf_path = argv[++i];
            continue;
        }
        if (std::strcmp(arg, "--cycles") == 0) {
            if (i + 1 >= argc) {
                parse_ok = false;
                error_message = "--cycles requires a numeric argument";
                return false;
            }
            char* end = nullptr;
            unsigned long val = std::strtoul(argv[++i], &end, 10);
            if (end == argv[i] || *end != '\0') {
                parse_ok = false;
                error_message = "--cycles: invalid number";
                return false;
            }
            if (val > UINT32_MAX) {
                parse_ok = false;
                error_message = "--cycles: value out of range";
                return false;
            }
            cycles = static_cast<uint32_t>(val);
            continue;
        }
        if (std::strcmp(arg, "--machine") == 0) {
            if (i + 1 >= argc) {
                parse_ok = false;
                error_message = "--machine requires a type argument";
                return false;
            }
            machine_type = argv[++i];
            machine_type_explicit = true;
            continue;
        }
        if (std::strcmp(arg, "--memsize") == 0) {
            if (i + 1 >= argc) {
                parse_ok = false;
                error_message = "--memsize requires a numeric argument";
                return false;
            }
            char* end = nullptr;
            unsigned long val = std::strtoul(argv[++i], &end, 10);
            if (end == argv[i] || *end != '\0') {
                parse_ok = false;
                error_message = "--memsize: invalid number";
                return false;
            }
            if (val > UINT32_MAX) {
                parse_ok = false;
                error_message = "--memsize: value out of range";
                return false;
            }
            memsize_kb = static_cast<uint32_t>(val);
            continue;
        }
        if (std::strcmp(arg, "--profile") == 0) {
            if (i + 1 >= argc) {
                parse_ok = false;
                error_message = "--profile requires a name argument";
                return false;
            }
            profile = argv[++i];
            continue;
        }

        // Unknown flag
        if (arg[0] == '-') {
            parse_ok = false;
            error_message = std::string("Unknown option: ") + arg;
            return false;
        }

        // Positional: program to run
        if (program.empty()) {
            program = arg;
        } else {
            parse_ok = false;
            error_message = std::string("Unexpected argument: ") + arg;
            return false;
        }
    }

    return true;
}

void CLIOptions::printUsage(const char* program_name) {
    std::printf(
        "Usage: %s [options] [program]\n"
        "\n"
        "Options:\n"
        "  --conf <path>      Path to .conf configuration file\n"
        "  --fullscreen       Start in fullscreen mode\n"
        "  --cycles <n>       CPU cycles per millisecond (0 = auto)\n"
        "  --machine <type>   Machine type: vga, ega, cga, hercules, tandy\n"
        "  --memsize <kb>     Conventional memory size in KB (default: 640)\n"
        "  --profile <name>   Execution profile: interactive, deterministic\n"
        "  --log              Enable engine log output\n"
        "  --version          Print version and exit\n"
        "  --help, -h         Print this help and exit\n"
        "\n"
        "Positional:\n"
        "  [program]          DOS program to auto-run on startup\n",
        program_name);
}

void CLIOptions::printVersion() {
    std::printf("Project Legends %s\n", LEGENDS_VERSION_STRING);
}

} // namespace legends
