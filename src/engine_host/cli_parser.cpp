// SPDX-License-Identifier: GPL-2.0-or-later
#include "cli_parser.h"
#include <cstring>

namespace legends::engine_host {

std::expected<CliArgs, CliError> parse_cli(int argc, const char* const* argv) {
    CliArgs args;

    for (int i = 1; i < argc; ++i) {
        if (std::strcmp(argv[i], "--version") == 0) {
            args.version = true;
            return args;
        } else if (std::strcmp(argv[i], "--pipe") == 0) {
            if (i + 1 >= argc) return std::unexpected(CliError::MissingPipe);
            args.pipe_name = argv[++i];
        } else if (std::strcmp(argv[i], "--shm") == 0) {
            if (i + 1 >= argc) return std::unexpected(CliError::MissingShm);
            args.shm_name = argv[++i];
        } else {
            return std::unexpected(CliError::UnknownFlag);
        }
    }

    if (!args.version) {
        if (args.pipe_name.empty()) return std::unexpected(CliError::MissingPipe);
        if (args.shm_name.empty()) return std::unexpected(CliError::MissingShm);
    }

    return args;
}

} // namespace legends::engine_host
