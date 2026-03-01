// SPDX-License-Identifier: GPL-2.0-or-later
#ifndef LEGENDS_ENGINE_HOST_CLI_PARSER_H
#define LEGENDS_ENGINE_HOST_CLI_PARSER_H

#include <cstdint>
#include <expected>
#include <string>

namespace legends::engine_host {

struct CliArgs {
    std::string pipe_name;
    std::string shm_name;
    bool version = false;
};

enum class CliError : uint8_t {
    Ok,
    MissingPipe,
    MissingShm,
    UnknownFlag,
};

std::expected<CliArgs, CliError> parse_cli(int argc, const char* const* argv);

} // namespace legends::engine_host

#endif // LEGENDS_ENGINE_HOST_CLI_PARSER_H
