// SPDX-License-Identifier: GPL-2.0-or-later
//
// legends_engine_host: GPL-licensed child process that runs the DOSBox-X
// engine and communicates with the application shell via IPC.

#include "cli_parser.h"
#include "engine_dispatcher.h"
#include <legends_ipc/control_channel.h>
#include <legends_ipc/framebuffer_shm.h>
#include <legends_ipc/audio_ring.h>
#include <legends_ipc/messages.h>
#include <legends/legends_embed.h>
#include <cstdio>
#include <cstdlib>

namespace legends::engine_host {
void print_version();
}

int main(int argc, char* argv[]) {
    using namespace legends::engine_host;
    using namespace legends_ipc;

    auto args = parse_cli(argc, argv);
    if (!args.has_value()) {
        switch (args.error()) {
        case CliError::MissingPipe:
            std::fprintf(stderr, "Error: --pipe <name> is required\n");
            return 1;
        case CliError::MissingShm:
            std::fprintf(stderr, "Error: --shm <name> is required\n");
            return 1;
        case CliError::UnknownFlag:
            std::fprintf(stderr, "Error: unknown flag\n");
            return 1;
        default:
            return 1;
        }
    }

    if (args->version) {
        print_version();
        return 0;
    }

    // Connect to named pipe as client
    auto channel = ControlChannel::connect_client(args->pipe_name, 5000);
    if (!channel.has_value()) {
        std::fprintf(stderr, "Error: failed to connect to pipe '%s'\n",
                     args->pipe_name.c_str());
        return 1;
    }

    // Send HandshakeAck
    msg::HandshakeAck ack;
    ack.protocol_version = 1;
    ack.engine_version = LEGENDS_API_VERSION;
    ack.error_code = 0;

    std::array<uint8_t, msg::HandshakeAck::serialized_size> ack_buf{};
    ack.serialize(ack_buf);
    channel->send(MsgType::HandshakeAck, 0, ack_buf);

    // Message loop
    while (channel->is_connected()) {
        auto msg = channel->recv(5000);
        if (!msg.has_value()) {
            if (msg.error() == IpcError::Timeout ||
                msg.error() == IpcError::BufferTooSmall) {
                continue; // keep waiting
            }
            break; // broken pipe or error
        }

        auto result = dispatch(msg->header.msg_type, msg->payload);
        if (!result.has_value()) {
            msg::ErrorResponseMsg err;
            err.error_code = LEGENDS_ERR_INTERNAL;
            std::array<uint8_t, 4> err_buf{};
            err.serialize(err_buf);
            channel->send(MsgType::ErrorResponse, msg->header.sequence_id, err_buf);
            continue;
        }

        channel->send(result->response_type, msg->header.sequence_id, result->payload);

        // Check for shutdown
        if (msg->header.msg_type == MsgType::Shutdown) {
            break;
        }
    }

    return 0;
}
