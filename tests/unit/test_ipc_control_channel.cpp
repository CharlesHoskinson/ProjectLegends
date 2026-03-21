// SPDX-License-Identifier: MIT
#include <gtest/gtest.h>
#include <legends_ipc/control_channel.h>
#include <legends_ipc/messages.h>
#include "test_utils/ipc_test_helpers.h"
#include <array>
#include <string>
#include <thread>

using namespace legends_ipc;
using legends_ipc::test_utils::ipc_test_unique_name;

static std::string cc_name(const char* base) {
    return ipc_test_unique_name(base);
}

TEST(IpcControlChannelTest, ServerClientConnect) {
    auto name = cc_name("cc_connect");

    std::thread server_thread([&name]() {
        auto server = ControlChannel::create_server(name, 5000);
        ASSERT_TRUE(server.has_value()) << "Server create failed";
        EXPECT_TRUE(server->is_connected());
    });

    // Give server a moment to start
    std::this_thread::sleep_for(std::chrono::milliseconds(50));

    auto client = ControlChannel::connect_client(name, 5000);
    ASSERT_TRUE(client.has_value()) << "Client connect failed";
    EXPECT_TRUE(client->is_connected());

    server_thread.join();
}

TEST(IpcControlChannelTest, BidirectionalSendRecv) {
    auto name = cc_name("cc_bidir");

    std::thread server_thread([&name]() {
        auto server = ControlChannel::create_server(name, 5000);
        ASSERT_TRUE(server.has_value());

        // Server receives from client
        auto msg = server->recv(2000);
        ASSERT_TRUE(msg.has_value());
        EXPECT_EQ(msg->header.msg_type, MsgType::Handshake);
        EXPECT_EQ(msg->header.sequence_id, 1u);

        // Server sends response
        std::array<uint8_t, 12> payload{};
        auto r = server->send(MsgType::HandshakeAck, 1, payload);
        EXPECT_TRUE(r.has_value());
    });

    std::this_thread::sleep_for(std::chrono::milliseconds(50));

    auto client = ControlChannel::connect_client(name, 5000);
    ASSERT_TRUE(client.has_value());

    // Client sends to server
    std::array<uint8_t, 16> payload{};
    auto r = client->send(MsgType::Handshake, 1, payload);
    EXPECT_TRUE(r.has_value());

    // Client receives from server
    auto msg = client->recv(2000);
    ASSERT_TRUE(msg.has_value());
    EXPECT_EQ(msg->header.msg_type, MsgType::HandshakeAck);

    server_thread.join();
}

TEST(IpcControlChannelTest, TimeoutOnEmpty) {
    auto name = cc_name("cc_timeout");

    std::thread server_thread([&name]() {
        auto server = ControlChannel::create_server(name, 5000);
        ASSERT_TRUE(server.has_value());

        // Try to receive with short timeout - should timeout
        auto msg = server->recv(100);
        ASSERT_FALSE(msg.has_value());
        // Either Timeout or BufferTooSmall
    });

    std::this_thread::sleep_for(std::chrono::milliseconds(50));

    auto client = ControlChannel::connect_client(name, 5000);
    ASSERT_TRUE(client.has_value());
    // Don't send anything - let server timeout

    std::this_thread::sleep_for(std::chrono::milliseconds(200));
    server_thread.join();
}

TEST(IpcControlChannelTest, PipeNameFormat) {
    auto name_win = ControlChannel::make_pipe_name(12345);
#ifdef _WIN32
    EXPECT_EQ(name_win, "\\\\.\\pipe\\legends_12345");
#else
    EXPECT_EQ(name_win, "/tmp/legends_12345.sock");
#endif
}

TEST(IpcControlChannelTest, SequentialMessages) {
    auto name = cc_name("cc_seq");

    std::thread server_thread([&name]() {
        auto server = ControlChannel::create_server(name, 5000);
        ASSERT_TRUE(server.has_value());

        for (uint32_t i = 1; i <= 5; ++i) {
            auto msg = server->recv(2000);
            ASSERT_TRUE(msg.has_value());
            EXPECT_EQ(msg->header.sequence_id, i);

            std::array<uint8_t, 4> resp{};
            (void)server->send(MsgType::StepMsResp, i, resp);
        }
    });

    std::this_thread::sleep_for(std::chrono::milliseconds(50));

    auto client = ControlChannel::connect_client(name, 5000);
    ASSERT_TRUE(client.has_value());

    for (uint32_t i = 1; i <= 5; ++i) {
        std::array<uint8_t, 4> payload{};
        (void)client->send(MsgType::StepMsReq, i, payload);
        auto msg = client->recv(2000);
        ASSERT_TRUE(msg.has_value());
        EXPECT_EQ(msg->header.sequence_id, i);
    }

    server_thread.join();
}

TEST(IpcControlChannelTest, LargePayload) {
    auto name = cc_name("cc_large");

    std::thread server_thread([&name]() {
        auto server = ControlChannel::create_server(name, 5000);
        ASSERT_TRUE(server.has_value());

        auto msg = server->recv(5000);
        ASSERT_TRUE(msg.has_value());
        EXPECT_EQ(msg->header.payload_size, 65536u);
        // Verify payload content
        for (size_t i = 0; i < 65536; ++i)
            EXPECT_EQ(msg->payload[i], static_cast<uint8_t>(i & 0xFF));
    });

    std::this_thread::sleep_for(std::chrono::milliseconds(50));

    auto client = ControlChannel::connect_client(name, 5000);
    ASSERT_TRUE(client.has_value());

    std::vector<uint8_t> payload(65536);
    for (size_t i = 0; i < 65536; ++i)
        payload[i] = static_cast<uint8_t>(i & 0xFF);

    auto r = client->send(MsgType::SaveStateResp, 42, payload);
    EXPECT_TRUE(r.has_value());

    server_thread.join();
}
