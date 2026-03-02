// SPDX-License-Identifier: MIT
//
// Tests for ProxyConnection. These verify the connection lifecycle
// and sequence ID matching using a mock server thread.

#include <gtest/gtest.h>
#include <legends_ipc/control_channel.h>
#include <legends_ipc/messages.h>
#include <string>
#include <thread>

#ifdef _WIN32
#include <windows.h>
#define GET_PID() static_cast<uint32_t>(GetCurrentProcessId())
#else
#include <unistd.h>
#define GET_PID() static_cast<uint32_t>(getpid())
#endif

using namespace legends_ipc;

static std::string pc_name(const char* base) {
    static int counter = 0;
    return std::string(base) + "_" + std::to_string(GET_PID()) +
           "_" + std::to_string(counter++);
}

TEST(ProxyConnectionTest, ConnectRoundTrip) {
    auto pipe = pc_name("proxy_conn");
    auto shm = pc_name("proxy_shm");

    // Simulate what proxy_connection.cpp does: create server, wait for client
    std::thread mock_engine([&pipe]() {
        std::this_thread::sleep_for(std::chrono::milliseconds(50));
        auto client = ControlChannel::connect_client(pipe, 5000);
        ASSERT_TRUE(client.has_value());

        // Send HandshakeAck
        msg::HandshakeAck ack;
        ack.protocol_version = 1;
        ack.engine_version = 0x010000;
        ack.error_code = 0;
        std::array<uint8_t, msg::HandshakeAck::serialized_size> buf{};
        ack.serialize(buf);
        (void)client->send(MsgType::HandshakeAck, 0, buf);

        // Wait for a request and respond
        auto req = client->recv(5000);
        if (req.has_value()) {
            msg::CreateResp resp;
            resp.error_code = 0;
            std::array<uint8_t, msg::CreateResp::serialized_size> rbuf{};
            resp.serialize(rbuf);
            (void)client->send(MsgType::CreateResp, req->header.sequence_id, rbuf);
        }
    });

    // Create server side (like ProxyConnection::connect does)
    auto server = ControlChannel::create_server(pipe, 5000);
    ASSERT_TRUE(server.has_value());

    // Receive handshake ack
    auto msg = server->recv(5000);
    ASSERT_TRUE(msg.has_value());
    EXPECT_EQ(msg->header.msg_type, MsgType::HandshakeAck);

    // Send a create request
    msg::CreateReq req;
    req.deterministic = 1;
    std::array<uint8_t, msg::CreateReq::serialized_size> reqbuf{};
    req.serialize(reqbuf);
    (void)server->send(MsgType::CreateReq, 1, reqbuf);

    // Receive response
    auto resp = server->recv(5000);
    ASSERT_TRUE(resp.has_value());
    EXPECT_EQ(resp->header.msg_type, MsgType::CreateResp);
    EXPECT_EQ(resp->header.sequence_id, 1u);

    mock_engine.join();
}

TEST(ProxyConnectionTest, TimeoutOnNonExistentPipe) {
    auto client = ControlChannel::connect_client("nonexistent_pipe_12345", 200);
    EXPECT_FALSE(client.has_value());
}

TEST(ProxyConnectionTest, SequenceIdMatching) {
    auto pipe = pc_name("proxy_seq");

    std::thread mock_engine([&pipe]() {
        std::this_thread::sleep_for(std::chrono::milliseconds(50));
        auto client = ControlChannel::connect_client(pipe, 5000);
        ASSERT_TRUE(client.has_value());

        for (int i = 0; i < 3; ++i) {
            auto req = client->recv(2000);
            if (!req) break;
            // Echo back with same sequence ID
            std::array<uint8_t, 4> resp{};
            (void)client->send(MsgType::StepMsResp, req->header.sequence_id, resp);
        }
    });

    auto server = ControlChannel::create_server(pipe, 5000);
    ASSERT_TRUE(server.has_value());

    for (uint32_t seq = 1; seq <= 3; ++seq) {
        std::array<uint8_t, 4> payload{};
        (void)server->send(MsgType::StepMsReq, seq, payload);
        auto resp = server->recv(2000);
        ASSERT_TRUE(resp.has_value());
        EXPECT_EQ(resp->header.sequence_id, seq);
    }

    mock_engine.join();
}
