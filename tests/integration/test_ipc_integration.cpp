// SPDX-License-Identifier: MIT
//
// Full end-to-end IPC integration test.
// Requires LEGENDS_USE_IPC=ON and a built legends_engine_host.
//
// Flow: spawn engine host -> handshake -> create -> step -> destroy -> shutdown

#include <gtest/gtest.h>
#include <legends_ipc/engine_spawner.h>
#include <legends_ipc/control_channel.h>
#include <legends_ipc/framebuffer_shm.h>
#include <legends_ipc/audio_ring.h>
#include <legends_ipc/messages.h>
#include <thread>
#include <chrono>
#include <string>

#ifdef _WIN32
#include <windows.h>
#define GET_PID() static_cast<uint32_t>(GetCurrentProcessId())
#else
#include <unistd.h>
#define GET_PID() static_cast<uint32_t>(getpid())
#endif

using namespace legends_ipc;

class IpcIntegrationTest : public ::testing::Test {
protected:
    std::string pipe_name_;
    std::string shm_name_;

    void SetUp() override {
        auto pid = GET_PID();
        pipe_name_ = "ipc_integ_" + std::to_string(pid);
        shm_name_ = "ipc_integ_shm_" + std::to_string(pid);
    }
};

// This test requires the engine host binary to be available.
// Skip gracefully if it's not found.
TEST_F(IpcIntegrationTest, DISABLED_FullE2E) {
    // Find engine host (relative to build dir)
    std::string engine_path = "./legends_engine_host";
#ifdef _WIN32
    engine_path = ".\\legends_engine_host.exe";
#endif

    // Create shared memory
    auto fb = FramebufferShm::create(shm_name_, 640, 480);
    ASSERT_TRUE(fb.has_value());

    auto audio = AudioRingBuffer::create(shm_name_, 2048, 2, 44100);
    ASSERT_TRUE(audio.has_value());

    // Start pipe server in background
    std::thread server_thread([this, &engine_path]() {
        // Spawn engine host
        SpawnConfig config;
        config.executable_path = engine_path;
        config.pipe_name = pipe_name_;
        config.shm_name = shm_name_;

        auto proc = EngineSpawner::spawn(config);
        if (!proc.has_value()) {
            GTEST_SKIP() << "Engine host not found at " << engine_path;
            return;
        }

        // Wait for it to exit
        auto exit_result = proc->wait_for_exit(30000);
        (void)exit_result;
    });

    // Create pipe server and wait for connection
    auto channel = ControlChannel::create_server(pipe_name_, 10000);
    if (!channel.has_value()) {
        server_thread.join();
        GTEST_SKIP() << "Failed to create pipe server";
        return;
    }

    // Wait for HandshakeAck
    auto ack_msg = channel->recv(5000);
    ASSERT_TRUE(ack_msg.has_value());
    EXPECT_EQ(ack_msg->header.msg_type, MsgType::HandshakeAck);

    // Send Create
    msg::CreateReq create_req;
    create_req.deterministic = 1;
    std::vector<uint8_t> cbuf(msg::CreateReq::serialized_size);
    create_req.serialize(cbuf);
    auto create_send = channel->send(MsgType::CreateReq, 1, cbuf);
    ASSERT_TRUE(create_send.has_value());

    auto create_resp = channel->recv(5000);
    ASSERT_TRUE(create_resp.has_value());
    EXPECT_EQ(create_resp->header.msg_type, MsgType::CreateResp);

    // Send StepMs
    msg::StepMsReq step_req;
    step_req.ms = 10;
    std::vector<uint8_t> sbuf(msg::StepMsReq::serialized_size);
    step_req.serialize(sbuf);
    auto step_send = channel->send(MsgType::StepMsReq, 2, sbuf);
    ASSERT_TRUE(step_send.has_value());

    auto step_resp = channel->recv(5000);
    ASSERT_TRUE(step_resp.has_value());
    EXPECT_EQ(step_resp->header.msg_type, MsgType::StepMsResp);

    // Send Destroy
    auto destroy_send = channel->send(MsgType::DestroyReq, 3, {});
    ASSERT_TRUE(destroy_send.has_value());
    auto destroy_resp = channel->recv(5000);
    ASSERT_TRUE(destroy_resp.has_value());

    // Send Shutdown
    msg::ShutdownMsg shutdown;
    shutdown.reason = 0;
    std::vector<uint8_t> shutbuf(msg::ShutdownMsg::serialized_size);
    shutdown.serialize(shutbuf);
    auto shutdown_send = channel->send(MsgType::Shutdown, 4, shutbuf);
    ASSERT_TRUE(shutdown_send.has_value());

    auto shutdown_resp = channel->recv(5000);
    ASSERT_TRUE(shutdown_resp.has_value());

    server_thread.join();
}
