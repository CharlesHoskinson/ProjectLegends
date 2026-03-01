// SPDX-License-Identifier: GPL-2.0-or-later
//
// Tests for the engine dispatcher. Since the dispatcher calls legends_*()
// functions which need a full engine, these tests verify the dispatch
// routing logic with the actual API (create -> dispatch -> check response).
// The engine must be available (linked legends_core).

#include <gtest/gtest.h>
#include <legends_ipc/messages.h>
#include <legends_ipc/message_types.h>
#include <legends/legends_embed.h>
#include <vector>

// Forward declare the dispatch function
namespace legends::engine_host {
    struct DispatchResult {
        legends_ipc::MsgType response_type;
        std::vector<uint8_t> payload;
    };
    std::expected<DispatchResult, legends_ipc::IpcError>
    dispatch(legends_ipc::MsgType msg_type, std::span<const uint8_t> payload);
}

using namespace legends_ipc;
using namespace legends_ipc::msg;
using namespace legends::engine_host;

class EngineDispatcherTest : public ::testing::Test {
protected:
    void SetUp() override {
        legends_force_destroy();
    }
    void TearDown() override {
        legends_force_destroy();
    }
};

TEST_F(EngineDispatcherTest, DispatchCreate) {
    CreateReq req;
    req.memory_kb = 640;
    req.deterministic = 1;

    std::vector<uint8_t> payload(CreateReq::serialized_size);
    req.serialize(payload);

    auto result = dispatch(MsgType::CreateReq, payload);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result->response_type, MsgType::CreateResp);

    auto resp = CreateResp::deserialize(result->payload);
    ASSERT_TRUE(resp.has_value());
    EXPECT_EQ(resp->error_code, LEGENDS_OK);
}

TEST_F(EngineDispatcherTest, DispatchShutdown) {
    // Create first
    CreateReq create_req;
    create_req.deterministic = 1;
    std::vector<uint8_t> cpayload(CreateReq::serialized_size);
    create_req.serialize(cpayload);
    dispatch(MsgType::CreateReq, cpayload);

    // Shutdown
    ShutdownMsg shutdown;
    shutdown.reason = 0;
    std::vector<uint8_t> payload(ShutdownMsg::serialized_size);
    shutdown.serialize(payload);

    auto result = dispatch(MsgType::Shutdown, payload);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result->response_type, MsgType::ShutdownAck);
}

TEST_F(EngineDispatcherTest, DispatchUnknownReturnsError) {
    auto result = dispatch(static_cast<MsgType>(0xFFFF), {});
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result->response_type, MsgType::ErrorResponse);

    auto resp = ErrorResponseMsg::deserialize(result->payload);
    ASSERT_TRUE(resp.has_value());
    EXPECT_EQ(resp->error_code, LEGENDS_ERR_NOT_SUPPORTED);
}

TEST_F(EngineDispatcherTest, DispatchStepMsAfterCreate) {
    // Create
    CreateReq create_req;
    create_req.deterministic = 1;
    std::vector<uint8_t> cpayload(CreateReq::serialized_size);
    create_req.serialize(cpayload);
    dispatch(MsgType::CreateReq, cpayload);

    // Step
    StepMsReq step_req;
    step_req.ms = 10;
    std::vector<uint8_t> spayload(StepMsReq::serialized_size);
    step_req.serialize(spayload);

    auto result = dispatch(MsgType::StepMsReq, spayload);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result->response_type, MsgType::StepMsResp);

    auto resp = StepMsResp::deserialize(result->payload);
    ASSERT_TRUE(resp.has_value());
    EXPECT_EQ(resp->error_code, LEGENDS_OK);
}

TEST_F(EngineDispatcherTest, DispatchHeartbeat) {
    HeartbeatMsg hb;
    hb.timestamp_us = 42;
    std::vector<uint8_t> payload(HeartbeatMsg::serialized_size);
    hb.serialize(payload);

    auto result = dispatch(MsgType::Heartbeat, payload);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result->response_type, MsgType::HeartbeatAck);

    auto resp = HeartbeatAckMsg::deserialize(result->payload);
    ASSERT_TRUE(resp.has_value());
    EXPECT_EQ(resp->timestamp_us, 42u);
}
