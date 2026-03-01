// SPDX-License-Identifier: MIT
#include <gtest/gtest.h>
#include <legends_ipc/message_header.h>
#include <array>

using namespace legends_ipc;

class IpcMessageHeaderTest : public ::testing::Test {
protected:
    std::array<uint8_t, 64> buf_{};
};

TEST_F(IpcMessageHeaderTest, RoundTrip) {
    MessageHeader h;
    h.msg_type     = MsgType::StepMsReq;
    h.payload_size = 1024;
    h.sequence_id  = 42;

    h.serialize(buf_);
    auto result = MessageHeader::deserialize(buf_);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result->msg_type, MsgType::StepMsReq);
    EXPECT_EQ(result->payload_size, 1024u);
    EXPECT_EQ(result->sequence_id, 42u);
}

TEST_F(IpcMessageHeaderTest, BufferTooSmall) {
    std::array<uint8_t, 9> small{};
    auto result = MessageHeader::deserialize(small);
    ASSERT_FALSE(result.has_value());
    EXPECT_EQ(result.error(), IpcError::BufferTooSmall);
}

TEST_F(IpcMessageHeaderTest, ZeroPayload) {
    MessageHeader h;
    h.msg_type     = MsgType::Heartbeat;
    h.payload_size = 0;
    h.sequence_id  = 0;

    h.serialize(buf_);
    auto result = MessageHeader::deserialize(buf_);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result->payload_size, 0u);
    EXPECT_EQ(result->sequence_id, 0u);
}

TEST_F(IpcMessageHeaderTest, MaxSequenceId) {
    MessageHeader h;
    h.msg_type     = MsgType::Handshake;
    h.payload_size = 0;
    h.sequence_id  = 0xFFFFFFFF;

    h.serialize(buf_);
    auto result = MessageHeader::deserialize(buf_);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result->sequence_id, 0xFFFFFFFF);
}

TEST_F(IpcMessageHeaderTest, MaxPayloadSize) {
    MessageHeader h;
    h.msg_type     = MsgType::SaveStateResp;
    h.payload_size = 0xFFFFFFFF;
    h.sequence_id  = 1;

    h.serialize(buf_);
    auto result = MessageHeader::deserialize(buf_);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result->payload_size, 0xFFFFFFFF);
}

TEST_F(IpcMessageHeaderTest, ExactSizeBuffer) {
    std::array<uint8_t, HeaderSize> exact{};
    MessageHeader h;
    h.msg_type     = MsgType::CreateReq;
    h.payload_size = 20;
    h.sequence_id  = 7;

    h.serialize(exact);
    auto result = MessageHeader::deserialize(exact);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result->msg_type, MsgType::CreateReq);
    EXPECT_EQ(result->payload_size, 20u);
    EXPECT_EQ(result->sequence_id, 7u);
}

TEST_F(IpcMessageHeaderTest, HeaderSizeIs10) {
    EXPECT_EQ(HeaderSize, 10u);
}
