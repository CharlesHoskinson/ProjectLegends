// SPDX-License-Identifier: MIT
#include <gtest/gtest.h>
#include <legends_ipc/message_codec.h>
#include <legends_ipc/message_header.h>
#include <legends_ipc/messages.h>
#include <legends_ipc/wire_format.h>
#include <array>

using namespace legends_ipc;

class IpcMessageCodecTest : public ::testing::Test {
protected:
    MessageCodec codec_;
};

TEST_F(IpcMessageCodecTest, EncodeDecodeRoundTrip) {
    std::array<uint8_t, 4> payload = {0x01, 0x02, 0x03, 0x04};
    auto wire = MessageCodec::encode(MsgType::StepMsReq, 42, payload);

    EXPECT_EQ(wire.size(), HeaderSize + 4);

    codec_.feed(wire);
    auto result = codec_.try_decode();
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result->header.msg_type, MsgType::StepMsReq);
    EXPECT_EQ(result->header.payload_size, 4u);
    EXPECT_EQ(result->header.sequence_id, 42u);
    ASSERT_EQ(result->payload.size(), 4u);
    EXPECT_EQ(result->payload[0], 0x01);
    EXPECT_EQ(result->payload[3], 0x04);
}

TEST_F(IpcMessageCodecTest, EmptyPayload) {
    auto wire = MessageCodec::encode(MsgType::DestroyReq, 1, {});

    codec_.feed(wire);
    auto result = codec_.try_decode();
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result->header.msg_type, MsgType::DestroyReq);
    EXPECT_EQ(result->header.payload_size, 0u);
    EXPECT_TRUE(result->payload.empty());
}

TEST_F(IpcMessageCodecTest, MultiMessageStream) {
    auto wire1 = MessageCodec::encode(MsgType::Handshake, 1, std::array<uint8_t, 16>{});
    auto wire2 = MessageCodec::encode(MsgType::StepMsReq, 2, std::array<uint8_t, 4>{});
    auto wire3 = MessageCodec::encode(MsgType::DestroyReq, 3, {});

    // Feed all at once
    codec_.feed(wire1);
    codec_.feed(wire2);
    codec_.feed(wire3);

    auto r1 = codec_.try_decode();
    ASSERT_TRUE(r1.has_value());
    EXPECT_EQ(r1->header.msg_type, MsgType::Handshake);
    EXPECT_EQ(r1->header.sequence_id, 1u);

    auto r2 = codec_.try_decode();
    ASSERT_TRUE(r2.has_value());
    EXPECT_EQ(r2->header.msg_type, MsgType::StepMsReq);
    EXPECT_EQ(r2->header.sequence_id, 2u);

    auto r3 = codec_.try_decode();
    ASSERT_TRUE(r3.has_value());
    EXPECT_EQ(r3->header.msg_type, MsgType::DestroyReq);
    EXPECT_EQ(r3->header.sequence_id, 3u);

    // No more messages
    auto r4 = codec_.try_decode();
    ASSERT_FALSE(r4.has_value());
    EXPECT_EQ(r4.error(), IpcError::BufferTooSmall);
}

TEST_F(IpcMessageCodecTest, TruncatedMessage) {
    auto wire = MessageCodec::encode(MsgType::StepMsReq, 1, std::array<uint8_t, 4>{});
    // Feed only partial data
    codec_.feed(std::span<const uint8_t>(wire.data(), wire.size() - 2));
    auto result = codec_.try_decode();
    ASSERT_FALSE(result.has_value());
    EXPECT_EQ(result.error(), IpcError::BufferTooSmall);

    // Feed remaining bytes
    codec_.feed(std::span<const uint8_t>(wire.data() + wire.size() - 2, 2));
    auto result2 = codec_.try_decode();
    ASSERT_TRUE(result2.has_value());
    EXPECT_EQ(result2->header.msg_type, MsgType::StepMsReq);
}

TEST_F(IpcMessageCodecTest, PartialHeaderFeed) {
    auto wire = MessageCodec::encode(MsgType::Heartbeat, 99, std::array<uint8_t, 8>{});

    // Feed 5 bytes (less than HeaderSize=10)
    codec_.feed(std::span<const uint8_t>(wire.data(), 5));
    auto r1 = codec_.try_decode();
    ASSERT_FALSE(r1.has_value());
    EXPECT_EQ(r1.error(), IpcError::BufferTooSmall);

    // Feed rest
    codec_.feed(std::span<const uint8_t>(wire.data() + 5, wire.size() - 5));
    auto r2 = codec_.try_decode();
    ASSERT_TRUE(r2.has_value());
    EXPECT_EQ(r2->header.msg_type, MsgType::Heartbeat);
    EXPECT_EQ(r2->header.sequence_id, 99u);
}

TEST_F(IpcMessageCodecTest, ResetClearsBuffer) {
    auto wire = MessageCodec::encode(MsgType::Handshake, 1, std::array<uint8_t, 16>{});
    codec_.feed(std::span<const uint8_t>(wire.data(), 5));
    EXPECT_EQ(codec_.buffered_bytes(), 5u);

    codec_.reset();
    EXPECT_EQ(codec_.buffered_bytes(), 0u);

    auto r = codec_.try_decode();
    ASSERT_FALSE(r.has_value());
}

TEST_F(IpcMessageCodecTest, LargePayload) {
    std::vector<uint8_t> payload(65536);
    for (size_t i = 0; i < payload.size(); ++i)
        payload[i] = static_cast<uint8_t>(i & 0xFF);

    auto wire = MessageCodec::encode(MsgType::SaveStateResp, 7, payload);
    codec_.feed(wire);
    auto result = codec_.try_decode();
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result->header.payload_size, 65536u);
    ASSERT_EQ(result->payload.size(), 65536u);
    for (size_t i = 0; i < 65536; ++i)
        EXPECT_EQ(result->payload[i], static_cast<uint8_t>(i & 0xFF));
}

TEST_F(IpcMessageCodecTest, ByteByByteFeed) {
    auto wire = MessageCodec::encode(MsgType::KeyEventReq, 5, std::array<uint8_t, 2>{0x1C, 1});

    for (size_t i = 0; i < wire.size() - 1; ++i) {
        codec_.feed(std::span<const uint8_t>(wire.data() + i, 1));
        auto r = codec_.try_decode();
        ASSERT_FALSE(r.has_value());
    }
    codec_.feed(std::span<const uint8_t>(wire.data() + wire.size() - 1, 1));
    auto r = codec_.try_decode();
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->header.msg_type, MsgType::KeyEventReq);
}

TEST_F(IpcMessageCodecTest, RejectsOversizedPayload) {
    // Craft a raw header that claims a payload of 256 MB + 1 byte,
    // which exceeds kMaxPayloadSize (64 MB).  The decoder must reject
    // this without attempting the allocation.
    constexpr uint32_t oversized = 256u * 1024u * 1024u + 1u;
    std::array<uint8_t, 10> raw_header{};  // HeaderSize == 10
    wire::write_u16_le(raw_header, 0, static_cast<uint16_t>(MsgType::Handshake));
    wire::write_u32_le(raw_header, 2, oversized);
    wire::write_u32_le(raw_header, 6, 1);  // sequence_id

    codec_.feed(raw_header);
    auto result = codec_.try_decode();
    ASSERT_FALSE(result.has_value());
    EXPECT_EQ(result.error(), IpcError::InvalidHeader);

    // Buffer should have been cleared on rejection.
    EXPECT_EQ(codec_.buffered_bytes(), 0u);
}
