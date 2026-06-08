// SPDX-License-Identifier: MIT
#include <gtest/gtest.h>
#include <legends_ipc/messages.h>
#include <array>
#include <cstring>

using namespace legends_ipc;
using namespace legends_ipc::msg;

class IpcMessagesTest : public ::testing::Test {
protected:
    std::array<uint8_t, 256> buf_{};
    std::span<uint8_t> buf() { return buf_; }
    std::span<const uint8_t> cbuf() { return buf_; }
    std::span<const uint8_t> cbuf(size_t n) {
        return std::span<const uint8_t>(buf_.data(), n);
    }
};

// ── Handshake ───────────────────────────────────────────────────────────────

TEST_F(IpcMessagesTest, HandshakeRoundTrip) {
    Handshake h;
    h.protocol_version  = 1;
    h.max_fb_width      = 1920;
    h.max_fb_height     = 1080;
    h.audio_ring_frames = 4096;

    h.serialize(buf());
    auto r = Handshake::deserialize(cbuf());
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->protocol_version, 1u);
    EXPECT_EQ(r->max_fb_width, 1920u);
    EXPECT_EQ(r->max_fb_height, 1080u);
    EXPECT_EQ(r->audio_ring_frames, 4096u);
}

TEST_F(IpcMessagesTest, HandshakeTooSmall) {
    auto r = Handshake::deserialize(cbuf(Handshake::serialized_size - 1));
    ASSERT_FALSE(r.has_value());
    EXPECT_EQ(r.error(), IpcError::BufferTooSmall);
}

// ── HandshakeAck ────────────────────────────────────────────────────────────

TEST_F(IpcMessagesTest, HandshakeAckRoundTrip) {
    HandshakeAck a;
    a.protocol_version = 1;
    a.engine_version   = 0x010000;
    a.error_code       = 0;

    a.serialize(buf());
    auto r = HandshakeAck::deserialize(cbuf());
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->protocol_version, 1u);
    EXPECT_EQ(r->engine_version, 0x010000u);
    EXPECT_EQ(r->error_code, 0);
}

TEST_F(IpcMessagesTest, HandshakeAckTooSmall) {
    auto r = HandshakeAck::deserialize(cbuf(HandshakeAck::serialized_size - 1));
    ASSERT_FALSE(r.has_value());
    EXPECT_EQ(r.error(), IpcError::BufferTooSmall);
}

// ── Shutdown ────────────────────────────────────────────────────────────────

TEST_F(IpcMessagesTest, ShutdownRoundTrip) {
    ShutdownMsg m;
    m.reason = 1;
    m.serialize(buf());
    auto r = ShutdownMsg::deserialize(cbuf());
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->reason, 1u);
}

// ── Heartbeat ───────────────────────────────────────────────────────────────

TEST_F(IpcMessagesTest, HeartbeatRoundTrip) {
    HeartbeatMsg m;
    m.timestamp_us = 123456789012345ULL;
    m.serialize(buf());
    auto r = HeartbeatMsg::deserialize(cbuf());
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->timestamp_us, 123456789012345ULL);
}

TEST_F(IpcMessagesTest, HeartbeatAckRoundTrip) {
    HeartbeatAckMsg m;
    m.timestamp_us = 999999999ULL;
    m.serialize(buf());
    auto r = HeartbeatAckMsg::deserialize(cbuf());
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->timestamp_us, 999999999ULL);
}

// ── ErrorResponse ───────────────────────────────────────────────────────────

TEST_F(IpcMessagesTest, ErrorResponseRoundTrip) {
    ErrorResponseMsg m;
    m.error_code = -13;
    m.serialize(buf());
    auto r = ErrorResponseMsg::deserialize(cbuf());
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->error_code, -13);
}

// ── GetApiVersion ───────────────────────────────────────────────────────────

TEST_F(IpcMessagesTest, GetApiVersionReqRoundTrip) {
    GetApiVersionReq m;
    m.serialize(buf());
    auto r = GetApiVersionReq::deserialize(cbuf());
    ASSERT_TRUE(r.has_value());
}

TEST_F(IpcMessagesTest, GetApiVersionRespRoundTrip) {
    GetApiVersionResp m;
    m.major = 1; m.minor = 2; m.patch = 3; m.error_code = 0;
    m.serialize(buf());
    auto r = GetApiVersionResp::deserialize(cbuf());
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->major, 1u);
    EXPECT_EQ(r->minor, 2u);
    EXPECT_EQ(r->patch, 3u);
    EXPECT_EQ(r->error_code, 0);
}

TEST_F(IpcMessagesTest, GetApiVersionRespTooSmall) {
    auto r = GetApiVersionResp::deserialize(cbuf(GetApiVersionResp::serialized_size - 1));
    ASSERT_FALSE(r.has_value());
    EXPECT_EQ(r.error(), IpcError::BufferTooSmall);
}

// ── Create ──────────────────────────────────────────────────────────────────

TEST_F(IpcMessagesTest, CreateReqRoundTrip) {
    CreateReq m;
    m.memory_kb = 640; m.xms_kb = 16384; m.ems_kb = 8192;
    m.cpu_cycles = 10000; m.cpu_type = 5; m.machine_type = 0;
    m.deterministic = 1;

    m.serialize(buf());
    auto r = CreateReq::deserialize(cbuf());
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->memory_kb, 640u);
    EXPECT_EQ(r->xms_kb, 16384u);
    EXPECT_EQ(r->ems_kb, 8192u);
    EXPECT_EQ(r->cpu_cycles, 10000u);
    EXPECT_EQ(r->cpu_type, 5);
    EXPECT_EQ(r->machine_type, 0);
    EXPECT_EQ(r->deterministic, 1);
}

TEST_F(IpcMessagesTest, CreateReqTooSmall) {
    auto r = CreateReq::deserialize(cbuf(CreateReq::serialized_size - 1));
    ASSERT_FALSE(r.has_value());
    EXPECT_EQ(r.error(), IpcError::BufferTooSmall);
}

TEST_F(IpcMessagesTest, CreateRespRoundTrip) {
    CreateResp m;
    m.error_code = -3;
    m.serialize(buf());
    auto r = CreateResp::deserialize(cbuf());
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->error_code, -3);
}

// ── StepMs ──────────────────────────────────────────────────────────────────

TEST_F(IpcMessagesTest, StepMsReqRoundTrip) {
    StepMsReq m;
    m.ms = 100;
    m.serialize(buf());
    auto r = StepMsReq::deserialize(cbuf());
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->ms, 100u);
}

TEST_F(IpcMessagesTest, StepMsRespRoundTrip) {
    StepMsResp m;
    m.error_code = 0;
    m.cycles_executed = 500000;
    m.emu_time_us = 100000;
    m.stop_reason = 0;
    m.events_processed = 42;

    m.serialize(buf());
    auto r = StepMsResp::deserialize(cbuf());
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->error_code, 0);
    EXPECT_EQ(r->cycles_executed, 500000ull);
    EXPECT_EQ(r->emu_time_us, 100000ull);
    EXPECT_EQ(r->stop_reason, 0u);
    EXPECT_EQ(r->events_processed, 42u);
}

TEST_F(IpcMessagesTest, StepMsRespTooSmall) {
    auto r = StepMsResp::deserialize(cbuf(StepMsResp::serialized_size - 1));
    ASSERT_FALSE(r.has_value());
    EXPECT_EQ(r.error(), IpcError::BufferTooSmall);
}

// ── StepCycles ──────────────────────────────────────────────────────────────

TEST_F(IpcMessagesTest, StepCyclesReqRoundTrip) {
    StepCyclesReq m;
    m.cycles = 999999999ULL;
    m.serialize(buf());
    auto r = StepCyclesReq::deserialize(cbuf());
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->cycles, 999999999ULL);
}

// ── KeyEvent ────────────────────────────────────────────────────────────────

TEST_F(IpcMessagesTest, KeyEventReqRoundTrip) {
    KeyEventReq m;
    m.scancode = 0x1C; m.is_down = 1;
    m.serialize(buf());
    auto r = KeyEventReq::deserialize(cbuf());
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->scancode, 0x1C);
    EXPECT_EQ(r->is_down, 1);
}

// ── MouseEvent ──────────────────────────────────────────────────────────────

TEST_F(IpcMessagesTest, MouseEventReqRoundTrip) {
    MouseEventReq m;
    m.delta_x = -50; m.delta_y = 30; m.buttons = 0x03;
    m.serialize(buf());
    auto r = MouseEventReq::deserialize(cbuf());
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->delta_x, -50);
    EXPECT_EQ(r->delta_y, 30);
    EXPECT_EQ(r->buttons, 0x03);
}

TEST_F(IpcMessagesTest, MouseEventReqTooSmall) {
    auto r = MouseEventReq::deserialize(cbuf(MouseEventReq::serialized_size - 1));
    ASSERT_FALSE(r.has_value());
    EXPECT_EQ(r.error(), IpcError::BufferTooSmall);
}

// ── GetStateHash ────────────────────────────────────────────────────────────

TEST_F(IpcMessagesTest, GetStateHashRespRoundTrip) {
    GetStateHashResp m;
    m.error_code = 0;
    for (int i = 0; i < 32; ++i) m.hash[i] = static_cast<uint8_t>(i);

    m.serialize(buf());
    auto r = GetStateHashResp::deserialize(cbuf());
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->error_code, 0);
    for (int i = 0; i < 32; ++i)
        EXPECT_EQ(r->hash[i], static_cast<uint8_t>(i));
}

TEST_F(IpcMessagesTest, GetStateHashRespTooSmall) {
    auto r = GetStateHashResp::deserialize(cbuf(GetStateHashResp::serialized_size - 1));
    ASSERT_FALSE(r.has_value());
    EXPECT_EQ(r.error(), IpcError::BufferTooSmall);
}

// ── MountDrive (dynamic-size message) ───────────────────────────────────────

TEST_F(IpcMessagesTest, MountDriveReqRoundTrip) {
    MountDriveReq m;
    m.drive_letter = 'D';
    m.flags = 0x01;
    m.host_path = "/mnt/games";

    m.serialize(buf());
    auto r = MountDriveReq::deserialize(cbuf());
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->drive_letter, 'D');
    EXPECT_EQ(r->flags, 0x01u);
    EXPECT_EQ(r->host_path, "/mnt/games");
}

TEST_F(IpcMessagesTest, MountDriveReqTooSmall) {
    auto r = MountDriveReq::deserialize(cbuf(5));
    ASSERT_FALSE(r.has_value());
    EXPECT_EQ(r.error(), IpcError::BufferTooSmall);
}

// ── UnmountDrive ────────────────────────────────────────────────────────────

TEST_F(IpcMessagesTest, UnmountDriveReqRoundTrip) {
    UnmountDriveReq m;
    m.drive_letter = 'Z';
    m.serialize(buf());
    auto r = UnmountDriveReq::deserialize(cbuf());
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->drive_letter, 'Z');
}

// ── IsFrameDirty ────────────────────────────────────────────────────────────

TEST_F(IpcMessagesTest, IsFrameDirtyRespRoundTrip) {
    IsFrameDirtyResp m;
    m.error_code = 0; m.is_dirty = 1;
    m.serialize(buf());
    auto r = IsFrameDirtyResp::deserialize(cbuf());
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->error_code, 0);
    EXPECT_EQ(r->is_dirty, 1);
}

// ── GetCursor ───────────────────────────────────────────────────────────────

TEST_F(IpcMessagesTest, GetCursorRespRoundTrip) {
    GetCursorResp m;
    m.error_code = 0; m.x = 40; m.y = 12; m.visible = 1;
    m.serialize(buf());
    auto r = GetCursorResp::deserialize(cbuf());
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->x, 40);
    EXPECT_EQ(r->y, 12);
    EXPECT_EQ(r->visible, 1);
}

// ── IsAudioActive ───────────────────────────────────────────────────────────

TEST_F(IpcMessagesTest, IsAudioActiveRespRoundTrip) {
    IsAudioActiveResp m;
    m.error_code = 0; m.is_active = 1;
    m.serialize(buf());
    auto r = IsAudioActiveResp::deserialize(cbuf());
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->is_active, 1);
}

// ── SaveState / LoadState ───────────────────────────────────────────────────

TEST_F(IpcMessagesTest, SaveStateRespRoundTrip) {
    SaveStateResp m;
    m.error_code = 0;
    m.data_size = 4;
    m.state_bytes = {0xDE, 0xAD, 0xBE, 0xEF};
    std::vector<uint8_t> local_buf(m.serialized_size_dynamic());
    m.serialize(local_buf);
    auto r = SaveStateResp::deserialize(local_buf);
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->data_size, 4u);
    EXPECT_EQ(r->state_bytes, m.state_bytes);
}

TEST_F(IpcMessagesTest, LoadStateReqRoundTrip) {
    LoadStateReq m;
    m.data_size = 4;
    m.state_bytes = {1, 2, 3, 4};
    std::vector<uint8_t> local_buf(m.serialized_size_dynamic());
    m.serialize(local_buf);
    auto r = LoadStateReq::deserialize(local_buf);
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->data_size, 4u);
    EXPECT_EQ(r->state_bytes, m.state_bytes);
}

// ── Zero-payload request round-trips ────────────────────────────────────────

TEST_F(IpcMessagesTest, ZeroPayloadRequestsRoundTrip) {
    { auto r = DestroyReq::deserialize(cbuf()); ASSERT_TRUE(r.has_value()); }
    { auto r = ResetReq::deserialize(cbuf()); ASSERT_TRUE(r.has_value()); }
    { auto r = GetEmuTimeReq::deserialize(cbuf()); ASSERT_TRUE(r.has_value()); }
    { auto r = GetTotalCyclesReq::deserialize(cbuf()); ASSERT_TRUE(r.has_value()); }
    { auto r = IsFrameDirtyReq::deserialize(cbuf()); ASSERT_TRUE(r.has_value()); }
    { auto r = GetCursorReq::deserialize(cbuf()); ASSERT_TRUE(r.has_value()); }
    { auto r = IsAudioActiveReq::deserialize(cbuf()); ASSERT_TRUE(r.has_value()); }
    { auto r = SaveStateReq::deserialize(cbuf()); ASSERT_TRUE(r.has_value()); }
    { auto r = GetStateHashReq::deserialize(cbuf()); ASSERT_TRUE(r.has_value()); }
}

// ── GetEmuTime / GetTotalCycles ─────────────────────────────────────────────

TEST_F(IpcMessagesTest, GetEmuTimeRespRoundTrip) {
    GetEmuTimeResp m;
    m.error_code = 0; m.time_us = 5000000ULL;
    m.serialize(buf());
    auto r = GetEmuTimeResp::deserialize(cbuf());
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->time_us, 5000000ULL);
}

TEST_F(IpcMessagesTest, GetTotalCyclesRespRoundTrip) {
    GetTotalCyclesResp m;
    m.error_code = 0; m.cycles = 1234567890ULL;
    m.serialize(buf());
    auto r = GetTotalCyclesResp::deserialize(cbuf());
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->cycles, 1234567890ULL);
}

// ── StepCyclesResp ──────────────────────────────────────────────────────────

TEST_F(IpcMessagesTest, StepCyclesRespRoundTrip) {
    StepCyclesResp m;
    m.error_code = 0;
    m.cycles_executed = 12345;
    m.emu_time_us = 67890;
    m.stop_reason = 1;
    m.events_processed = 7;

    m.serialize(buf());
    auto r = StepCyclesResp::deserialize(cbuf());
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->cycles_executed, 12345ull);
    EXPECT_EQ(r->emu_time_us, 67890ull);
    EXPECT_EQ(r->stop_reason, 1u);
    EXPECT_EQ(r->events_processed, 7u);
}

TEST_F(IpcMessagesTest, SaveStateRespDynamicRoundTrip) {
    SaveStateResp m;
    m.error_code = 0;
    m.data_size = 4;
    m.state_bytes = {1, 2, 3, 4};
    std::vector<uint8_t> local_buf(m.serialized_size_dynamic());
    m.serialize(local_buf);
    auto r = SaveStateResp::deserialize(local_buf);
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->error_code, 0);
    EXPECT_EQ(r->data_size, 4u);
    EXPECT_EQ(r->state_bytes.size(), 4u);
    EXPECT_EQ(r->state_bytes[2], 3);
}

TEST_F(IpcMessagesTest, SaveStateRespRejectsTruncatedPayload) {
    std::array<uint8_t, 10> local_buf{};
    SaveStateResp m;
    m.error_code = 0;
    m.data_size = 4;
    m.state_bytes = {1, 2};

    // Write an intentionally inconsistent header by hand: declared payload is
    // four bytes, but only two bytes are present.
    local_buf[4] = 4;
    auto r = SaveStateResp::deserialize(
        std::span<const uint8_t>(local_buf.data(), local_buf.size()));
    ASSERT_FALSE(r.has_value());
    EXPECT_EQ(r.error(), IpcError::BufferTooSmall);
}

TEST_F(IpcMessagesTest, GetConfigRespRoundTrip) {
    GetConfigResp m;
    m.error_code = 0;
    m.struct_size = 32;
    m.api_version = 1;
    m.memory_kb = 640;
    m.cpu_cycles = 1000;
    m.cpu_type = 3;
    m.machine_type = 1;
    m.deterministic = 1;

    m.serialize(buf());
    auto r = GetConfigResp::deserialize(cbuf());
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->error_code, 0);
    EXPECT_EQ(r->struct_size, 32u);
    EXPECT_EQ(r->api_version, 1u);
    EXPECT_EQ(r->memory_kb, 640u);
    EXPECT_EQ(r->cpu_cycles, 1000u);
    EXPECT_EQ(r->cpu_type, 3);
    EXPECT_EQ(r->machine_type, 1);
    EXPECT_EQ(r->deterministic, 1);
}

TEST_F(IpcMessagesTest, CaptureTextRespRoundTrip) {
    CaptureTextResp m;
    m.error_code = 0;
    m.required_count = 2;
    m.columns = 80;
    m.rows = 25;
    m.cells = {{'A', 0x07}, {'B', 0x0F}};

    std::vector<uint8_t> local_buf(m.serialized_size_dynamic());
    m.serialize(local_buf);
    auto r = CaptureTextResp::deserialize(local_buf);
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->error_code, 0);
    EXPECT_EQ(r->required_count, 2u);
    EXPECT_EQ(r->columns, 80);
    EXPECT_EQ(r->rows, 25);
    ASSERT_EQ(r->cells.size(), 2u);
    EXPECT_EQ(r->cells[0].character, 'A');
    EXPECT_EQ(r->cells[1].attribute, 0x0F);
}

TEST_F(IpcMessagesTest, CaptureTextRespRejectsOddCellPayload) {
    CaptureTextResp m;
    m.error_code = 0;
    m.required_count = 1;

    std::vector<uint8_t> local_buf(17);
    m.serialize(std::span<uint8_t>(local_buf.data(), 16));
    local_buf[16] = 'A';

    auto r = CaptureTextResp::deserialize(local_buf);
    ASSERT_FALSE(r.has_value());
    EXPECT_EQ(r.error(), IpcError::InvalidArgument);
}

TEST_F(IpcMessagesTest, GetLastErrorRespRoundTrip) {
    GetLastErrorResp m;
    m.error_code = 0;
    m.required_len = 12;
    m.error_msg = "Hello World";

    std::vector<uint8_t> local_buf(m.serialized_size_dynamic());
    m.serialize(local_buf);
    auto r = GetLastErrorResp::deserialize(local_buf);
    ASSERT_TRUE(r.has_value());
    EXPECT_EQ(r->error_code, 0);
    EXPECT_EQ(r->required_len, 12u);
    EXPECT_EQ(r->error_msg, "Hello World");
}

TEST_F(IpcMessagesTest, LoadStateReqRejectsMismatchedPayloadSize) {
    std::array<uint8_t, 6> local_buf{};
    // data_size = 4, but only two payload bytes follow.
    local_buf[0] = 4;
    local_buf[4] = 0xAA;
    local_buf[5] = 0xBB;

    auto r = LoadStateReq::deserialize(
        std::span<const uint8_t>(local_buf.data(), local_buf.size()));
    ASSERT_FALSE(r.has_value());
    EXPECT_EQ(r.error(), IpcError::BufferTooSmall);
}

TEST_F(IpcMessagesTest, CaptureMidiAudioRespRejectsOddPayload) {
    CaptureMidiAudioResp m;
    m.error_code = 0;
    m.required_count = 1;

    std::vector<uint8_t> local_buf(9);
    m.serialize(std::span<uint8_t>(local_buf.data(), 8));
    local_buf[8] = 0x7F;

    auto r = CaptureMidiAudioResp::deserialize(local_buf);
    ASSERT_FALSE(r.has_value());
    EXPECT_EQ(r.error(), IpcError::InvalidArgument);
}
