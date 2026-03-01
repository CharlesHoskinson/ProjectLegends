// SPDX-License-Identifier: MIT
#include <legends_ipc/messages.h>

namespace legends_ipc::msg {

using namespace legends_ipc::wire;

// ── Helper macro for fixed-size message with single error_code field ────────

#define IMPL_ERROR_ONLY(Type)                                                 \
    void Type::serialize(std::span<uint8_t> buf) const {                      \
        gsl_Expects(buf.size() >= serialized_size);                           \
        write_i32_le(buf, 0, error_code);                                     \
    }                                                                         \
    std::expected<Type, IpcError> Type::deserialize(std::span<const uint8_t> buf) { \
        if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall); \
        Type m; m.error_code = read_i32_le(buf, 0); return m;                \
    }

// ── Control messages ────────────────────────────────────────────────────────

void Handshake::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_u32_le(buf, 0, protocol_version);
    write_u32_le(buf, 4, max_fb_width);
    write_u32_le(buf, 8, max_fb_height);
    write_u32_le(buf, 12, audio_ring_frames);
}

std::expected<Handshake, IpcError> Handshake::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    Handshake m;
    m.protocol_version  = read_u32_le(buf, 0);
    m.max_fb_width      = read_u32_le(buf, 4);
    m.max_fb_height     = read_u32_le(buf, 8);
    m.audio_ring_frames = read_u32_le(buf, 12);
    return m;
}

void HandshakeAck::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_u32_le(buf, 0, protocol_version);
    write_u32_le(buf, 4, engine_version);
    write_i32_le(buf, 8, error_code);
}

std::expected<HandshakeAck, IpcError> HandshakeAck::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    HandshakeAck m;
    m.protocol_version = read_u32_le(buf, 0);
    m.engine_version   = read_u32_le(buf, 4);
    m.error_code       = read_i32_le(buf, 8);
    return m;
}

void ShutdownMsg::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_u32_le(buf, 0, reason);
}

std::expected<ShutdownMsg, IpcError> ShutdownMsg::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    ShutdownMsg m;
    m.reason = read_u32_le(buf, 0);
    return m;
}

IMPL_ERROR_ONLY(ShutdownAckMsg)
IMPL_ERROR_ONLY(ErrorResponseMsg)

void HeartbeatMsg::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_u64_le(buf, 0, timestamp_us);
}

std::expected<HeartbeatMsg, IpcError> HeartbeatMsg::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    HeartbeatMsg m;
    m.timestamp_us = read_u64_le(buf, 0);
    return m;
}

void HeartbeatAckMsg::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_u64_le(buf, 0, timestamp_us);
}

std::expected<HeartbeatAckMsg, IpcError> HeartbeatAckMsg::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    HeartbeatAckMsg m;
    m.timestamp_us = read_u64_le(buf, 0);
    return m;
}

// ── Lifecycle messages ──────────────────────────────────────────────────────

void GetApiVersionResp::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_u32_le(buf, 0, major);
    write_u32_le(buf, 4, minor);
    write_u32_le(buf, 8, patch);
    write_i32_le(buf, 12, error_code);
}

std::expected<GetApiVersionResp, IpcError> GetApiVersionResp::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    GetApiVersionResp m;
    m.major      = read_u32_le(buf, 0);
    m.minor      = read_u32_le(buf, 4);
    m.patch      = read_u32_le(buf, 8);
    m.error_code = read_i32_le(buf, 12);
    return m;
}

void CreateReq::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_u32_le(buf, 0, memory_kb);
    write_u32_le(buf, 4, xms_kb);
    write_u32_le(buf, 8, ems_kb);
    write_u32_le(buf, 12, cpu_cycles);
    write_u8(buf, 16, cpu_type);
    write_u8(buf, 17, machine_type);
    write_u8(buf, 18, deterministic);
    write_u8(buf, 19, _pad);
}

std::expected<CreateReq, IpcError> CreateReq::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    CreateReq m;
    m.memory_kb     = read_u32_le(buf, 0);
    m.xms_kb        = read_u32_le(buf, 4);
    m.ems_kb        = read_u32_le(buf, 8);
    m.cpu_cycles    = read_u32_le(buf, 12);
    m.cpu_type      = read_u8(buf, 16);
    m.machine_type  = read_u8(buf, 17);
    m.deterministic = read_u8(buf, 18);
    m._pad          = read_u8(buf, 19);
    return m;
}

IMPL_ERROR_ONLY(CreateResp)
IMPL_ERROR_ONLY(DestroyResp)
IMPL_ERROR_ONLY(ResetResp)

// ── Stepping messages ───────────────────────────────────────────────────────

void StepMsReq::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_u32_le(buf, 0, ms);
}

std::expected<StepMsReq, IpcError> StepMsReq::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    StepMsReq m;
    m.ms = read_u32_le(buf, 0);
    return m;
}

void StepMsResp::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_i32_le(buf, 0, error_code);
    write_u64_le(buf, 4, cycles_executed);
    write_u64_le(buf, 12, emu_time_us);
    write_u32_le(buf, 20, stop_reason);
    write_u32_le(buf, 24, events_processed);
}

std::expected<StepMsResp, IpcError> StepMsResp::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    StepMsResp m;
    m.error_code       = read_i32_le(buf, 0);
    m.cycles_executed  = read_u64_le(buf, 4);
    m.emu_time_us      = read_u64_le(buf, 12);
    m.stop_reason      = read_u32_le(buf, 20);
    m.events_processed = read_u32_le(buf, 24);
    return m;
}

void StepCyclesReq::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_u64_le(buf, 0, cycles);
}

std::expected<StepCyclesReq, IpcError> StepCyclesReq::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    StepCyclesReq m;
    m.cycles = read_u64_le(buf, 0);
    return m;
}

void StepCyclesResp::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_i32_le(buf, 0, error_code);
    write_u64_le(buf, 4, cycles_executed);
    write_u64_le(buf, 12, emu_time_us);
    write_u32_le(buf, 20, stop_reason);
    write_u32_le(buf, 24, events_processed);
}

std::expected<StepCyclesResp, IpcError> StepCyclesResp::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    StepCyclesResp m;
    m.error_code       = read_i32_le(buf, 0);
    m.cycles_executed  = read_u64_le(buf, 4);
    m.emu_time_us      = read_u64_le(buf, 12);
    m.stop_reason      = read_u32_le(buf, 20);
    m.events_processed = read_u32_le(buf, 24);
    return m;
}

void GetEmuTimeResp::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_i32_le(buf, 0, error_code);
    write_u64_le(buf, 4, time_us);
}

std::expected<GetEmuTimeResp, IpcError> GetEmuTimeResp::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    GetEmuTimeResp m;
    m.error_code = read_i32_le(buf, 0);
    m.time_us    = read_u64_le(buf, 4);
    return m;
}

void GetTotalCyclesResp::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_i32_le(buf, 0, error_code);
    write_u64_le(buf, 4, cycles);
}

std::expected<GetTotalCyclesResp, IpcError> GetTotalCyclesResp::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    GetTotalCyclesResp m;
    m.error_code = read_i32_le(buf, 0);
    m.cycles     = read_u64_le(buf, 4);
    return m;
}

// ── Input messages ──────────────────────────────────────────────────────────

void KeyEventReq::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_u8(buf, 0, scancode);
    write_u8(buf, 1, is_down);
}

std::expected<KeyEventReq, IpcError> KeyEventReq::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    KeyEventReq m;
    m.scancode = read_u8(buf, 0);
    m.is_down  = read_u8(buf, 1);
    return m;
}

IMPL_ERROR_ONLY(KeyEventResp)

void MouseEventReq::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_i16_le(buf, 0, delta_x);
    write_i16_le(buf, 2, delta_y);
    write_u8(buf, 4, buttons);
}

std::expected<MouseEventReq, IpcError> MouseEventReq::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    MouseEventReq m;
    m.delta_x = read_i16_le(buf, 0);
    m.delta_y = read_i16_le(buf, 2);
    m.buttons = read_u8(buf, 4);
    return m;
}

IMPL_ERROR_ONLY(MouseEventResp)

// ── Save/Load messages ──────────────────────────────────────────────────────

void SaveStateResp::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_i32_le(buf, 0, error_code);
    write_u32_le(buf, 4, data_size);
}

std::expected<SaveStateResp, IpcError> SaveStateResp::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    SaveStateResp m;
    m.error_code = read_i32_le(buf, 0);
    m.data_size  = read_u32_le(buf, 4);
    return m;
}

void LoadStateReq::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_u32_le(buf, 0, data_size);
}

std::expected<LoadStateReq, IpcError> LoadStateReq::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    LoadStateReq m;
    m.data_size = read_u32_le(buf, 0);
    return m;
}

IMPL_ERROR_ONLY(LoadStateResp)

void GetStateHashResp::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_i32_le(buf, 0, error_code);
    std::memcpy(buf.data() + 4, hash, 32);
}

std::expected<GetStateHashResp, IpcError> GetStateHashResp::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    GetStateHashResp m;
    m.error_code = read_i32_le(buf, 0);
    std::memcpy(m.hash, buf.data() + 4, 32);
    return m;
}

// ── String-carrying messages ────────────────────────────────────────────────

void MountDriveReq::serialize(std::span<uint8_t> buf) const {
    auto sz = serialized_size_dynamic();
    gsl_Expects(buf.size() >= sz);
    write_u8(buf, 0, static_cast<uint8_t>(drive_letter));
    write_u32_le(buf, 1, flags);
    write_u8(buf, 5, static_cast<uint8_t>(host_path.size()));
    std::memcpy(buf.data() + 6, host_path.data(), host_path.size());
}

std::expected<MountDriveReq, IpcError> MountDriveReq::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < 6) return std::unexpected(IpcError::BufferTooSmall);
    MountDriveReq m;
    m.drive_letter = static_cast<char>(read_u8(buf, 0));
    m.flags        = read_u32_le(buf, 1);
    uint8_t path_len = read_u8(buf, 5);
    if (buf.size() < 6u + path_len) return std::unexpected(IpcError::BufferTooSmall);
    m.host_path = std::string(reinterpret_cast<const char*>(buf.data() + 6), path_len);
    return m;
}

IMPL_ERROR_ONLY(MountDriveResp)

void UnmountDriveReq::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_u8(buf, 0, static_cast<uint8_t>(drive_letter));
}

std::expected<UnmountDriveReq, IpcError> UnmountDriveReq::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    UnmountDriveReq m;
    m.drive_letter = static_cast<char>(read_u8(buf, 0));
    return m;
}

IMPL_ERROR_ONLY(UnmountDriveResp)

// ── Frame dirty / cursor ────────────────────────────────────────────────────

void IsFrameDirtyResp::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_i32_le(buf, 0, error_code);
    write_u8(buf, 4, is_dirty);
}

std::expected<IsFrameDirtyResp, IpcError> IsFrameDirtyResp::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    IsFrameDirtyResp m;
    m.error_code = read_i32_le(buf, 0);
    m.is_dirty   = read_u8(buf, 4);
    return m;
}

void GetCursorResp::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_i32_le(buf, 0, error_code);
    write_u8(buf, 4, x);
    write_u8(buf, 5, y);
    write_u8(buf, 6, visible);
}

std::expected<GetCursorResp, IpcError> GetCursorResp::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    GetCursorResp m;
    m.error_code = read_i32_le(buf, 0);
    m.x          = read_u8(buf, 4);
    m.y          = read_u8(buf, 5);
    m.visible    = read_u8(buf, 6);
    return m;
}

// ── Audio active ────────────────────────────────────────────────────────────

void IsAudioActiveResp::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_i32_le(buf, 0, error_code);
    write_u8(buf, 4, is_active);
}

std::expected<IsAudioActiveResp, IpcError> IsAudioActiveResp::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    IsAudioActiveResp m;
    m.error_code = read_i32_le(buf, 0);
    m.is_active  = read_u8(buf, 4);
    return m;
}

#undef IMPL_ERROR_ONLY

} // namespace legends_ipc::msg
