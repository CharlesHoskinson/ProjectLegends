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
    gsl_Expects(buf.size() >= serialized_size_dynamic());
    write_i32_le(buf, 0, error_code);
    write_u32_le(buf, 4, data_size);
    if (!state_bytes.empty()) {
        std::memcpy(buf.data() + 8, state_bytes.data(), state_bytes.size());
    }
}

std::expected<SaveStateResp, IpcError> SaveStateResp::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < 8) return std::unexpected(IpcError::BufferTooSmall);
    SaveStateResp m;
    m.error_code = read_i32_le(buf, 0);
    m.data_size  = read_u32_le(buf, 4);
    size_t payload_len = buf.size() - 8;
    if (payload_len < m.data_size) return std::unexpected(IpcError::BufferTooSmall);
    if (payload_len > m.data_size) return std::unexpected(IpcError::InvalidArgument);
    if (payload_len > 0) {
        m.state_bytes.resize(m.data_size);
        std::memcpy(m.state_bytes.data(), buf.data() + 8, payload_len);
    }
    return m;
}

void LoadStateReq::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size_dynamic());
    write_u32_le(buf, 0, data_size);
    if (!state_bytes.empty()) {
        std::memcpy(buf.data() + 4, state_bytes.data(), state_bytes.size());
    }
}

std::expected<LoadStateReq, IpcError> LoadStateReq::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < 4) return std::unexpected(IpcError::BufferTooSmall);
    LoadStateReq m;
    m.data_size = read_u32_le(buf, 0);
    size_t payload_len = buf.size() - 4;
    if (payload_len < m.data_size) return std::unexpected(IpcError::BufferTooSmall);
    if (payload_len > m.data_size) return std::unexpected(IpcError::InvalidArgument);
    if (payload_len > 0) {
        m.state_bytes.resize(m.data_size);
        std::memcpy(m.state_bytes.data(), buf.data() + 4, payload_len);
    }
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

// ── Core Proxy Parity additions ──────────────────────────────────────────────

void GetConfigResp::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_i32_le(buf, 0, error_code);
    write_u32_le(buf, 4, struct_size);
    write_u32_le(buf, 8, api_version);
    write_u32_le(buf, 12, memory_kb);
    write_u32_le(buf, 16, xms_kb);
    write_u32_le(buf, 20, ems_kb);
    write_u32_le(buf, 24, cpu_cycles);
    write_u8(buf, 28, cpu_type);
    write_u8(buf, 29, machine_type);
    write_u8(buf, 30, deterministic);
    write_u8(buf, 31, _pad);
}

std::expected<GetConfigResp, IpcError> GetConfigResp::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    GetConfigResp m;
    m.error_code    = read_i32_le(buf, 0);
    m.struct_size   = read_u32_le(buf, 4);
    m.api_version   = read_u32_le(buf, 8);
    m.memory_kb     = read_u32_le(buf, 12);
    m.xms_kb        = read_u32_le(buf, 16);
    m.ems_kb        = read_u32_le(buf, 20);
    m.cpu_cycles    = read_u32_le(buf, 24);
    m.cpu_type      = read_u8(buf, 28);
    m.machine_type  = read_u8(buf, 29);
    m.deterministic = read_u8(buf, 30);
    m._pad          = read_u8(buf, 31);
    return m;
}

void CaptureTextReq::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_u32_le(buf, 0, cells_count);
}

std::expected<CaptureTextReq, IpcError> CaptureTextReq::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    CaptureTextReq m;
    m.cells_count = read_u32_le(buf, 0);
    return m;
}

void CaptureTextResp::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size_dynamic());
    write_i32_le(buf, 0, error_code);
    write_u32_le(buf, 4, required_count);
    write_u8(buf, 8, columns);
    write_u8(buf, 9, rows);
    write_u8(buf, 10, active_page);
    write_u8(buf, 11, cursor_x);
    write_u8(buf, 12, cursor_y);
    write_u8(buf, 13, cursor_visible);
    write_u8(buf, 14, cursor_start);
    write_u8(buf, 15, cursor_end);
    for (size_t i = 0; i < cells.size(); ++i) {
        write_u8(buf, 16 + i * 2, cells[i].character);
        write_u8(buf, 17 + i * 2, cells[i].attribute);
    }
}

std::expected<CaptureTextResp, IpcError> CaptureTextResp::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < 16) return std::unexpected(IpcError::BufferTooSmall);
    CaptureTextResp m;
    m.error_code     = read_i32_le(buf, 0);
    m.required_count = read_u32_le(buf, 4);
    m.columns        = read_u8(buf, 8);
    m.rows           = read_u8(buf, 9);
    m.active_page    = read_u8(buf, 10);
    m.cursor_x       = read_u8(buf, 11);
    m.cursor_y       = read_u8(buf, 12);
    m.cursor_visible = read_u8(buf, 13);
    m.cursor_start   = read_u8(buf, 14);
    m.cursor_end     = read_u8(buf, 15);
    size_t payload_len = buf.size() - 16;
    if (payload_len > 0) {
        if ((payload_len % 2) != 0) return std::unexpected(IpcError::InvalidArgument);
        size_t count = payload_len / 2;
        if (count > m.required_count) return std::unexpected(IpcError::InvalidArgument);
        m.cells.resize(count);
        for (size_t i = 0; i < count; ++i) {
            m.cells[i].character = read_u8(buf, 16 + i * 2);
            m.cells[i].attribute = read_u8(buf, 17 + i * 2);
        }
    }
    return m;
}

void VerifyDeterminismReq::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_u64_le(buf, 0, test_cycles);
}

std::expected<VerifyDeterminismReq, IpcError> VerifyDeterminismReq::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    VerifyDeterminismReq m;
    m.test_cycles = read_u64_le(buf, 0);
    return m;
}

void VerifyDeterminismResp::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_i32_le(buf, 0, error_code);
    write_i32_le(buf, 4, is_deterministic);
}

std::expected<VerifyDeterminismResp, IpcError> VerifyDeterminismResp::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    VerifyDeterminismResp m;
    m.error_code = read_i32_le(buf, 0);
    m.is_deterministic = read_i32_le(buf, 4);
    return m;
}

void GetLastErrorResp::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size_dynamic());
    write_i32_le(buf, 0, error_code);
    write_u32_le(buf, 4, required_len);
    if (!error_msg.empty()) {
        std::memcpy(buf.data() + 8, error_msg.data(), error_msg.size());
    }
}

std::expected<GetLastErrorResp, IpcError> GetLastErrorResp::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < 8) return std::unexpected(IpcError::BufferTooSmall);
    GetLastErrorResp m;
    m.error_code   = read_i32_le(buf, 0);
    m.required_len = read_u32_le(buf, 4);
    size_t len = buf.size() - 8;
    if (len > 0) {
        m.error_msg = std::string(reinterpret_cast<const char*>(buf.data() + 8), len);
    }
    return m;
}

// ── Device Command Proxy Parity additions ────────────────────────────────────

void KeyEventExtReq::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_u8(buf, 0, scancode);
    write_u8(buf, 1, is_down);
}

std::expected<KeyEventExtReq, IpcError> KeyEventExtReq::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    KeyEventExtReq m;
    m.scancode = read_u8(buf, 0);
    m.is_down = read_u8(buf, 1);
    return m;
}

IMPL_ERROR_ONLY(KeyEventExtResp)

void TextInputReq::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size_dynamic());
    write_u32_le(buf, 0, static_cast<uint32_t>(text.size()));
    if (!text.empty()) {
        std::memcpy(buf.data() + 4, text.data(), text.size());
    }
}

std::expected<TextInputReq, IpcError> TextInputReq::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < 4) return std::unexpected(IpcError::BufferTooSmall);
    uint32_t len = read_u32_le(buf, 0);
    if (buf.size() - 4 < len) return std::unexpected(IpcError::BufferTooSmall);
    TextInputReq m;
    if (len > 0) {
        m.text = std::string(reinterpret_cast<const char*>(buf.data() + 4), len);
    }
    return m;
}

IMPL_ERROR_ONLY(TextInputResp)

void JoystickEventReq::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_u8(buf, 0, joystick_id);
    write_u8(buf, 1, axis_x);
    write_u8(buf, 2, axis_y);
    write_u8(buf, 3, buttons);
}

std::expected<JoystickEventReq, IpcError> JoystickEventReq::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    JoystickEventReq m;
    m.joystick_id = read_u8(buf, 0);
    m.axis_x = read_u8(buf, 1);
    m.axis_y = read_u8(buf, 2);
    m.buttons = read_u8(buf, 3);
    return m;
}

IMPL_ERROR_ONLY(JoystickEventResp)

void MidiSetDeviceReq::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size_dynamic());
    write_u32_le(buf, 0, static_cast<uint32_t>(device.size()));
    if (!device.empty()) {
        std::memcpy(buf.data() + 4, device.data(), device.size());
    }
}

std::expected<MidiSetDeviceReq, IpcError> MidiSetDeviceReq::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < 4) return std::unexpected(IpcError::BufferTooSmall);
    uint32_t len = read_u32_le(buf, 0);
    if (buf.size() - 4 < len) return std::unexpected(IpcError::BufferTooSmall);
    MidiSetDeviceReq m;
    if (len > 0) {
        m.device = std::string(reinterpret_cast<const char*>(buf.data() + 4), len);
    }
    return m;
}

IMPL_ERROR_ONLY(MidiSetDeviceResp)

void MidiSetSoundfontReq::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size_dynamic());
    write_u32_le(buf, 0, static_cast<uint32_t>(soundfont.size()));
    if (!soundfont.empty()) {
        std::memcpy(buf.data() + 4, soundfont.data(), soundfont.size());
    }
}

std::expected<MidiSetSoundfontReq, IpcError> MidiSetSoundfontReq::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < 4) return std::unexpected(IpcError::BufferTooSmall);
    uint32_t len = read_u32_le(buf, 0);
    if (buf.size() - 4 < len) return std::unexpected(IpcError::BufferTooSmall);
    MidiSetSoundfontReq m;
    if (len > 0) {
        m.soundfont = std::string(reinterpret_cast<const char*>(buf.data() + 4), len);
    }
    return m;
}

IMPL_ERROR_ONLY(MidiSetSoundfontResp)

void MidiSetRomdirReq::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size_dynamic());
    write_u32_le(buf, 0, static_cast<uint32_t>(romdir.size()));
    if (!romdir.empty()) {
        std::memcpy(buf.data() + 4, romdir.data(), romdir.size());
    }
}

std::expected<MidiSetRomdirReq, IpcError> MidiSetRomdirReq::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < 4) return std::unexpected(IpcError::BufferTooSmall);
    uint32_t len = read_u32_le(buf, 0);
    if (buf.size() - 4 < len) return std::unexpected(IpcError::BufferTooSmall);
    MidiSetRomdirReq m;
    if (len > 0) {
        m.romdir = std::string(reinterpret_cast<const char*>(buf.data() + 4), len);
    }
    return m;
}

IMPL_ERROR_ONLY(MidiSetRomdirResp)

void CaptureMidiAudioReq::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_u32_le(buf, 0, buffer_count);
}

std::expected<CaptureMidiAudioReq, IpcError> CaptureMidiAudioReq::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    CaptureMidiAudioReq m;
    m.buffer_count = read_u32_le(buf, 0);
    return m;
}

void CaptureMidiAudioResp::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size_dynamic());
    write_i32_le(buf, 0, error_code);
    write_u32_le(buf, 4, required_count);
    if (!audio_data.empty()) {
        std::memcpy(buf.data() + 8, audio_data.data(), audio_data.size() * 2);
    }
}

std::expected<CaptureMidiAudioResp, IpcError> CaptureMidiAudioResp::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < 8) return std::unexpected(IpcError::BufferTooSmall);
    CaptureMidiAudioResp m;
    m.error_code = read_i32_le(buf, 0);
    m.required_count = read_u32_le(buf, 4);
    size_t payload_len = buf.size() - 8;
    if (payload_len > 0) {
        if ((payload_len % 2) != 0) return std::unexpected(IpcError::InvalidArgument);
        if ((payload_len / 2) > m.required_count) return std::unexpected(IpcError::InvalidArgument);
        m.audio_data.resize(payload_len / 2);
        std::memcpy(m.audio_data.data(), buf.data() + 8, payload_len);
    }
    return m;
}

void PrinterSetOutputReq::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size_dynamic());
    write_u32_le(buf, 0, static_cast<uint32_t>(output_path.size()));
    if (!output_path.empty()) {
        std::memcpy(buf.data() + 4, output_path.data(), output_path.size());
    }
}

std::expected<PrinterSetOutputReq, IpcError> PrinterSetOutputReq::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < 4) return std::unexpected(IpcError::BufferTooSmall);
    uint32_t len = read_u32_le(buf, 0);
    if (buf.size() - 4 < len) return std::unexpected(IpcError::BufferTooSmall);
    PrinterSetOutputReq m;
    if (len > 0) {
        m.output_path = std::string(reinterpret_cast<const char*>(buf.data() + 4), len);
    }
    return m;
}

IMPL_ERROR_ONLY(PrinterSetOutputResp)

void PrinterIsActiveResp::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_i32_le(buf, 0, error_code);
    write_i32_le(buf, 4, is_active);
}

std::expected<PrinterIsActiveResp, IpcError> PrinterIsActiveResp::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    PrinterIsActiveResp m;
    m.error_code = read_i32_le(buf, 0);
    m.is_active = read_i32_le(buf, 4);
    return m;
}

IMPL_ERROR_ONLY(PrinterFlushResp)

void IpxEnableReq::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_i32_le(buf, 0, enable);
}

std::expected<IpxEnableReq, IpcError> IpxEnableReq::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    IpxEnableReq m;
    m.enable = read_i32_le(buf, 0);
    return m;
}

IMPL_ERROR_ONLY(IpxEnableResp)

void IpxConnectReq::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size_dynamic());
    write_u16_le(buf, 0, port);
    write_u32_le(buf, 2, static_cast<uint32_t>(server.size()));
    if (!server.empty()) {
        std::memcpy(buf.data() + 6, server.data(), server.size());
    }
}

std::expected<IpxConnectReq, IpcError> IpxConnectReq::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < 6) return std::unexpected(IpcError::BufferTooSmall);
    IpxConnectReq m;
    m.port = read_u16_le(buf, 0);
    uint32_t len = read_u32_le(buf, 2);
    if (buf.size() - 6 < len) return std::unexpected(IpcError::BufferTooSmall);
    if (len > 0) {
        m.server = std::string(reinterpret_cast<const char*>(buf.data() + 6), len);
    }
    return m;
}

IMPL_ERROR_ONLY(IpxConnectResp)
IMPL_ERROR_ONLY(IpxDisconnectResp)

void IpxIsConnectedResp::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_i32_le(buf, 0, error_code);
    write_i32_le(buf, 4, is_connected);
}

std::expected<IpxIsConnectedResp, IpcError> IpxIsConnectedResp::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    IpxIsConnectedResp m;
    m.error_code = read_i32_le(buf, 0);
    m.is_connected = read_i32_le(buf, 4);
    return m;
}

void GlideEnableReq::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_i32_le(buf, 0, enable);
}

std::expected<GlideEnableReq, IpcError> GlideEnableReq::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    GlideEnableReq m;
    m.enable = read_i32_le(buf, 0);
    return m;
}

IMPL_ERROR_ONLY(GlideEnableResp)

void GlideSetResolutionReq::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_u16_le(buf, 0, width);
    write_u16_le(buf, 2, height);
}

std::expected<GlideSetResolutionReq, IpcError> GlideSetResolutionReq::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    GlideSetResolutionReq m;
    m.width = read_u16_le(buf, 0);
    m.height = read_u16_le(buf, 2);
    return m;
}

IMPL_ERROR_ONLY(GlideSetResolutionResp)

void SetMachinePc98Req::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_i32_le(buf, 0, enable);
}

std::expected<SetMachinePc98Req, IpcError> SetMachinePc98Req::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    SetMachinePc98Req m;
    m.enable = read_i32_le(buf, 0);
    return m;
}

IMPL_ERROR_ONLY(SetMachinePc98Resp)

void IsPc98ModeResp::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_i32_le(buf, 0, error_code);
    write_i32_le(buf, 4, is_pc98);
}

std::expected<IsPc98ModeResp, IpcError> IsPc98ModeResp::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    IsPc98ModeResp m;
    m.error_code = read_i32_le(buf, 0);
    m.is_pc98 = read_i32_le(buf, 4);
    return m;
}

void HasCapabilityReq::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size_dynamic());
    write_u32_le(buf, 0, static_cast<uint32_t>(name.size()));
    if (!name.empty()) {
        std::memcpy(buf.data() + 4, name.data(), name.size());
    }
}

std::expected<HasCapabilityReq, IpcError> HasCapabilityReq::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < 4) return std::unexpected(IpcError::BufferTooSmall);
    uint32_t len = read_u32_le(buf, 0);
    if (buf.size() - 4 < len) return std::unexpected(IpcError::BufferTooSmall);
    HasCapabilityReq m;
    if (len > 0) {
        m.name = std::string(reinterpret_cast<const char*>(buf.data() + 4), len);
    }
    return m;
}

void HasCapabilityResp::serialize(std::span<uint8_t> buf) const {
    gsl_Expects(buf.size() >= serialized_size);
    write_i32_le(buf, 0, error_code);
    write_i32_le(buf, 4, has_cap);
}

std::expected<HasCapabilityResp, IpcError> HasCapabilityResp::deserialize(std::span<const uint8_t> buf) {
    if (buf.size() < serialized_size) return std::unexpected(IpcError::BufferTooSmall);
    HasCapabilityResp m;
    m.error_code = read_i32_le(buf, 0);
    m.has_cap = read_i32_le(buf, 4);
    return m;
}

#undef IMPL_ERROR_ONLY

} // namespace legends_ipc::msg
