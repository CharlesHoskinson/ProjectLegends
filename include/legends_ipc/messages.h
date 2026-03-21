// SPDX-License-Identifier: MIT
#ifndef LEGENDS_IPC_MESSAGES_H
#define LEGENDS_IPC_MESSAGES_H

#include <cstdint>
#include <cstring>
#include <expected>
#include <span>
#include <string>
#include <vector>
#include <legends_ipc/ipc_error.h>
#include <legends_ipc/message_types.h>
#include <legends_ipc/wire_format.h>

namespace legends_ipc::msg {

// ── Control messages ────────────────────────────────────────────────────────

struct Handshake {
    static constexpr MsgType type = MsgType::Handshake;
    uint32_t protocol_version  = 1;
    uint32_t max_fb_width      = 1920;
    uint32_t max_fb_height     = 1080;
    uint32_t audio_ring_frames = 2048;

    static constexpr size_t serialized_size = 16;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<Handshake, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct HandshakeAck {
    static constexpr MsgType type = MsgType::HandshakeAck;
    uint32_t protocol_version = 1;
    uint32_t engine_version   = 0; // LEGENDS_API_VERSION packed
    int32_t  error_code       = 0;

    static constexpr size_t serialized_size = 12;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<HandshakeAck, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct ShutdownMsg {
    static constexpr MsgType type = MsgType::Shutdown;
    uint32_t reason = 0; // 0 = normal

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<ShutdownMsg, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct ShutdownAckMsg {
    static constexpr MsgType type = MsgType::ShutdownAck;
    int32_t error_code = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<ShutdownAckMsg, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct HeartbeatMsg {
    static constexpr MsgType type = MsgType::Heartbeat;
    uint64_t timestamp_us = 0;

    static constexpr size_t serialized_size = 8;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<HeartbeatMsg, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct HeartbeatAckMsg {
    static constexpr MsgType type = MsgType::HeartbeatAck;
    uint64_t timestamp_us = 0;

    static constexpr size_t serialized_size = 8;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<HeartbeatAckMsg, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct ErrorResponseMsg {
    static constexpr MsgType type = MsgType::ErrorResponse;
    int32_t error_code = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<ErrorResponseMsg, IpcError> deserialize(std::span<const uint8_t> buf);
};

// ── Lifecycle messages ──────────────────────────────────────────────────────

struct GetApiVersionReq {
    static constexpr MsgType type = MsgType::GetApiVersionReq;
    static constexpr size_t serialized_size = 0;
    void serialize(std::span<uint8_t>) const {}
    [[nodiscard]] static std::expected<GetApiVersionReq, IpcError> deserialize(std::span<const uint8_t>) {
        return GetApiVersionReq{};
    }
};

struct GetApiVersionResp {
    static constexpr MsgType type = MsgType::GetApiVersionResp;
    uint32_t major = 0;
    uint32_t minor = 0;
    uint32_t patch = 0;
    int32_t  error_code = 0;

    static constexpr size_t serialized_size = 16;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<GetApiVersionResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct CreateReq {
    static constexpr MsgType type = MsgType::CreateReq;
    // Config fields sent inline
    uint32_t memory_kb     = 640;
    uint32_t xms_kb        = 0;
    uint32_t ems_kb        = 0;
    uint32_t cpu_cycles    = 0;
    uint8_t  cpu_type      = 0;
    uint8_t  machine_type  = 0;
    uint8_t  deterministic = 1;
    uint8_t  _pad          = 0;

    static constexpr size_t serialized_size = 20;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<CreateReq, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct CreateResp {
    static constexpr MsgType type = MsgType::CreateResp;
    int32_t error_code = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<CreateResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct DestroyReq {
    static constexpr MsgType type = MsgType::DestroyReq;
    static constexpr size_t serialized_size = 0;
    void serialize(std::span<uint8_t>) const {}
    [[nodiscard]] static std::expected<DestroyReq, IpcError> deserialize(std::span<const uint8_t>) {
        return DestroyReq{};
    }
};

struct DestroyResp {
    static constexpr MsgType type = MsgType::DestroyResp;
    int32_t error_code = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<DestroyResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct ResetReq {
    static constexpr MsgType type = MsgType::ResetReq;
    static constexpr size_t serialized_size = 0;
    void serialize(std::span<uint8_t>) const {}
    [[nodiscard]] static std::expected<ResetReq, IpcError> deserialize(std::span<const uint8_t>) {
        return ResetReq{};
    }
};

struct ResetResp {
    static constexpr MsgType type = MsgType::ResetResp;
    int32_t error_code = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<ResetResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

// ── Stepping messages ───────────────────────────────────────────────────────

struct StepMsReq {
    static constexpr MsgType type = MsgType::StepMsReq;
    uint32_t ms = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<StepMsReq, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct StepMsResp {
    static constexpr MsgType type = MsgType::StepMsResp;
    int32_t  error_code       = 0;
    uint64_t cycles_executed  = 0;
    uint64_t emu_time_us      = 0;
    uint32_t stop_reason      = 0;
    uint32_t events_processed = 0;

    static constexpr size_t serialized_size = 28;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<StepMsResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct StepCyclesReq {
    static constexpr MsgType type = MsgType::StepCyclesReq;
    uint64_t cycles = 0;

    static constexpr size_t serialized_size = 8;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<StepCyclesReq, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct StepCyclesResp {
    static constexpr MsgType type = MsgType::StepCyclesResp;
    int32_t  error_code       = 0;
    uint64_t cycles_executed  = 0;
    uint64_t emu_time_us      = 0;
    uint32_t stop_reason      = 0;
    uint32_t events_processed = 0;

    static constexpr size_t serialized_size = 28;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<StepCyclesResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct GetEmuTimeReq {
    static constexpr MsgType type = MsgType::GetEmuTimeReq;
    static constexpr size_t serialized_size = 0;
    void serialize(std::span<uint8_t>) const {}
    [[nodiscard]] static std::expected<GetEmuTimeReq, IpcError> deserialize(std::span<const uint8_t>) {
        return GetEmuTimeReq{};
    }
};

struct GetEmuTimeResp {
    static constexpr MsgType type = MsgType::GetEmuTimeResp;
    int32_t  error_code = 0;
    uint64_t time_us    = 0;

    static constexpr size_t serialized_size = 12;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<GetEmuTimeResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct GetTotalCyclesReq {
    static constexpr MsgType type = MsgType::GetTotalCyclesReq;
    static constexpr size_t serialized_size = 0;
    void serialize(std::span<uint8_t>) const {}
    [[nodiscard]] static std::expected<GetTotalCyclesReq, IpcError> deserialize(std::span<const uint8_t>) {
        return GetTotalCyclesReq{};
    }
};

struct GetTotalCyclesResp {
    static constexpr MsgType type = MsgType::GetTotalCyclesResp;
    int32_t  error_code = 0;
    uint64_t cycles     = 0;

    static constexpr size_t serialized_size = 12;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<GetTotalCyclesResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

// ── Input messages ──────────────────────────────────────────────────────────

struct KeyEventReq {
    static constexpr MsgType type = MsgType::KeyEventReq;
    uint8_t scancode = 0;
    uint8_t is_down  = 0;

    static constexpr size_t serialized_size = 2;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<KeyEventReq, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct KeyEventResp {
    static constexpr MsgType type = MsgType::KeyEventResp;
    int32_t error_code = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<KeyEventResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct MouseEventReq {
    static constexpr MsgType type = MsgType::MouseEventReq;
    int16_t delta_x = 0;
    int16_t delta_y = 0;
    uint8_t buttons = 0;

    static constexpr size_t serialized_size = 5;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<MouseEventReq, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct MouseEventResp {
    static constexpr MsgType type = MsgType::MouseEventResp;
    int32_t error_code = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<MouseEventResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

// ── Save/Load messages ──────────────────────────────────────────────────────

struct SaveStateReq {
    static constexpr MsgType type = MsgType::SaveStateReq;
    static constexpr size_t serialized_size = 0;
    void serialize(std::span<uint8_t>) const {}
    [[nodiscard]] static std::expected<SaveStateReq, IpcError> deserialize(std::span<const uint8_t>) {
        return SaveStateReq{};
    }
};

struct SaveStateResp {
    static constexpr MsgType type = MsgType::SaveStateResp;
    int32_t error_code = 0;
    uint32_t data_size = 0;
    // Payload bytes follow inline (variable length)

    static constexpr size_t serialized_size = 8; // fixed header part
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<SaveStateResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct LoadStateReq {
    static constexpr MsgType type = MsgType::LoadStateReq;
    uint32_t data_size = 0;
    // Payload bytes follow inline (variable length)

    static constexpr size_t serialized_size = 4; // fixed header part
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<LoadStateReq, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct LoadStateResp {
    static constexpr MsgType type = MsgType::LoadStateResp;
    int32_t error_code = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<LoadStateResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct GetStateHashReq {
    static constexpr MsgType type = MsgType::GetStateHashReq;
    static constexpr size_t serialized_size = 0;
    void serialize(std::span<uint8_t>) const {}
    [[nodiscard]] static std::expected<GetStateHashReq, IpcError> deserialize(std::span<const uint8_t>) {
        return GetStateHashReq{};
    }
};

struct GetStateHashResp {
    static constexpr MsgType type = MsgType::GetStateHashResp;
    int32_t error_code = 0;
    uint8_t hash[32]   = {};

    static constexpr size_t serialized_size = 36;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<GetStateHashResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

// ── String-carrying messages (common pattern) ───────────────────────────────

struct MountDriveReq {
    static constexpr MsgType type = MsgType::MountDriveReq;
    char     drive_letter = 'C';
    uint32_t flags        = 0;
    std::string host_path;

    [[nodiscard]] size_t serialized_size_dynamic() const { return 6 + host_path.size(); }
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<MountDriveReq, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct MountDriveResp {
    static constexpr MsgType type = MsgType::MountDriveResp;
    int32_t error_code = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<MountDriveResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct UnmountDriveReq {
    static constexpr MsgType type = MsgType::UnmountDriveReq;
    char drive_letter = 'C';

    static constexpr size_t serialized_size = 1;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<UnmountDriveReq, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct UnmountDriveResp {
    static constexpr MsgType type = MsgType::UnmountDriveResp;
    int32_t error_code = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<UnmountDriveResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

// ── Frame dirty / cursor ────────────────────────────────────────────────────

struct IsFrameDirtyReq {
    static constexpr MsgType type = MsgType::IsFrameDirtyReq;
    static constexpr size_t serialized_size = 0;
    void serialize(std::span<uint8_t>) const {}
    [[nodiscard]] static std::expected<IsFrameDirtyReq, IpcError> deserialize(std::span<const uint8_t>) {
        return IsFrameDirtyReq{};
    }
};

struct IsFrameDirtyResp {
    static constexpr MsgType type = MsgType::IsFrameDirtyResp;
    int32_t error_code = 0;
    uint8_t is_dirty   = 0;

    static constexpr size_t serialized_size = 5;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<IsFrameDirtyResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct GetCursorReq {
    static constexpr MsgType type = MsgType::GetCursorReq;
    static constexpr size_t serialized_size = 0;
    void serialize(std::span<uint8_t>) const {}
    [[nodiscard]] static std::expected<GetCursorReq, IpcError> deserialize(std::span<const uint8_t>) {
        return GetCursorReq{};
    }
};

struct GetCursorResp {
    static constexpr MsgType type = MsgType::GetCursorResp;
    int32_t error_code = 0;
    uint8_t x          = 0;
    uint8_t y          = 0;
    uint8_t visible    = 0;

    static constexpr size_t serialized_size = 7;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<GetCursorResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

// ── Audio active ────────────────────────────────────────────────────────────

struct IsAudioActiveReq {
    static constexpr MsgType type = MsgType::IsAudioActiveReq;
    static constexpr size_t serialized_size = 0;
    void serialize(std::span<uint8_t>) const {}
    [[nodiscard]] static std::expected<IsAudioActiveReq, IpcError> deserialize(std::span<const uint8_t>) {
        return IsAudioActiveReq{};
    }
};

struct IsAudioActiveResp {
    static constexpr MsgType type = MsgType::IsAudioActiveResp;
    int32_t error_code = 0;
    uint8_t is_active  = 0;

    static constexpr size_t serialized_size = 5;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<IsAudioActiveResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

} // namespace legends_ipc::msg

#endif // LEGENDS_IPC_MESSAGES_H
