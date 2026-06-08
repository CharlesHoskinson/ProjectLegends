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
#include <legends/legends_embed.h>


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
    std::vector<uint8_t> state_bytes;

    [[nodiscard]] size_t serialized_size_dynamic() const { return 8 + state_bytes.size(); }
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<SaveStateResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct LoadStateReq {
    static constexpr MsgType type = MsgType::LoadStateReq;
    uint32_t data_size = 0;
    std::vector<uint8_t> state_bytes;

    [[nodiscard]] size_t serialized_size_dynamic() const { return 4 + state_bytes.size(); }
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

// ── Core Proxy Parity additions ──────────────────────────────────────────────

struct GetConfigReq {
    static constexpr MsgType type = MsgType::GetConfigReq;
    static constexpr size_t serialized_size = 0;
    void serialize(std::span<uint8_t>) const {}
    [[nodiscard]] static std::expected<GetConfigReq, IpcError> deserialize(std::span<const uint8_t>) {
        return GetConfigReq{};
    }
};

struct GetConfigResp {
    static constexpr MsgType type = MsgType::GetConfigResp;
    int32_t error_code = 0;
    uint32_t struct_size = 0;
    uint32_t api_version = 0;
    uint32_t memory_kb = 0;
    uint32_t xms_kb = 0;
    uint32_t ems_kb = 0;
    uint32_t cpu_cycles = 0;
    uint8_t cpu_type = 0;
    uint8_t machine_type = 0;
    uint8_t deterministic = 0;
    uint8_t _pad = 0;

    static constexpr size_t serialized_size = 32;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<GetConfigResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct CaptureTextReq {
    static constexpr MsgType type = MsgType::CaptureTextReq;
    uint32_t cells_count = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<CaptureTextReq, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct CaptureTextResp {
    static constexpr MsgType type = MsgType::CaptureTextResp;
    int32_t error_code = 0;
    uint32_t required_count = 0;
    uint8_t columns = 0;
    uint8_t rows = 0;
    uint8_t active_page = 0;
    uint8_t cursor_x = 0;
    uint8_t cursor_y = 0;
    uint8_t cursor_visible = 0;
    uint8_t cursor_start = 0;
    uint8_t cursor_end = 0;
    std::vector<legends_text_cell_t> cells;

    [[nodiscard]] size_t serialized_size_dynamic() const {
        return 16 + cells.size() * 2;
    }
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<CaptureTextResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct VerifyDeterminismReq {
    static constexpr MsgType type = MsgType::VerifyDeterminismReq;
    uint64_t test_cycles = 0;

    static constexpr size_t serialized_size = 8;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<VerifyDeterminismReq, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct VerifyDeterminismResp {
    static constexpr MsgType type = MsgType::VerifyDeterminismResp;
    int32_t error_code = 0;
    int32_t is_deterministic = 0;

    static constexpr size_t serialized_size = 8;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<VerifyDeterminismResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct GetLastErrorReq {
    static constexpr MsgType type = MsgType::GetLastErrorReq;
    static constexpr size_t serialized_size = 0;
    void serialize(std::span<uint8_t>) const {}
    [[nodiscard]] static std::expected<GetLastErrorReq, IpcError> deserialize(std::span<const uint8_t>) {
        return GetLastErrorReq{};
    }
};

struct GetLastErrorResp {
    static constexpr MsgType type = MsgType::GetLastErrorResp;
    int32_t error_code = 0;
    uint32_t required_len = 0;
    std::string error_msg;

    [[nodiscard]] size_t serialized_size_dynamic() const {
        return 8 + error_msg.size();
    }
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<GetLastErrorResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

// ── Device Command Proxy Parity additions ────────────────────────────────────

struct KeyEventExtReq {
    static constexpr MsgType type = MsgType::KeyEventExtReq;
    uint8_t scancode = 0;
    uint8_t is_down = 0;

    static constexpr size_t serialized_size = 2;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<KeyEventExtReq, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct KeyEventExtResp {
    static constexpr MsgType type = MsgType::KeyEventExtResp;
    int32_t error_code = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<KeyEventExtResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct TextInputReq {
    static constexpr MsgType type = MsgType::TextInputReq;
    std::string text;

    [[nodiscard]] size_t serialized_size_dynamic() const {
        return 4 + text.size();
    }
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<TextInputReq, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct TextInputResp {
    static constexpr MsgType type = MsgType::TextInputResp;
    int32_t error_code = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<TextInputResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct JoystickEventReq {
    static constexpr MsgType type = MsgType::JoystickEventReq;
    uint8_t joystick_id = 0;
    uint8_t axis_x = 0;
    uint8_t axis_y = 0;
    uint8_t buttons = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<JoystickEventReq, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct JoystickEventResp {
    static constexpr MsgType type = MsgType::JoystickEventResp;
    int32_t error_code = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<JoystickEventResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct MidiSetDeviceReq {
    static constexpr MsgType type = MsgType::MidiSetDeviceReq;
    std::string device;

    [[nodiscard]] size_t serialized_size_dynamic() const {
        return 4 + device.size();
    }
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<MidiSetDeviceReq, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct MidiSetDeviceResp {
    static constexpr MsgType type = MsgType::MidiSetDeviceResp;
    int32_t error_code = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<MidiSetDeviceResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct MidiSetSoundfontReq {
    static constexpr MsgType type = MsgType::MidiSetSoundfontReq;
    std::string soundfont;

    [[nodiscard]] size_t serialized_size_dynamic() const {
        return 4 + soundfont.size();
    }
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<MidiSetSoundfontReq, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct MidiSetSoundfontResp {
    static constexpr MsgType type = MsgType::MidiSetSoundfontResp;
    int32_t error_code = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<MidiSetSoundfontResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct MidiSetRomdirReq {
    static constexpr MsgType type = MsgType::MidiSetRomdirReq;
    std::string romdir;

    [[nodiscard]] size_t serialized_size_dynamic() const {
        return 4 + romdir.size();
    }
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<MidiSetRomdirReq, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct MidiSetRomdirResp {
    static constexpr MsgType type = MsgType::MidiSetRomdirResp;
    int32_t error_code = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<MidiSetRomdirResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct CaptureMidiAudioReq {
    static constexpr MsgType type = MsgType::CaptureMidiAudioReq;
    uint32_t buffer_count = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<CaptureMidiAudioReq, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct CaptureMidiAudioResp {
    static constexpr MsgType type = MsgType::CaptureMidiAudioResp;
    int32_t error_code = 0;
    uint32_t required_count = 0;
    std::vector<int16_t> audio_data;

    [[nodiscard]] size_t serialized_size_dynamic() const {
        return 8 + audio_data.size() * 2;
    }
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<CaptureMidiAudioResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct PrinterSetOutputReq {
    static constexpr MsgType type = MsgType::PrinterSetOutputReq;
    std::string output_path;

    [[nodiscard]] size_t serialized_size_dynamic() const {
        return 4 + output_path.size();
    }
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<PrinterSetOutputReq, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct PrinterSetOutputResp {
    static constexpr MsgType type = MsgType::PrinterSetOutputResp;
    int32_t error_code = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<PrinterSetOutputResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct PrinterIsActiveReq {
    static constexpr MsgType type = MsgType::PrinterIsActiveReq;
    static constexpr size_t serialized_size = 0;
    void serialize(std::span<uint8_t>) const {}
    [[nodiscard]] static std::expected<PrinterIsActiveReq, IpcError> deserialize(std::span<const uint8_t>) {
        return PrinterIsActiveReq{};
    }
};

struct PrinterIsActiveResp {
    static constexpr MsgType type = MsgType::PrinterIsActiveResp;
    int32_t error_code = 0;
    int32_t is_active = 0;

    static constexpr size_t serialized_size = 8;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<PrinterIsActiveResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct PrinterFlushReq {
    static constexpr MsgType type = MsgType::PrinterFlushReq;
    static constexpr size_t serialized_size = 0;
    void serialize(std::span<uint8_t>) const {}
    [[nodiscard]] static std::expected<PrinterFlushReq, IpcError> deserialize(std::span<const uint8_t>) {
        return PrinterFlushReq{};
    }
};

struct PrinterFlushResp {
    static constexpr MsgType type = MsgType::PrinterFlushResp;
    int32_t error_code = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<PrinterFlushResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct IpxEnableReq {
    static constexpr MsgType type = MsgType::IpxEnableReq;
    int32_t enable = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<IpxEnableReq, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct IpxEnableResp {
    static constexpr MsgType type = MsgType::IpxEnableResp;
    int32_t error_code = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<IpxEnableResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct IpxConnectReq {
    static constexpr MsgType type = MsgType::IpxConnectReq;
    uint16_t port = 0;
    std::string server;

    [[nodiscard]] size_t serialized_size_dynamic() const {
        return 6 + server.size();
    }
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<IpxConnectReq, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct IpxConnectResp {
    static constexpr MsgType type = MsgType::IpxConnectResp;
    int32_t error_code = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<IpxConnectResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct IpxDisconnectReq {
    static constexpr MsgType type = MsgType::IpxDisconnectReq;
    static constexpr size_t serialized_size = 0;
    void serialize(std::span<uint8_t>) const {}
    [[nodiscard]] static std::expected<IpxDisconnectReq, IpcError> deserialize(std::span<const uint8_t>) {
        return IpxDisconnectReq{};
    }
};

struct IpxDisconnectResp {
    static constexpr MsgType type = MsgType::IpxDisconnectResp;
    int32_t error_code = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<IpxDisconnectResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct IpxIsConnectedReq {
    static constexpr MsgType type = MsgType::IpxIsConnectedReq;
    static constexpr size_t serialized_size = 0;
    void serialize(std::span<uint8_t>) const {}
    [[nodiscard]] static std::expected<IpxIsConnectedReq, IpcError> deserialize(std::span<const uint8_t>) {
        return IpxIsConnectedReq{};
    }
};

struct IpxIsConnectedResp {
    static constexpr MsgType type = MsgType::IpxIsConnectedResp;
    int32_t error_code = 0;
    int32_t is_connected = 0;

    static constexpr size_t serialized_size = 8;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<IpxIsConnectedResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct GlideEnableReq {
    static constexpr MsgType type = MsgType::GlideEnableReq;
    int32_t enable = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<GlideEnableReq, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct GlideEnableResp {
    static constexpr MsgType type = MsgType::GlideEnableResp;
    int32_t error_code = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<GlideEnableResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct GlideSetResolutionReq {
    static constexpr MsgType type = MsgType::GlideSetResolutionReq;
    uint16_t width = 0;
    uint16_t height = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<GlideSetResolutionReq, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct GlideSetResolutionResp {
    static constexpr MsgType type = MsgType::GlideSetResolutionResp;
    int32_t error_code = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<GlideSetResolutionResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct SetMachinePc98Req {
    static constexpr MsgType type = MsgType::SetMachinePc98Req;
    int32_t enable = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<SetMachinePc98Req, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct SetMachinePc98Resp {
    static constexpr MsgType type = MsgType::SetMachinePc98Resp;
    int32_t error_code = 0;

    static constexpr size_t serialized_size = 4;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<SetMachinePc98Resp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct IsPc98ModeReq {
    static constexpr MsgType type = MsgType::IsPc98ModeReq;
    static constexpr size_t serialized_size = 0;
    void serialize(std::span<uint8_t>) const {}
    [[nodiscard]] static std::expected<IsPc98ModeReq, IpcError> deserialize(std::span<const uint8_t>) {
        return IsPc98ModeReq{};
    }
};

struct IsPc98ModeResp {
    static constexpr MsgType type = MsgType::IsPc98ModeResp;
    int32_t error_code = 0;
    int32_t is_pc98 = 0;

    static constexpr size_t serialized_size = 8;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<IsPc98ModeResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct HasCapabilityReq {
    static constexpr MsgType type = MsgType::HasCapabilityReq;
    std::string name;

    [[nodiscard]] size_t serialized_size_dynamic() const {
        return 4 + name.size();
    }
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<HasCapabilityReq, IpcError> deserialize(std::span<const uint8_t> buf);
};

struct HasCapabilityResp {
    static constexpr MsgType type = MsgType::HasCapabilityResp;
    int32_t error_code = 0;
    int32_t has_cap = 0;

    static constexpr size_t serialized_size = 8;
    void serialize(std::span<uint8_t> buf) const;
    [[nodiscard]] static std::expected<HasCapabilityResp, IpcError> deserialize(std::span<const uint8_t> buf);
};

} // namespace legends_ipc::msg

#endif // LEGENDS_IPC_MESSAGES_H
