// SPDX-License-Identifier: GPL-2.0-or-later
#include "engine_dispatcher.h"
#include <legends_ipc/messages.h>
#include <legends/legends_embed.h>
#include <cstring>

namespace legends::engine_host {

using namespace legends_ipc;
using namespace legends_ipc::msg;

// Singleton handle (engine host has one instance).
static legends_handle g_handle = nullptr;

namespace {

template<typename Resp>
std::vector<uint8_t> serialize_resp(const Resp& resp) {
    std::vector<uint8_t> buf(Resp::serialized_size);
    resp.serialize(buf);
    return buf;
}

template<typename Resp>
std::vector<uint8_t> serialize_resp_dynamic(const Resp& resp) {
    std::vector<uint8_t> buf(resp.serialized_size_dynamic());
    resp.serialize(buf);
    return buf;
}

} // anonymous namespace


std::expected<DispatchResult, IpcError>
dispatch(MsgType msg_type, std::span<const uint8_t> payload) {

    switch (msg_type) {

    case MsgType::GetApiVersionReq: {
        uint32_t major, minor, patch;
        auto err = legends_get_api_version(&major, &minor, &patch);
        GetApiVersionResp resp;
        resp.major = major; resp.minor = minor; resp.patch = patch;
        resp.error_code = err;
        return DispatchResult{MsgType::GetApiVersionResp, serialize_resp(resp)};
    }

    case MsgType::CreateReq: {
        auto req = CreateReq::deserialize(payload);
        if (!req) return std::unexpected(req.error());

        legends_config_t config = LEGENDS_CONFIG_INIT;
        config.memory_kb     = req->memory_kb;
        config.xms_kb        = req->xms_kb;
        config.ems_kb        = req->ems_kb;
        config.cpu_cycles    = req->cpu_cycles;
        config.cpu_type      = req->cpu_type;
        config.machine_type  = req->machine_type;
        config.deterministic = req->deterministic;

        auto err = legends_create(&config, &g_handle);
        CreateResp resp;
        resp.error_code = err;
        return DispatchResult{MsgType::CreateResp, serialize_resp(resp)};
    }

    case MsgType::DestroyReq: {
        auto err = legends_destroy(g_handle);
        g_handle = nullptr;
        DestroyResp resp;
        resp.error_code = err;
        return DispatchResult{MsgType::DestroyResp, serialize_resp(resp)};
    }

    case MsgType::ResetReq: {
        auto err = legends_reset(g_handle);
        ResetResp resp;
        resp.error_code = err;
        return DispatchResult{MsgType::ResetResp, serialize_resp(resp)};
    }

    case MsgType::StepMsReq: {
        auto req = StepMsReq::deserialize(payload);
        if (!req) return std::unexpected(req.error());

        legends_step_result_t result{};
        auto err = legends_step_ms(g_handle, req->ms, &result);
        StepMsResp resp;
        resp.error_code = err;
        resp.cycles_executed = result.cycles_executed;
        resp.emu_time_us = result.emu_time_us;
        resp.stop_reason = result.stop_reason;
        resp.events_processed = result.events_processed;
        return DispatchResult{MsgType::StepMsResp, serialize_resp(resp)};
    }

    case MsgType::StepCyclesReq: {
        auto req = StepCyclesReq::deserialize(payload);
        if (!req) return std::unexpected(req.error());

        legends_step_result_t result{};
        auto err = legends_step_cycles(g_handle, req->cycles, &result);
        StepCyclesResp resp;
        resp.error_code = err;
        resp.cycles_executed = result.cycles_executed;
        resp.emu_time_us = result.emu_time_us;
        resp.stop_reason = result.stop_reason;
        resp.events_processed = result.events_processed;
        return DispatchResult{MsgType::StepCyclesResp, serialize_resp(resp)};
    }

    case MsgType::GetEmuTimeReq: {
        uint64_t time_us = 0;
        auto err = legends_get_emu_time(g_handle, &time_us);
        GetEmuTimeResp resp;
        resp.error_code = err;
        resp.time_us = time_us;
        return DispatchResult{MsgType::GetEmuTimeResp, serialize_resp(resp)};
    }

    case MsgType::GetTotalCyclesReq: {
        uint64_t cycles = 0;
        auto err = legends_get_total_cycles(g_handle, &cycles);
        GetTotalCyclesResp resp;
        resp.error_code = err;
        resp.cycles = cycles;
        return DispatchResult{MsgType::GetTotalCyclesResp, serialize_resp(resp)};
    }

    case MsgType::KeyEventReq: {
        auto req = KeyEventReq::deserialize(payload);
        if (!req) return std::unexpected(req.error());
        auto err = legends_key_event(g_handle, req->scancode, req->is_down);
        KeyEventResp resp;
        resp.error_code = err;
        return DispatchResult{MsgType::KeyEventResp, serialize_resp(resp)};
    }

    case MsgType::MouseEventReq: {
        auto req = MouseEventReq::deserialize(payload);
        if (!req) return std::unexpected(req.error());
        auto err = legends_mouse_event(g_handle, req->delta_x, req->delta_y, req->buttons);
        MouseEventResp resp;
        resp.error_code = err;
        return DispatchResult{MsgType::MouseEventResp, serialize_resp(resp)};
    }

    case MsgType::IsFrameDirtyReq: {
        int dirty = 0;
        auto err = legends_is_frame_dirty(g_handle, &dirty);
        IsFrameDirtyResp resp;
        resp.error_code = err;
        resp.is_dirty = static_cast<uint8_t>(dirty);
        return DispatchResult{MsgType::IsFrameDirtyResp, serialize_resp(resp)};
    }

    case MsgType::GetCursorReq: {
        uint8_t x = 0, y = 0;
        int visible = 0;
        auto err = legends_get_cursor(g_handle, &x, &y, &visible);
        GetCursorResp resp;
        resp.error_code = err;
        resp.x = x; resp.y = y;
        resp.visible = static_cast<uint8_t>(visible);
        return DispatchResult{MsgType::GetCursorResp, serialize_resp(resp)};
    }

    case MsgType::IsAudioActiveReq: {
        int active = 0;
        auto err = legends_is_audio_active(g_handle, &active);
        IsAudioActiveResp resp;
        resp.error_code = err;
        resp.is_active = static_cast<uint8_t>(active);
        return DispatchResult{MsgType::IsAudioActiveResp, serialize_resp(resp)};
    }

    case MsgType::GetStateHashReq: {
        GetStateHashResp resp;
        auto err = legends_get_state_hash(g_handle, resp.hash);
        resp.error_code = err;
        return DispatchResult{MsgType::GetStateHashResp, serialize_resp(resp)};
    }

    case MsgType::MountDriveReq: {
        auto req = MountDriveReq::deserialize(payload);
        if (!req) return std::unexpected(req.error());
        auto err = legends_mount_drive(g_handle, req->drive_letter, req->host_path.c_str(), req->flags);
        MountDriveResp resp;
        resp.error_code = err;
        return DispatchResult{MsgType::MountDriveResp, serialize_resp(resp)};
    }

    case MsgType::UnmountDriveReq: {
        auto req = UnmountDriveReq::deserialize(payload);
        if (!req) return std::unexpected(req.error());
        auto err = legends_unmount_drive(g_handle, req->drive_letter);
        UnmountDriveResp resp;
        resp.error_code = err;
        return DispatchResult{MsgType::UnmountDriveResp, serialize_resp(resp)};
    }

    case MsgType::Shutdown: {
        if (g_handle) {
            legends_destroy(g_handle);
            g_handle = nullptr;
        }
        ShutdownAckMsg resp;
        resp.error_code = 0;
        return DispatchResult{MsgType::ShutdownAck, serialize_resp(resp)};
    }

    case MsgType::Heartbeat: {
        auto req = HeartbeatMsg::deserialize(payload);
        HeartbeatAckMsg resp;
        resp.timestamp_us = req.has_value() ? req->timestamp_us : 0;
        return DispatchResult{MsgType::HeartbeatAck, serialize_resp(resp)};
    }

    case MsgType::GetConfigReq: {
        legends_config_t config{};
        auto err = legends_get_config(g_handle, &config);
        GetConfigResp resp;
        resp.error_code = err;
        if (err == LEGENDS_OK) {
            resp.struct_size = config.struct_size;
            resp.api_version = config.api_version;
            resp.memory_kb = config.memory_kb;
            resp.xms_kb = config.xms_kb;
            resp.ems_kb = config.ems_kb;
            resp.cpu_cycles = config.cpu_cycles;
            resp.cpu_type = config.cpu_type;
            resp.machine_type = config.machine_type;
            resp.deterministic = config.deterministic;
        }
        return DispatchResult{MsgType::GetConfigResp, serialize_resp(resp)};
    }

    case MsgType::CaptureTextReq: {
        auto req = CaptureTextReq::deserialize(payload);
        if (!req) return std::unexpected(req.error());

        CaptureTextResp resp;
        legends_text_info_t info{};
        size_t needed = 0;
        auto err = legends_capture_text(g_handle, nullptr, 0, &needed, &info);

        resp.error_code = err;
        resp.required_count = static_cast<uint32_t>(needed);
        resp.columns = info.columns;
        resp.rows = info.rows;
        resp.active_page = info.active_page;
        resp.cursor_x = info.cursor_x;
        resp.cursor_y = info.cursor_y;
        resp.cursor_visible = info.cursor_visible;
        resp.cursor_start = info.cursor_start;
        resp.cursor_end = info.cursor_end;

        if (err == LEGENDS_OK && req->cells_count > 0) {
            if (req->cells_count < needed) {
                resp.error_code = LEGENDS_ERR_BUFFER_TOO_SMALL;
            } else {
                std::vector<legends_text_cell_t> cells(needed);
                err = legends_capture_text(g_handle, cells.data(), cells.size(), &needed, &info);
                resp.error_code = err;
                resp.required_count = static_cast<uint32_t>(needed);
                if (err == LEGENDS_OK) {
                    if (needed < cells.size()) {
                        cells.resize(needed);
                    }
                    resp.cells = std::move(cells);
                }
            }
        }
        return DispatchResult{MsgType::CaptureTextResp, serialize_resp_dynamic(resp)};
    }

    case MsgType::VerifyDeterminismReq: {
        auto req = VerifyDeterminismReq::deserialize(payload);
        if (!req) return std::unexpected(req.error());

        int is_det = 0;
        auto err = legends_verify_determinism(g_handle, req->test_cycles, &is_det);
        VerifyDeterminismResp resp;
        resp.error_code = err;
        resp.is_deterministic = is_det;
        return DispatchResult{MsgType::VerifyDeterminismResp, serialize_resp(resp)};
    }

    case MsgType::GetLastErrorReq: {
        size_t needed = 0;
        auto err = legends_get_last_error(g_handle, nullptr, 0, &needed);
        GetLastErrorResp resp;
        resp.error_code = err;
        resp.required_len = static_cast<uint32_t>(needed);
        if (err == LEGENDS_OK || err == LEGENDS_ERR_BUFFER_TOO_SMALL) {
            if (needed > 0) {
                std::string buf(needed, '\0');
                size_t actual = 0;
                err = legends_get_last_error(g_handle, buf.data(), buf.size(), &actual);
                resp.error_code = err;
                if (err == LEGENDS_OK) {
                    if (actual > 0 && buf[actual - 1] == '\0') {
                        buf.resize(actual - 1);
                    } else {
                        buf.resize(actual);
                    }
                    resp.error_msg = std::move(buf);
                }
            }
        }
        return DispatchResult{MsgType::GetLastErrorResp, serialize_resp_dynamic(resp)};
    }

    case MsgType::KeyEventExtReq: {
        auto req = KeyEventExtReq::deserialize(payload);
        if (!req) return std::unexpected(req.error());
        auto err = legends_key_event_ext(g_handle, req->scancode, req->is_down);
        KeyEventExtResp resp;
        resp.error_code = err;
        return DispatchResult{MsgType::KeyEventExtResp, serialize_resp(resp)};
    }

    case MsgType::TextInputReq: {
        auto req = TextInputReq::deserialize(payload);
        if (!req) return std::unexpected(req.error());
        auto err = legends_text_input(g_handle, req->text.c_str());
        TextInputResp resp;
        resp.error_code = err;
        return DispatchResult{MsgType::TextInputResp, serialize_resp(resp)};
    }

    case MsgType::JoystickEventReq: {
        auto req = JoystickEventReq::deserialize(payload);
        if (!req) return std::unexpected(req.error());
        auto err = legends_joystick_event(g_handle, req->joystick_id, req->axis_x, req->axis_y, req->buttons);
        JoystickEventResp resp;
        resp.error_code = err;
        return DispatchResult{MsgType::JoystickEventResp, serialize_resp(resp)};
    }

    case MsgType::MidiSetDeviceReq: {
        auto req = MidiSetDeviceReq::deserialize(payload);
        if (!req) return std::unexpected(req.error());
        auto err = legends_midi_set_device(g_handle, req->device.c_str());
        MidiSetDeviceResp resp;
        resp.error_code = err;
        return DispatchResult{MsgType::MidiSetDeviceResp, serialize_resp(resp)};
    }

    case MsgType::MidiSetSoundfontReq: {
        auto req = MidiSetSoundfontReq::deserialize(payload);
        if (!req) return std::unexpected(req.error());
        auto err = legends_midi_set_soundfont(g_handle, req->soundfont.c_str());
        MidiSetSoundfontResp resp;
        resp.error_code = err;
        return DispatchResult{MsgType::MidiSetSoundfontResp, serialize_resp(resp)};
    }

    case MsgType::MidiSetRomdirReq: {
        auto req = MidiSetRomdirReq::deserialize(payload);
        if (!req) return std::unexpected(req.error());
        auto err = legends_midi_set_romdir(g_handle, req->romdir.c_str());
        MidiSetRomdirResp resp;
        resp.error_code = err;
        return DispatchResult{MsgType::MidiSetRomdirResp, serialize_resp(resp)};
    }

    case MsgType::CaptureMidiAudioReq: {
        auto req = CaptureMidiAudioReq::deserialize(payload);
        if (!req) return std::unexpected(req.error());

        CaptureMidiAudioResp resp;
        size_t out_count = 0;
        auto err = legends_capture_midi_audio(g_handle, nullptr, 0, &out_count);
        resp.error_code = err;
        resp.required_count = static_cast<uint32_t>(out_count);

        if (err == LEGENDS_OK && req->buffer_count > 0) {
            if (req->buffer_count < out_count) {
                resp.error_code = LEGENDS_ERR_BUFFER_TOO_SMALL;
            } else {
                std::vector<int16_t> audio(out_count);
                err = legends_capture_midi_audio(g_handle, audio.data(), audio.size(), &out_count);
                resp.error_code = err;
                resp.required_count = static_cast<uint32_t>(out_count);
                if (err == LEGENDS_OK) {
                    if (out_count < audio.size()) {
                        audio.resize(out_count);
                    }
                    resp.audio_data = std::move(audio);
                }
            }
        }
        return DispatchResult{MsgType::CaptureMidiAudioResp, serialize_resp_dynamic(resp)};
    }

    case MsgType::PrinterSetOutputReq: {
        auto req = PrinterSetOutputReq::deserialize(payload);
        if (!req) return std::unexpected(req.error());
        auto err = legends_printer_set_output(g_handle, req->output_path.c_str());
        PrinterSetOutputResp resp;
        resp.error_code = err;
        return DispatchResult{MsgType::PrinterSetOutputResp, serialize_resp(resp)};
    }

    case MsgType::PrinterIsActiveReq: {
        int active = 0;
        auto err = legends_printer_is_active(g_handle, &active);
        PrinterIsActiveResp resp;
        resp.error_code = err;
        resp.is_active = active;
        return DispatchResult{MsgType::PrinterIsActiveResp, serialize_resp(resp)};
    }

    case MsgType::PrinterFlushReq: {
        auto err = legends_printer_flush(g_handle);
        PrinterFlushResp resp;
        resp.error_code = err;
        return DispatchResult{MsgType::PrinterFlushResp, serialize_resp(resp)};
    }

    case MsgType::IpxEnableReq: {
        auto req = IpxEnableReq::deserialize(payload);
        if (!req) return std::unexpected(req.error());
        auto err = legends_ipx_enable(g_handle, req->enable);
        IpxEnableResp resp;
        resp.error_code = err;
        return DispatchResult{MsgType::IpxEnableResp, serialize_resp(resp)};
    }

    case MsgType::IpxConnectReq: {
        auto req = IpxConnectReq::deserialize(payload);
        if (!req) return std::unexpected(req.error());
        auto err = legends_ipx_connect(g_handle, req->server.c_str(), req->port);
        IpxConnectResp resp;
        resp.error_code = err;
        return DispatchResult{MsgType::IpxConnectResp, serialize_resp(resp)};
    }

    case MsgType::IpxDisconnectReq: {
        auto err = legends_ipx_disconnect(g_handle);
        IpxDisconnectResp resp;
        resp.error_code = err;
        return DispatchResult{MsgType::IpxDisconnectResp, serialize_resp(resp)};
    }

    case MsgType::IpxIsConnectedReq: {
        int connected = 0;
        auto err = legends_ipx_is_connected(g_handle, &connected);
        IpxIsConnectedResp resp;
        resp.error_code = err;
        resp.is_connected = connected;
        return DispatchResult{MsgType::IpxIsConnectedResp, serialize_resp(resp)};
    }

    case MsgType::GlideEnableReq: {
        auto req = GlideEnableReq::deserialize(payload);
        if (!req) return std::unexpected(req.error());
        auto err = legends_glide_enable(g_handle, req->enable);
        GlideEnableResp resp;
        resp.error_code = err;
        return DispatchResult{MsgType::GlideEnableResp, serialize_resp(resp)};
    }

    case MsgType::GlideSetResolutionReq: {
        auto req = GlideSetResolutionReq::deserialize(payload);
        if (!req) return std::unexpected(req.error());
        auto err = legends_glide_set_resolution(g_handle, req->width, req->height);
        GlideSetResolutionResp resp;
        resp.error_code = err;
        return DispatchResult{MsgType::GlideSetResolutionResp, serialize_resp(resp)};
    }

    case MsgType::SetMachinePc98Req: {
        auto req = SetMachinePc98Req::deserialize(payload);
        if (!req) return std::unexpected(req.error());
        auto err = legends_set_machine_pc98(g_handle, req->enable);
        SetMachinePc98Resp resp;
        resp.error_code = err;
        return DispatchResult{MsgType::SetMachinePc98Resp, serialize_resp(resp)};
    }

    case MsgType::IsPc98ModeReq: {
        int pc98 = 0;
        auto err = legends_is_pc98_mode(g_handle, &pc98);
        IsPc98ModeResp resp;
        resp.error_code = err;
        resp.is_pc98 = pc98;
        return DispatchResult{MsgType::IsPc98ModeResp, serialize_resp(resp)};
    }

    case MsgType::HasCapabilityReq: {
        auto req = HasCapabilityReq::deserialize(payload);
        if (!req) return std::unexpected(req.error());
        int has_cap = 0;
        auto err = legends_has_capability(g_handle, req->name.c_str(), &has_cap);
        HasCapabilityResp resp;
        resp.error_code = err;
        resp.has_cap = has_cap;
        return DispatchResult{MsgType::HasCapabilityResp, serialize_resp(resp)};
    }

    case MsgType::SaveStateReq: {
        size_t needed_size = 0;
        auto err = legends_save_state(g_handle, nullptr, 0, &needed_size);
        if (err == LEGENDS_OK || err == LEGENDS_ERR_BUFFER_TOO_SMALL || needed_size > 0) {
            std::vector<uint8_t> state(needed_size);
            size_t actual_size = 0;
            err = legends_save_state(g_handle, state.data(), state.size(), &actual_size);
            if (err == LEGENDS_OK) {
                state.resize(actual_size);
                SaveStateResp resp;
                resp.error_code = err;
                resp.data_size = static_cast<uint32_t>(actual_size);
                resp.state_bytes = std::move(state);
                return DispatchResult{MsgType::SaveStateResp, serialize_resp_dynamic(resp)};
            }
        }
        SaveStateResp resp;
        resp.error_code = err;
        resp.data_size = 0;
        return DispatchResult{MsgType::SaveStateResp, serialize_resp_dynamic(resp)};
    }

    case MsgType::LoadStateReq: {
        auto req = LoadStateReq::deserialize(payload);
        if (!req) return std::unexpected(req.error());
        auto err = legends_load_state(g_handle, req->state_bytes.data(), req->state_bytes.size());
        LoadStateResp resp;
        resp.error_code = err;
        return DispatchResult{MsgType::LoadStateResp, serialize_resp(resp)};
    }

    default: {
        ErrorResponseMsg resp;
        resp.error_code = LEGENDS_ERR_NOT_SUPPORTED;
        return DispatchResult{MsgType::ErrorResponse, serialize_resp(resp)};
    }

    } // switch
}

} // namespace legends::engine_host
