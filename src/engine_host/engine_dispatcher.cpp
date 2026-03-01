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

    default: {
        ErrorResponseMsg resp;
        resp.error_code = LEGENDS_ERR_NOT_SUPPORTED;
        return DispatchResult{MsgType::ErrorResponse, serialize_resp(resp)};
    }

    } // switch
}

} // namespace legends::engine_host
