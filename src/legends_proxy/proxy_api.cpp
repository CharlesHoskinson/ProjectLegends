// SPDX-License-Identifier: MIT
//
// Proxy implementation of legends_embed.h that forwards all calls
// over IPC to the engine host process.

#include <legends/legends_embed.h>
#include "proxy_connection.h"
#include "ipc_error_mapping.h"
#include <legends_ipc/messages.h>
#include <cstring>
#include <vector>

using namespace legends_ipc;
using namespace legends_ipc::msg;
using namespace legends_proxy;

static ProxyConnection& conn() { return ProxyConnection::instance(); }

// Helper: serialize a message, send request, deserialize response.
#define PROXY_REQUEST(ReqType, RespType, req_msg)                             \
    do {                                                                       \
        if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;       \
        std::vector<uint8_t> _buf(ReqType::serialized_size);                  \
        req_msg.serialize(_buf);                                               \
        auto _resp = conn().request<RespType>(ReqType::type, _buf);           \
        if (!_resp) return map_ipc_error(_resp.error());                      \
        return _resp->error_code;                                              \
    } while (0)

#define PROXY_EMPTY_REQUEST(ReqType, RespType)                                \
    do {                                                                       \
        if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;       \
        auto _resp = conn().request<RespType>(ReqType::type, {});             \
        if (!_resp) return map_ipc_error(_resp.error());                      \
        return _resp->error_code;                                              \
    } while (0)

extern "C" {

LEGENDS_API legends_error_t legends_get_api_version(
    uint32_t* major, uint32_t* minor, uint32_t* patch)
{
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    auto resp = conn().request<GetApiVersionResp>(MsgType::GetApiVersionReq, {});
    if (!resp) return map_ipc_error(resp.error());
    if (major) *major = resp->major;
    if (minor) *minor = resp->minor;
    if (patch) *patch = resp->patch;
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_create(
    const legends_config_t* config, legends_handle* handle_out)
{
    if (!handle_out) return LEGENDS_ERR_NULL_POINTER;
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;

    CreateReq req;
    if (config) {
        req.memory_kb     = config->memory_kb;
        req.xms_kb        = config->xms_kb;
        req.ems_kb        = config->ems_kb;
        req.cpu_cycles    = config->cpu_cycles;
        req.cpu_type      = config->cpu_type;
        req.machine_type  = config->machine_type;
        req.deterministic = config->deterministic;
    }

    std::vector<uint8_t> buf(CreateReq::serialized_size);
    req.serialize(buf);
    auto resp = conn().request<CreateResp>(MsgType::CreateReq, buf);
    if (!resp) return map_ipc_error(resp.error());

    // Return a sentinel handle (proxy doesn't track real handles)
    if (resp->error_code == LEGENDS_OK)
        *handle_out = reinterpret_cast<legends_handle>(static_cast<uintptr_t>(1));
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_destroy(legends_handle) {
    PROXY_EMPTY_REQUEST(DestroyReq, DestroyResp);
}

LEGENDS_API legends_error_t legends_force_destroy(void) {
    PROXY_EMPTY_REQUEST(DestroyReq, DestroyResp);
}

LEGENDS_API legends_error_t legends_reset(legends_handle) {
    PROXY_EMPTY_REQUEST(ResetReq, ResetResp);
}

LEGENDS_API legends_error_t legends_get_config(legends_handle, legends_config_t*) {
    return LEGENDS_ERR_NOT_SUPPORTED; // Config is engine-side
}

LEGENDS_API legends_error_t legends_step_ms(
    legends_handle, uint32_t ms, legends_step_result_t* result_out)
{
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    StepMsReq req; req.ms = ms;
    std::vector<uint8_t> buf(StepMsReq::serialized_size);
    req.serialize(buf);
    auto resp = conn().request<StepMsResp>(MsgType::StepMsReq, buf);
    if (!resp) return map_ipc_error(resp.error());
    if (result_out) {
        result_out->cycles_executed = resp->cycles_executed;
        result_out->emu_time_us = resp->emu_time_us;
        result_out->stop_reason = resp->stop_reason;
        result_out->events_processed = resp->events_processed;
    }
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_step_cycles(
    legends_handle, uint64_t cycles, legends_step_result_t* result_out)
{
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    StepCyclesReq req; req.cycles = cycles;
    std::vector<uint8_t> buf(StepCyclesReq::serialized_size);
    req.serialize(buf);
    auto resp = conn().request<StepCyclesResp>(MsgType::StepCyclesReq, buf);
    if (!resp) return map_ipc_error(resp.error());
    if (result_out) {
        result_out->cycles_executed = resp->cycles_executed;
        result_out->emu_time_us = resp->emu_time_us;
        result_out->stop_reason = resp->stop_reason;
        result_out->events_processed = resp->events_processed;
    }
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_get_emu_time(legends_handle, uint64_t* time_us_out) {
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    auto resp = conn().request<GetEmuTimeResp>(MsgType::GetEmuTimeReq, {});
    if (!resp) return map_ipc_error(resp.error());
    if (time_us_out) *time_us_out = resp->time_us;
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_get_total_cycles(legends_handle, uint64_t* cycles_out) {
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    auto resp = conn().request<GetTotalCyclesResp>(MsgType::GetTotalCyclesReq, {});
    if (!resp) return map_ipc_error(resp.error());
    if (cycles_out) *cycles_out = resp->cycles;
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_capture_text(
    legends_handle, legends_text_cell_t*, size_t, size_t*, legends_text_info_t*)
{
    return LEGENDS_ERR_NOT_SUPPORTED; // Framebuffer capture via shared memory
}

LEGENDS_API legends_error_t legends_capture_rgb(
    legends_handle, uint8_t* buffer, size_t buffer_size,
    size_t* size_out, uint16_t* width_out, uint16_t* height_out)
{
    // Read from shared memory framebuffer
    auto* fb = conn().framebuffer();
    if (!fb) return LEGENDS_ERR_NOT_INITIALIZED;

    auto frame = fb->read_if_new(0); // Always read latest
    if (!frame) {
        if (size_out) *size_out = 0;
        return LEGENDS_OK;
    }
    if (size_out) *size_out = frame->pixels.size();
    if (width_out) *width_out = static_cast<uint16_t>(frame->width);
    if (height_out) *height_out = static_cast<uint16_t>(frame->height);
    if (buffer && buffer_size >= frame->pixels.size())
        std::memcpy(buffer, frame->pixels.data(), frame->pixels.size());
    return LEGENDS_OK;
}

LEGENDS_API legends_error_t legends_is_frame_dirty(legends_handle, int* dirty_out) {
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    auto resp = conn().request<IsFrameDirtyResp>(MsgType::IsFrameDirtyReq, {});
    if (!resp) return map_ipc_error(resp.error());
    if (dirty_out) *dirty_out = resp->is_dirty;
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_get_cursor(
    legends_handle, uint8_t* x_out, uint8_t* y_out, int* visible_out)
{
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    auto resp = conn().request<GetCursorResp>(MsgType::GetCursorReq, {});
    if (!resp) return map_ipc_error(resp.error());
    if (x_out) *x_out = resp->x;
    if (y_out) *y_out = resp->y;
    if (visible_out) *visible_out = resp->visible;
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_key_event(legends_handle, uint8_t scancode, int is_down) {
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    KeyEventReq req;
    req.scancode = scancode;
    req.is_down = static_cast<uint8_t>(is_down);
    std::vector<uint8_t> buf(KeyEventReq::serialized_size);
    req.serialize(buf);
    auto resp = conn().request<KeyEventResp>(MsgType::KeyEventReq, buf);
    if (!resp) return map_ipc_error(resp.error());
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_key_event_ext(legends_handle h, uint8_t scancode, int is_down) {
    return legends_key_event(h, scancode, is_down); // Same IPC path
}

LEGENDS_API legends_error_t legends_text_input(legends_handle, const char*) {
    return LEGENDS_ERR_NOT_SUPPORTED; // Complex; deferred
}

LEGENDS_API legends_error_t legends_mouse_event(
    legends_handle, int16_t delta_x, int16_t delta_y, uint8_t buttons)
{
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    MouseEventReq req;
    req.delta_x = delta_x; req.delta_y = delta_y; req.buttons = buttons;
    std::vector<uint8_t> buf(MouseEventReq::serialized_size);
    req.serialize(buf);
    auto resp = conn().request<MouseEventResp>(MsgType::MouseEventReq, buf);
    if (!resp) return map_ipc_error(resp.error());
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_capture_audio(
    legends_handle, int16_t* buffer, size_t buffer_count, size_t* count_out)
{
    auto* ring = conn().audio_ring();
    if (!ring) return LEGENDS_ERR_NOT_INITIALIZED;
    if (!buffer) {
        if (count_out) *count_out = ring->available() * ring->channels();
        return LEGENDS_OK;
    }
    uint32_t frames = ring->pop(std::span<int16_t>(buffer, buffer_count));
    if (count_out) *count_out = frames * ring->channels();
    return LEGENDS_OK;
}

LEGENDS_API legends_error_t legends_is_audio_active(legends_handle, int* active_out) {
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    auto resp = conn().request<IsAudioActiveResp>(MsgType::IsAudioActiveReq, {});
    if (!resp) return map_ipc_error(resp.error());
    if (active_out) *active_out = resp->is_active;
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_save_state(legends_handle, void*, size_t, size_t*) {
    return LEGENDS_ERR_NOT_SUPPORTED; // Complex; uses control channel
}

LEGENDS_API legends_error_t legends_load_state(legends_handle, const void*, size_t) {
    return LEGENDS_ERR_NOT_SUPPORTED;
}

LEGENDS_API legends_error_t legends_get_state_hash(legends_handle, uint8_t hash_out[32]) {
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    auto resp = conn().request<GetStateHashResp>(MsgType::GetStateHashReq, {});
    if (!resp) return map_ipc_error(resp.error());
    if (hash_out) std::memcpy(hash_out, resp->hash, 32);
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_verify_determinism(legends_handle, uint64_t, int*) {
    return LEGENDS_ERR_NOT_SUPPORTED;
}

LEGENDS_API legends_error_t legends_get_last_error(legends_handle, char*, size_t, size_t*) {
    return LEGENDS_ERR_NOT_SUPPORTED;
}

LEGENDS_API legends_error_t legends_set_log_callback(legends_handle, legends_log_callback_t, void*) {
    return LEGENDS_ERR_NOT_SUPPORTED;
}

LEGENDS_API legends_error_t legends_mount_drive(legends_handle, char drive_letter, const char* host_path, uint32_t flags) {
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    MountDriveReq req;
    req.drive_letter = drive_letter;
    req.flags = flags;
    req.host_path = host_path ? host_path : "";
    std::vector<uint8_t> buf(req.serialized_size_dynamic());
    req.serialize(buf);
    auto resp = conn().request<MountDriveResp>(MsgType::MountDriveReq, buf);
    if (!resp) return map_ipc_error(resp.error());
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_unmount_drive(legends_handle, char drive_letter) {
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    UnmountDriveReq req; req.drive_letter = drive_letter;
    std::vector<uint8_t> buf(UnmountDriveReq::serialized_size);
    req.serialize(buf);
    auto resp = conn().request<UnmountDriveResp>(MsgType::UnmountDriveReq, buf);
    if (!resp) return map_ipc_error(resp.error());
    return resp->error_code;
}

// Phase 2+ functions — stub as not-supported over IPC for now
LEGENDS_API legends_error_t legends_start_video_capture(legends_handle, const char*) { return LEGENDS_ERR_NOT_SUPPORTED; }
LEGENDS_API legends_error_t legends_stop_video_capture(legends_handle) { return LEGENDS_ERR_NOT_SUPPORTED; }
LEGENDS_API legends_error_t legends_is_video_capturing(legends_handle, int*) { return LEGENDS_ERR_NOT_SUPPORTED; }
LEGENDS_API legends_error_t legends_joystick_event(legends_handle, uint8_t, uint8_t, uint8_t, uint8_t) { return LEGENDS_ERR_NOT_SUPPORTED; }
LEGENDS_API legends_error_t legends_midi_set_device(legends_handle, const char*) { return LEGENDS_ERR_NOT_SUPPORTED; }
LEGENDS_API legends_error_t legends_midi_set_soundfont(legends_handle, const char*) { return LEGENDS_ERR_NOT_SUPPORTED; }
LEGENDS_API legends_error_t legends_midi_set_romdir(legends_handle, const char*) { return LEGENDS_ERR_NOT_SUPPORTED; }
LEGENDS_API legends_error_t legends_capture_midi_audio(legends_handle, int16_t*, size_t, size_t*) { return LEGENDS_ERR_NOT_SUPPORTED; }
LEGENDS_API legends_error_t legends_printer_set_output(legends_handle, const char*) { return LEGENDS_ERR_NOT_SUPPORTED; }
LEGENDS_API legends_error_t legends_printer_is_active(legends_handle, int*) { return LEGENDS_ERR_NOT_SUPPORTED; }
LEGENDS_API legends_error_t legends_printer_flush(legends_handle) { return LEGENDS_ERR_NOT_SUPPORTED; }
LEGENDS_API legends_error_t legends_set_ttf_font(legends_handle, const char*, uint32_t) { return LEGENDS_ERR_NOT_SUPPORTED; }
LEGENDS_API legends_error_t legends_ipx_enable(legends_handle, int) { return LEGENDS_ERR_NOT_SUPPORTED; }
LEGENDS_API legends_error_t legends_ipx_connect(legends_handle, const char*, uint16_t) { return LEGENDS_ERR_NOT_SUPPORTED; }
LEGENDS_API legends_error_t legends_ipx_disconnect(legends_handle) { return LEGENDS_ERR_NOT_SUPPORTED; }
LEGENDS_API legends_error_t legends_ipx_is_connected(legends_handle, int*) { return LEGENDS_ERR_NOT_SUPPORTED; }
LEGENDS_API legends_error_t legends_glide_enable(legends_handle, int) { return LEGENDS_ERR_NOT_SUPPORTED; }
LEGENDS_API legends_error_t legends_glide_set_resolution(legends_handle, uint16_t, uint16_t) { return LEGENDS_ERR_NOT_SUPPORTED; }
LEGENDS_API legends_error_t legends_set_machine_pc98(legends_handle, int) { return LEGENDS_ERR_NOT_SUPPORTED; }
LEGENDS_API legends_error_t legends_is_pc98_mode(legends_handle, int*) { return LEGENDS_ERR_NOT_SUPPORTED; }
LEGENDS_API legends_error_t legends_has_capability(legends_handle, const char*, int*) { return LEGENDS_ERR_NOT_SUPPORTED; }
LEGENDS_API legends_error_t legends_register_event_callback(legends_handle, int, legends_event_callback_t, void*) { return LEGENDS_ERR_NOT_SUPPORTED; }

} // extern "C"
