// SPDX-License-Identifier: MIT
//
// Proxy implementation of legends_embed.h that forwards all calls
// over IPC to the engine host process.

#include <legends/legends_embed.h>
#include "proxy_connection.h"
#include "ipc_error_mapping.h"
#include <legends_ipc/messages.h>
#include <algorithm>
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

LEGENDS_API legends_error_t legends_get_config(legends_handle handle, legends_config_t* config) {
    if (!handle) return LEGENDS_ERR_NULL_HANDLE;
    if (!config) return LEGENDS_ERR_NULL_POINTER;
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    auto resp = conn().request<GetConfigResp>(MsgType::GetConfigReq, {});
    if (!resp) return map_ipc_error(resp.error());
    if (resp->error_code == LEGENDS_OK) {
        legends_config_t normalized = LEGENDS_CONFIG_INIT;
        *config = normalized;
        config->struct_size = resp->struct_size;
        config->api_version = resp->api_version;
        config->memory_kb = resp->memory_kb;
        config->xms_kb = resp->xms_kb;
        config->ems_kb = resp->ems_kb;
        config->cpu_cycles = resp->cpu_cycles;
        config->cpu_type = resp->cpu_type;
        config->machine_type = resp->machine_type;
        config->deterministic = resp->deterministic;
    }
    return resp->error_code;
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
    legends_handle handle, legends_text_cell_t* cells, size_t cells_count,
    size_t* cells_count_out, legends_text_info_t* info_out)
{
    if (!handle) return LEGENDS_ERR_NULL_HANDLE;
    if (!cells_count_out) return LEGENDS_ERR_NULL_POINTER;
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;

    CaptureTextReq req;
    if (!cells) {
        req.cells_count = 0;
    } else {
        req.cells_count = static_cast<uint32_t>(cells_count);
    }

    std::vector<uint8_t> buf(CaptureTextReq::serialized_size);
    req.serialize(buf);

    auto resp = conn().request<CaptureTextResp>(MsgType::CaptureTextReq, buf);
    if (!resp) return map_ipc_error(resp.error());

    if (cells_count_out) {
        *cells_count_out = resp->required_count;
    }
    if (info_out) {
        info_out->columns = resp->columns;
        info_out->rows = resp->rows;
        info_out->active_page = resp->active_page;
        info_out->cursor_x = resp->cursor_x;
        info_out->cursor_y = resp->cursor_y;
        info_out->cursor_visible = resp->cursor_visible;
        info_out->cursor_start = resp->cursor_start;
        info_out->cursor_end = resp->cursor_end;
    }

    if (cells && resp->error_code == LEGENDS_OK) {
        size_t to_copy = std::min(static_cast<size_t>(resp->cells.size()), cells_count);
        if (to_copy > 0) {
            std::memcpy(cells, resp->cells.data(), to_copy * sizeof(legends_text_cell_t));
        }
    }

    return resp->error_code;
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

LEGENDS_API legends_error_t legends_key_event_ext(legends_handle handle, uint8_t scancode, int is_down) {
    if (!handle) return LEGENDS_ERR_NULL_HANDLE;
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    KeyEventExtReq req;
    req.scancode = scancode;
    req.is_down = static_cast<uint8_t>(is_down);
    std::vector<uint8_t> buf(KeyEventExtReq::serialized_size);
    req.serialize(buf);
    auto resp = conn().request<KeyEventExtResp>(MsgType::KeyEventExtReq, buf);
    if (!resp) return map_ipc_error(resp.error());
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_text_input(legends_handle handle, const char* utf8_text) {
    if (!handle) return LEGENDS_ERR_NULL_HANDLE;
    if (!utf8_text) return LEGENDS_ERR_NULL_POINTER;
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    TextInputReq req;
    req.text = utf8_text;
    std::vector<uint8_t> buf(req.serialized_size_dynamic());
    req.serialize(buf);
    auto resp = conn().request<TextInputResp>(MsgType::TextInputReq, buf);
    if (!resp) return map_ipc_error(resp.error());
    return resp->error_code;
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

LEGENDS_API legends_error_t legends_save_state(
    legends_handle handle, void* buffer, size_t buffer_size, size_t* size_out)
{
    if (!handle) return LEGENDS_ERR_NULL_HANDLE;
    if (!size_out) return LEGENDS_ERR_NULL_POINTER;
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;

    auto resp = conn().request<SaveStateResp>(MsgType::SaveStateReq, {});
    if (!resp) return map_ipc_error(resp.error());

    *size_out = resp->data_size;

    if (resp->error_code == LEGENDS_OK) {
        if (!buffer) {
            return LEGENDS_OK;
        }
        if (buffer_size < resp->data_size) {
            return LEGENDS_ERR_BUFFER_TOO_SMALL;
        }
        if (resp->state_bytes.size() < resp->data_size) {
            return LEGENDS_ERR_INTERNAL;
        }
        std::memcpy(buffer, resp->state_bytes.data(), resp->data_size);
    }
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_load_state(legends_handle handle, const void* buffer, size_t buffer_size) {
    if (!handle) return LEGENDS_ERR_NULL_HANDLE;
    if (!buffer) return LEGENDS_ERR_NULL_POINTER;
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;

    LoadStateReq req;
    req.data_size = static_cast<uint32_t>(buffer_size);
    req.state_bytes.assign(reinterpret_cast<const uint8_t*>(buffer), reinterpret_cast<const uint8_t*>(buffer) + buffer_size);

    std::vector<uint8_t> buf(req.serialized_size_dynamic());
    req.serialize(buf);

    auto resp = conn().request<LoadStateResp>(MsgType::LoadStateReq, buf);
    if (!resp) return map_ipc_error(resp.error());
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_get_state_hash(legends_handle, uint8_t hash_out[32]) {
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    auto resp = conn().request<GetStateHashResp>(MsgType::GetStateHashReq, {});
    if (!resp) return map_ipc_error(resp.error());
    if (hash_out) std::memcpy(hash_out, resp->hash, 32);
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_verify_determinism(
    legends_handle handle, uint64_t test_cycles, int* is_deterministic_out)
{
    if (!handle) return LEGENDS_ERR_NULL_HANDLE;
    if (!is_deterministic_out) return LEGENDS_ERR_NULL_POINTER;
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    VerifyDeterminismReq req;
    req.test_cycles = test_cycles;
    std::vector<uint8_t> buf(VerifyDeterminismReq::serialized_size);
    req.serialize(buf);
    auto resp = conn().request<VerifyDeterminismResp>(MsgType::VerifyDeterminismReq, buf);
    if (!resp) return map_ipc_error(resp.error());
    *is_deterministic_out = resp->is_deterministic;
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_get_last_error(
    legends_handle, char* buffer, size_t buffer_size, size_t* length_out)
{
    if (!length_out) return LEGENDS_ERR_NULL_POINTER;
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;

    auto resp = conn().request<GetLastErrorResp>(MsgType::GetLastErrorReq, {});
    if (!resp) return map_ipc_error(resp.error());

    *length_out = resp->required_len;

    if (resp->error_code == LEGENDS_OK) {
        if (!buffer) {
            return LEGENDS_OK;
        }
        if (buffer_size < resp->required_len) {
            return LEGENDS_ERR_BUFFER_TOO_SMALL;
        }
        if (!resp->error_msg.empty()) {
            std::memcpy(buffer, resp->error_msg.c_str(), resp->error_msg.size());
            buffer[resp->error_msg.size()] = '\0';
        } else if (buffer_size > 0) {
            buffer[0] = '\0';
        }
    }
    return resp->error_code;
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
LEGENDS_API legends_error_t legends_joystick_event(
    legends_handle handle, uint8_t joystick_id, uint8_t axis_x, uint8_t axis_y, uint8_t buttons)
{
    if (!handle) return LEGENDS_ERR_NULL_HANDLE;
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    JoystickEventReq req;
    req.joystick_id = joystick_id;
    req.axis_x = axis_x;
    req.axis_y = axis_y;
    req.buttons = buttons;
    std::vector<uint8_t> buf(JoystickEventReq::serialized_size);
    req.serialize(buf);
    auto resp = conn().request<JoystickEventResp>(MsgType::JoystickEventReq, buf);
    if (!resp) return map_ipc_error(resp.error());
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_midi_set_device(legends_handle handle, const char* device_type) {
    if (!handle) return LEGENDS_ERR_NULL_HANDLE;
    if (!device_type) return LEGENDS_ERR_NULL_POINTER;
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    MidiSetDeviceReq req;
    req.device = device_type;
    std::vector<uint8_t> buf(req.serialized_size_dynamic());
    req.serialize(buf);
    auto resp = conn().request<MidiSetDeviceResp>(MsgType::MidiSetDeviceReq, buf);
    if (!resp) return map_ipc_error(resp.error());
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_midi_set_soundfont(legends_handle handle, const char* sf2_path) {
    if (!handle) return LEGENDS_ERR_NULL_HANDLE;
    if (!sf2_path) return LEGENDS_ERR_NULL_POINTER;
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    MidiSetSoundfontReq req;
    req.soundfont = sf2_path;
    std::vector<uint8_t> buf(req.serialized_size_dynamic());
    req.serialize(buf);
    auto resp = conn().request<MidiSetSoundfontResp>(MsgType::MidiSetSoundfontReq, buf);
    if (!resp) return map_ipc_error(resp.error());
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_midi_set_romdir(legends_handle handle, const char* rom_dir) {
    if (!handle) return LEGENDS_ERR_NULL_HANDLE;
    if (!rom_dir) return LEGENDS_ERR_NULL_POINTER;
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    MidiSetRomdirReq req;
    req.romdir = rom_dir;
    std::vector<uint8_t> buf(req.serialized_size_dynamic());
    req.serialize(buf);
    auto resp = conn().request<MidiSetRomdirResp>(MsgType::MidiSetRomdirReq, buf);
    if (!resp) return map_ipc_error(resp.error());
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_capture_midi_audio(
    legends_handle handle, int16_t* buf, size_t count, size_t* out)
{
    if (!handle) return LEGENDS_ERR_NULL_HANDLE;
    if (!out) return LEGENDS_ERR_NULL_POINTER;
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;

    CaptureMidiAudioReq req;
    if (!buf) {
        req.buffer_count = 0;
    } else {
        req.buffer_count = static_cast<uint32_t>(count);
    }

    std::vector<uint8_t> buf_bytes(CaptureMidiAudioReq::serialized_size);
    req.serialize(buf_bytes);

    auto resp = conn().request<CaptureMidiAudioResp>(MsgType::CaptureMidiAudioReq, buf_bytes);
    if (!resp) return map_ipc_error(resp.error());

    *out = resp->required_count;

    if (buf && resp->error_code == LEGENDS_OK) {
        size_t to_copy = std::min(static_cast<size_t>(resp->audio_data.size()), count);
        if (to_copy > 0) {
            std::memcpy(buf, resp->audio_data.data(), to_copy * sizeof(int16_t));
        }
    }

    return resp->error_code;
}

LEGENDS_API legends_error_t legends_printer_set_output(legends_handle handle, const char* output_path) {
    if (!handle) return LEGENDS_ERR_NULL_HANDLE;
    if (!output_path) return LEGENDS_ERR_NULL_POINTER;
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    PrinterSetOutputReq req;
    req.output_path = output_path;
    std::vector<uint8_t> buf(req.serialized_size_dynamic());
    req.serialize(buf);
    auto resp = conn().request<PrinterSetOutputResp>(MsgType::PrinterSetOutputReq, buf);
    if (!resp) return map_ipc_error(resp.error());
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_printer_is_active(legends_handle handle, int* active_out) {
    if (!handle) return LEGENDS_ERR_NULL_HANDLE;
    if (!active_out) return LEGENDS_ERR_NULL_POINTER;
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    auto resp = conn().request<PrinterIsActiveResp>(MsgType::PrinterIsActiveReq, {});
    if (!resp) return map_ipc_error(resp.error());
    *active_out = resp->is_active;
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_printer_flush(legends_handle handle) {
    if (!handle) return LEGENDS_ERR_NULL_HANDLE;
    PROXY_EMPTY_REQUEST(PrinterFlushReq, PrinterFlushResp);
}

LEGENDS_API legends_error_t legends_set_ttf_font(legends_handle, const char*, uint32_t) { return LEGENDS_ERR_NOT_SUPPORTED; }

LEGENDS_API legends_error_t legends_ipx_enable(legends_handle handle, int enable) {
    if (!handle) return LEGENDS_ERR_NULL_HANDLE;
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    IpxEnableReq req;
    req.enable = enable;
    std::vector<uint8_t> buf(IpxEnableReq::serialized_size);
    req.serialize(buf);
    auto resp = conn().request<IpxEnableResp>(MsgType::IpxEnableReq, buf);
    if (!resp) return map_ipc_error(resp.error());
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_ipx_connect(legends_handle handle, const char* server, uint16_t port) {
    if (!handle) return LEGENDS_ERR_NULL_HANDLE;
    if (!server) return LEGENDS_ERR_NULL_POINTER;
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    IpxConnectReq req;
    req.server = server;
    req.port = port;
    std::vector<uint8_t> buf(req.serialized_size_dynamic());
    req.serialize(buf);
    auto resp = conn().request<IpxConnectResp>(MsgType::IpxConnectReq, buf);
    if (!resp) return map_ipc_error(resp.error());
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_ipx_disconnect(legends_handle handle) {
    if (!handle) return LEGENDS_ERR_NULL_HANDLE;
    PROXY_EMPTY_REQUEST(IpxDisconnectReq, IpxDisconnectResp);
}

LEGENDS_API legends_error_t legends_ipx_is_connected(legends_handle handle, int* out) {
    if (!handle) return LEGENDS_ERR_NULL_HANDLE;
    if (!out) return LEGENDS_ERR_NULL_POINTER;
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    auto resp = conn().request<IpxIsConnectedResp>(MsgType::IpxIsConnectedReq, {});
    if (!resp) return map_ipc_error(resp.error());
    *out = resp->is_connected;
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_glide_enable(legends_handle handle, int enable) {
    if (!handle) return LEGENDS_ERR_NULL_HANDLE;
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    GlideEnableReq req;
    req.enable = enable;
    std::vector<uint8_t> buf(GlideEnableReq::serialized_size);
    req.serialize(buf);
    auto resp = conn().request<GlideEnableResp>(MsgType::GlideEnableReq, buf);
    if (!resp) return map_ipc_error(resp.error());
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_glide_set_resolution(legends_handle handle, uint16_t w, uint16_t h) {
    if (!handle) return LEGENDS_ERR_NULL_HANDLE;
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    GlideSetResolutionReq req;
    req.width = w;
    req.height = h;
    std::vector<uint8_t> buf(GlideSetResolutionReq::serialized_size);
    req.serialize(buf);
    auto resp = conn().request<GlideSetResolutionResp>(MsgType::GlideSetResolutionReq, buf);
    if (!resp) return map_ipc_error(resp.error());
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_set_machine_pc98(legends_handle handle, int enable) {
    if (!handle) return LEGENDS_ERR_NULL_HANDLE;
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    SetMachinePc98Req req;
    req.enable = enable;
    std::vector<uint8_t> buf(SetMachinePc98Req::serialized_size);
    req.serialize(buf);
    auto resp = conn().request<SetMachinePc98Resp>(MsgType::SetMachinePc98Req, buf);
    if (!resp) return map_ipc_error(resp.error());
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_is_pc98_mode(legends_handle handle, int* out) {
    if (!handle) return LEGENDS_ERR_NULL_HANDLE;
    if (!out) return LEGENDS_ERR_NULL_POINTER;
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    auto resp = conn().request<IsPc98ModeResp>(MsgType::IsPc98ModeReq, {});
    if (!resp) return map_ipc_error(resp.error());
    *out = resp->is_pc98;
    return resp->error_code;
}

LEGENDS_API legends_error_t legends_has_capability(legends_handle handle, const char* capability_name, int* out) {
    if (!handle) return LEGENDS_ERR_NULL_HANDLE;
    if (!capability_name) return LEGENDS_ERR_NULL_POINTER;
    if (!out) return LEGENDS_ERR_NULL_POINTER;
    if (!conn().is_connected()) return LEGENDS_ERR_NOT_INITIALIZED;
    HasCapabilityReq req;
    req.name = capability_name;
    std::vector<uint8_t> buf(req.serialized_size_dynamic());
    req.serialize(buf);
    auto resp = conn().request<HasCapabilityResp>(MsgType::HasCapabilityReq, buf);
    if (!resp) return map_ipc_error(resp.error());
    *out = resp->has_cap;
    return resp->error_code;
}
LEGENDS_API legends_error_t legends_register_event_callback(legends_handle, int, legends_event_callback_t, void*) { return LEGENDS_ERR_NOT_SUPPORTED; }

} // extern "C"
