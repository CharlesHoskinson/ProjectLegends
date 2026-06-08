// SPDX-License-Identifier: GPL-2.0-or-later

#include <legends/runtime_host.h>

#include <string>



namespace legends {

namespace {

std::string to_c_string(std::string_view value) {
    return std::string(value);
}

} // namespace



// ── InProcessEngineRuntime ──────────────────────────────────────────────────



InProcessEngineRuntime::InProcessEngineRuntime(legends_handle handle, bool own_handle)

    : handle_(handle), own_handle_(own_handle) {}



InProcessEngineRuntime::~InProcessEngineRuntime() {

    if (handle_ && own_handle_) {

        legends_destroy(handle_);

    }

}



legends_error_t InProcessEngineRuntime::step_ms(uint32_t ms, legends_step_result_t* result_out) {

    return legends_step_ms(handle_, ms, result_out);

}



legends_error_t InProcessEngineRuntime::step_cycles(uint64_t cycles, legends_step_result_t* result_out) {

    return legends_step_cycles(handle_, cycles, result_out);

}



legends_error_t InProcessEngineRuntime::capture_text(

    legends_text_cell_t* cells,

    size_t cells_count,

    size_t* cells_count_out,

    legends_text_info_t* info_out)

{

    return legends_capture_text(handle_, cells, cells_count, cells_count_out, info_out);

}



legends_error_t InProcessEngineRuntime::capture_rgb(

    uint8_t* buffer,

    size_t buffer_size,

    size_t* size_out,

    uint16_t* width_out,

    uint16_t* height_out)

{

    return legends_capture_rgb(handle_, buffer, buffer_size, size_out, width_out, height_out);

}



legends_error_t InProcessEngineRuntime::inject_key(uint8_t scancode, bool is_down) {

    return legends_key_event(handle_, scancode, is_down ? 1 : 0);

}



legends_error_t InProcessEngineRuntime::inject_mouse(int16_t dx, int16_t dy, uint8_t buttons) {

    return legends_mouse_event(handle_, dx, dy, buttons);

}



legends_error_t InProcessEngineRuntime::save_state(void* buffer, size_t buffer_size, size_t* size_out) {

    return legends_save_state(handle_, buffer, buffer_size, size_out);

}



legends_error_t InProcessEngineRuntime::load_state(const void* buffer, size_t buffer_size) {

    return legends_load_state(handle_, buffer, buffer_size);

}



legends_error_t InProcessEngineRuntime::mount_drive(char drive_letter, std::string_view host_path, uint32_t flags) {

    std::string path_str(host_path);

    return legends_mount_drive(handle_, drive_letter, path_str.c_str(), flags);

}



legends_error_t InProcessEngineRuntime::unmount_drive(char drive_letter) {

    return legends_unmount_drive(handle_, drive_letter);

}



legends_error_t InProcessEngineRuntime::get_total_cycles(uint64_t* cycles_out) {

    return legends_get_total_cycles(handle_, cycles_out);

}



legends_error_t InProcessEngineRuntime::is_frame_dirty(int* dirty_out) {

    return legends_is_frame_dirty(handle_, dirty_out);

}



legends_error_t InProcessEngineRuntime::inject_key_ext(uint8_t scancode, bool is_down) {

    return legends_key_event_ext(handle_, scancode, is_down ? 1 : 0);

}



legends_error_t InProcessEngineRuntime::capture_audio(int16_t* buffer, size_t buffer_count, size_t* count_out) {

    return legends_capture_audio(handle_, buffer, buffer_count, count_out);

}



legends_error_t InProcessEngineRuntime::capture_midi_audio(int16_t* buffer, size_t buffer_count, size_t* count_out) {

    return legends_capture_midi_audio(handle_, buffer, buffer_count, count_out);

}



legends_error_t InProcessEngineRuntime::reset() {

    return legends_reset(handle_);

}



legends_error_t InProcessEngineRuntime::text_input(std::string_view text) {

    std::string text_str = to_c_string(text);
    return legends_text_input(handle_, text_str.c_str());

}



legends_error_t InProcessEngineRuntime::get_cursor(uint8_t* x_out, uint8_t* y_out, int* visible_out) {

    return legends_get_cursor(handle_, x_out, y_out, visible_out);

}



legends_error_t InProcessEngineRuntime::joystick_event(uint8_t joystick_id, uint8_t axis_x, uint8_t axis_y, uint8_t buttons) {

    return legends_joystick_event(handle_, joystick_id, axis_x, axis_y, buttons);

}



legends_error_t InProcessEngineRuntime::set_log_callback(legends_log_callback_t callback, void* userdata) {

    return legends_set_log_callback(handle_, callback, userdata);

}



legends_error_t InProcessEngineRuntime::set_midi_device(std::string_view device) {

    std::string device_str = to_c_string(device);
    return legends_midi_set_device(handle_, device_str.c_str());

}



legends_error_t InProcessEngineRuntime::set_midi_soundfont(std::string_view sf2_path) {

    std::string sf2_path_str = to_c_string(sf2_path);
    return legends_midi_set_soundfont(handle_, sf2_path_str.c_str());

}



legends_error_t InProcessEngineRuntime::set_midi_romdir(std::string_view rom_dir) {

    std::string rom_dir_str = to_c_string(rom_dir);
    return legends_midi_set_romdir(handle_, rom_dir_str.c_str());

}



legends_error_t InProcessEngineRuntime::set_printer_output(std::string_view output_path) {

    std::string output_path_str = to_c_string(output_path);
    return legends_printer_set_output(handle_, output_path_str.c_str());

}



legends_error_t InProcessEngineRuntime::set_ttf_font(std::string_view ttf_path, uint32_t point_size) {

    std::string ttf_path_str = to_c_string(ttf_path);
    return legends_set_ttf_font(handle_, ttf_path_str.c_str(), point_size);

}



legends_error_t InProcessEngineRuntime::ipx_enable(bool enable) {

    return legends_ipx_enable(handle_, enable ? 1 : 0);

}



legends_error_t InProcessEngineRuntime::ipx_connect(std::string_view server, uint16_t port) {

    std::string server_str = to_c_string(server);
    return legends_ipx_connect(handle_, server_str.c_str(), port);

}



legends_error_t InProcessEngineRuntime::ipx_disconnect() {

    return legends_ipx_disconnect(handle_);

}



legends_error_t InProcessEngineRuntime::glide_enable(bool enable) {

    return legends_glide_enable(handle_, enable ? 1 : 0);

}



legends_error_t InProcessEngineRuntime::glide_set_resolution(uint16_t width, uint16_t height) {

    return legends_glide_set_resolution(handle_, width, height);

}



legends_error_t InProcessEngineRuntime::set_machine_pc98(bool enable) {

    return legends_set_machine_pc98(handle_, enable ? 1 : 0);

}





// ── IpcEngineRuntime ────────────────────────────────────────────────────────



IpcEngineRuntime::IpcEngineRuntime(legends_handle handle, bool own_handle)

    : handle_(handle), own_handle_(own_handle) {}



IpcEngineRuntime::~IpcEngineRuntime() {

    if (handle_ && own_handle_) {

        legends_destroy(handle_);

    }

}



legends_error_t IpcEngineRuntime::step_ms(uint32_t ms, legends_step_result_t* result_out) {

    return legends_step_ms(handle_, ms, result_out);

}



legends_error_t IpcEngineRuntime::step_cycles(uint64_t cycles, legends_step_result_t* result_out) {

    return legends_step_cycles(handle_, cycles, result_out);

}



legends_error_t IpcEngineRuntime::capture_text(

    legends_text_cell_t* cells,

    size_t cells_count,

    size_t* cells_count_out,

    legends_text_info_t* info_out)

{

    return legends_capture_text(handle_, cells, cells_count, cells_count_out, info_out);

}



legends_error_t IpcEngineRuntime::capture_rgb(

    uint8_t* buffer,

    size_t buffer_size,

    size_t* size_out,

    uint16_t* width_out,

    uint16_t* height_out)

{

    return legends_capture_rgb(handle_, buffer, buffer_size, size_out, width_out, height_out);

}



legends_error_t IpcEngineRuntime::inject_key(uint8_t scancode, bool is_down) {

    return legends_key_event(handle_, scancode, is_down ? 1 : 0);

}



legends_error_t IpcEngineRuntime::inject_mouse(int16_t dx, int16_t dy, uint8_t buttons) {

    return legends_mouse_event(handle_, dx, dy, buttons);

}



legends_error_t IpcEngineRuntime::save_state(void* buffer, size_t buffer_size, size_t* size_out) {

    return legends_save_state(handle_, buffer, buffer_size, size_out);

}



legends_error_t IpcEngineRuntime::load_state(const void* buffer, size_t buffer_size) {

    return legends_load_state(handle_, buffer, buffer_size);

}



legends_error_t IpcEngineRuntime::mount_drive(char drive_letter, std::string_view host_path, uint32_t flags) {

    std::string path_str(host_path);

    return legends_mount_drive(handle_, drive_letter, path_str.c_str(), flags);

}



legends_error_t IpcEngineRuntime::unmount_drive(char drive_letter) {

    return legends_unmount_drive(handle_, drive_letter);

}



legends_error_t IpcEngineRuntime::get_total_cycles(uint64_t* cycles_out) {

    return legends_get_total_cycles(handle_, cycles_out);

}



legends_error_t IpcEngineRuntime::is_frame_dirty(int* dirty_out) {

    return legends_is_frame_dirty(handle_, dirty_out);

}



legends_error_t IpcEngineRuntime::inject_key_ext(uint8_t scancode, bool is_down) {

    return legends_key_event_ext(handle_, scancode, is_down ? 1 : 0);

}



legends_error_t IpcEngineRuntime::capture_audio(int16_t* buffer, size_t buffer_count, size_t* count_out) {

    return legends_capture_audio(handle_, buffer, buffer_count, count_out);

}



legends_error_t IpcEngineRuntime::capture_midi_audio(int16_t* buffer, size_t buffer_count, size_t* count_out) {

    return legends_capture_midi_audio(handle_, buffer, buffer_count, count_out);

}



legends_error_t IpcEngineRuntime::reset() {

    return legends_reset(handle_);

}



legends_error_t IpcEngineRuntime::text_input(std::string_view text) {

    std::string text_str = to_c_string(text);
    return legends_text_input(handle_, text_str.c_str());

}



legends_error_t IpcEngineRuntime::get_cursor(uint8_t* x_out, uint8_t* y_out, int* visible_out) {

    return legends_get_cursor(handle_, x_out, y_out, visible_out);

}



legends_error_t IpcEngineRuntime::joystick_event(uint8_t joystick_id, uint8_t axis_x, uint8_t axis_y, uint8_t buttons) {

    return legends_joystick_event(handle_, joystick_id, axis_x, axis_y, buttons);

}



legends_error_t IpcEngineRuntime::set_log_callback(legends_log_callback_t callback, void* userdata) {

    return legends_set_log_callback(handle_, callback, userdata);

}



legends_error_t IpcEngineRuntime::set_midi_device(std::string_view device) {

    std::string device_str = to_c_string(device);
    return legends_midi_set_device(handle_, device_str.c_str());

}



legends_error_t IpcEngineRuntime::set_midi_soundfont(std::string_view sf2_path) {

    std::string sf2_path_str = to_c_string(sf2_path);
    return legends_midi_set_soundfont(handle_, sf2_path_str.c_str());

}



legends_error_t IpcEngineRuntime::set_midi_romdir(std::string_view rom_dir) {

    std::string rom_dir_str = to_c_string(rom_dir);
    return legends_midi_set_romdir(handle_, rom_dir_str.c_str());

}



legends_error_t IpcEngineRuntime::set_printer_output(std::string_view output_path) {

    std::string output_path_str = to_c_string(output_path);
    return legends_printer_set_output(handle_, output_path_str.c_str());

}



legends_error_t IpcEngineRuntime::set_ttf_font(std::string_view ttf_path, uint32_t point_size) {

    std::string ttf_path_str = to_c_string(ttf_path);
    return legends_set_ttf_font(handle_, ttf_path_str.c_str(), point_size);

}



legends_error_t IpcEngineRuntime::ipx_enable(bool enable) {

    return legends_ipx_enable(handle_, enable ? 1 : 0);

}



legends_error_t IpcEngineRuntime::ipx_connect(std::string_view server, uint16_t port) {

    std::string server_str = to_c_string(server);
    return legends_ipx_connect(handle_, server_str.c_str(), port);

}



legends_error_t IpcEngineRuntime::ipx_disconnect() {

    return legends_ipx_disconnect(handle_);

}



legends_error_t IpcEngineRuntime::glide_enable(bool enable) {

    return legends_glide_enable(handle_, enable ? 1 : 0);

}



legends_error_t IpcEngineRuntime::glide_set_resolution(uint16_t width, uint16_t height) {

    return legends_glide_set_resolution(handle_, width, height);

}



legends_error_t IpcEngineRuntime::set_machine_pc98(bool enable) {

    return legends_set_machine_pc98(handle_, enable ? 1 : 0);

}



// ── Dynamic Factory ─────────────────────────────────────────────────────────



std::unique_ptr<RuntimeHost> create_runtime(const legends_config_t* config) {

    legends_handle handle = nullptr;

    auto err = legends_create(config, &handle);

    if (err != LEGENDS_OK) {

        return nullptr;

    }

#if LEGENDS_USE_IPC

    return std::make_unique<IpcEngineRuntime>(handle);

#else

    return std::make_unique<InProcessEngineRuntime>(handle);

#endif

}



} // namespace legends
