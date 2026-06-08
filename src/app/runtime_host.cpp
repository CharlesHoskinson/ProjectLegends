// SPDX-License-Identifier: GPL-2.0-or-later
#include <legends/runtime_host.h>
#include <string>

namespace legends {

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
