// SPDX-License-Identifier: GPL-2.0-or-later

#ifndef LEGENDS_RUNTIME_HOST_H

#define LEGENDS_RUNTIME_HOST_H



#include <legends/legends_embed.h>

#include <vector>

#include <string_view>

#include <span>

#include <memory>



namespace legends {



struct FrameData {

    std::vector<uint8_t> pixels;

    uint16_t width = 0;

    uint16_t height = 0;

};



class RuntimeHost {

public:

    virtual ~RuntimeHost() = default;



    virtual legends_error_t step_ms(uint32_t ms, legends_step_result_t* result_out) = 0;

    virtual legends_error_t step_cycles(uint64_t cycles, legends_step_result_t* result_out) = 0;



    virtual legends_error_t capture_text(

        legends_text_cell_t* cells,

        size_t cells_count,

        size_t* cells_count_out,

        legends_text_info_t* info_out) = 0;



    virtual legends_error_t capture_rgb(

        uint8_t* buffer,

        size_t buffer_size,

        size_t* size_out,

        uint16_t* width_out,

        uint16_t* height_out) = 0;



    virtual legends_error_t inject_key(uint8_t scancode, bool is_down) = 0;

    virtual legends_error_t inject_mouse(int16_t dx, int16_t dy, uint8_t buttons) = 0;



    virtual legends_error_t save_state(void* buffer, size_t buffer_size, size_t* size_out) = 0;

    virtual legends_error_t load_state(const void* buffer, size_t buffer_size) = 0;



    virtual legends_error_t mount_drive(char drive_letter, std::string_view host_path, uint32_t flags) = 0;

    virtual legends_error_t unmount_drive(char drive_letter) = 0;



    virtual legends_error_t get_total_cycles(uint64_t* cycles_out) = 0;

    virtual legends_error_t is_frame_dirty(int* dirty_out) = 0;

    virtual legends_error_t inject_key_ext(uint8_t scancode, bool is_down) = 0;

    virtual legends_error_t capture_audio(int16_t* buffer, size_t buffer_count, size_t* count_out) = 0;

    virtual legends_error_t capture_midi_audio(int16_t* buffer, size_t buffer_count, size_t* count_out) = 0;



    virtual legends_error_t reset() = 0;

    virtual legends_error_t text_input(std::string_view text) = 0;

    virtual legends_error_t get_cursor(uint8_t* x_out, uint8_t* y_out, int* visible_out) = 0;

    virtual legends_error_t joystick_event(uint8_t joystick_id, uint8_t axis_x, uint8_t axis_y, uint8_t buttons) = 0;

    virtual legends_error_t set_log_callback(legends_log_callback_t callback, void* userdata) = 0;

    virtual legends_error_t set_midi_device(std::string_view device) = 0;

    virtual legends_error_t set_midi_soundfont(std::string_view sf2_path) = 0;

    virtual legends_error_t set_midi_romdir(std::string_view rom_dir) = 0;

    virtual legends_error_t set_printer_output(std::string_view output_path) = 0;

    virtual legends_error_t set_ttf_font(std::string_view ttf_path, uint32_t point_size) = 0;

    virtual legends_error_t ipx_enable(bool enable) = 0;

    virtual legends_error_t ipx_connect(std::string_view server, uint16_t port) = 0;

    virtual legends_error_t ipx_disconnect() = 0;

    virtual legends_error_t glide_enable(bool enable) = 0;

    virtual legends_error_t glide_set_resolution(uint16_t width, uint16_t height) = 0;

    virtual legends_error_t set_machine_pc98(bool enable) = 0;

};



// Subclass: InProcessEngineRuntime

class InProcessEngineRuntime : public RuntimeHost {

public:

    explicit InProcessEngineRuntime(legends_handle handle, bool own_handle = true);

    ~InProcessEngineRuntime() override;



    legends_error_t step_ms(uint32_t ms, legends_step_result_t* result_out) override;

    legends_error_t step_cycles(uint64_t cycles, legends_step_result_t* result_out) override;



    legends_error_t capture_text(

        legends_text_cell_t* cells,

        size_t cells_count,

        size_t* cells_count_out,

        legends_text_info_t* info_out) override;



    legends_error_t capture_rgb(

        uint8_t* buffer,

        size_t buffer_size,

        size_t* size_out,

        uint16_t* width_out,

        uint16_t* height_out) override;



    legends_error_t inject_key(uint8_t scancode, bool is_down) override;

    legends_error_t inject_mouse(int16_t dx, int16_t dy, uint8_t buttons) override;



    legends_error_t save_state(void* buffer, size_t buffer_size, size_t* size_out) override;

    legends_error_t load_state(const void* buffer, size_t buffer_size) override;



    legends_error_t mount_drive(char drive_letter, std::string_view host_path, uint32_t flags) override;

    legends_error_t unmount_drive(char drive_letter) override;



    legends_error_t get_total_cycles(uint64_t* cycles_out) override;

    legends_error_t is_frame_dirty(int* dirty_out) override;

    legends_error_t inject_key_ext(uint8_t scancode, bool is_down) override;

    legends_error_t capture_audio(int16_t* buffer, size_t buffer_count, size_t* count_out) override;

    legends_error_t capture_midi_audio(int16_t* buffer, size_t buffer_count, size_t* count_out) override;



    legends_error_t reset() override;

    legends_error_t text_input(std::string_view text) override;

    legends_error_t get_cursor(uint8_t* x_out, uint8_t* y_out, int* visible_out) override;

    legends_error_t joystick_event(uint8_t joystick_id, uint8_t axis_x, uint8_t axis_y, uint8_t buttons) override;

    legends_error_t set_log_callback(legends_log_callback_t callback, void* userdata) override;

    legends_error_t set_midi_device(std::string_view device) override;

    legends_error_t set_midi_soundfont(std::string_view sf2_path) override;

    legends_error_t set_midi_romdir(std::string_view rom_dir) override;

    legends_error_t set_printer_output(std::string_view output_path) override;

    legends_error_t set_ttf_font(std::string_view ttf_path, uint32_t point_size) override;

    legends_error_t ipx_enable(bool enable) override;

    legends_error_t ipx_connect(std::string_view server, uint16_t port) override;

    legends_error_t ipx_disconnect() override;

    legends_error_t glide_enable(bool enable) override;

    legends_error_t glide_set_resolution(uint16_t width, uint16_t height) override;

    legends_error_t set_machine_pc98(bool enable) override;



private:

    legends_handle handle_;

    bool own_handle_;

};



// Subclass: IpcEngineRuntime

class IpcEngineRuntime : public RuntimeHost {

public:

    explicit IpcEngineRuntime(legends_handle handle, bool own_handle = true);

    ~IpcEngineRuntime() override;



    legends_error_t step_ms(uint32_t ms, legends_step_result_t* result_out) override;

    legends_error_t step_cycles(uint64_t cycles, legends_step_result_t* result_out) override;



    legends_error_t capture_text(

        legends_text_cell_t* cells,

        size_t cells_count,

        size_t* cells_count_out,

        legends_text_info_t* info_out) override;



    legends_error_t capture_rgb(

        uint8_t* buffer,

        size_t buffer_size,

        size_t* size_out,

        uint16_t* width_out,

        uint16_t* height_out) override;



    legends_error_t inject_key(uint8_t scancode, bool is_down) override;

    legends_error_t inject_mouse(int16_t dx, int16_t dy, uint8_t buttons) override;



    legends_error_t save_state(void* buffer, size_t buffer_size, size_t* size_out) override;

    legends_error_t load_state(const void* buffer, size_t buffer_size) override;



    legends_error_t mount_drive(char drive_letter, std::string_view host_path, uint32_t flags) override;

    legends_error_t unmount_drive(char drive_letter) override;



    legends_error_t get_total_cycles(uint64_t* cycles_out) override;

    legends_error_t is_frame_dirty(int* dirty_out) override;

    legends_error_t inject_key_ext(uint8_t scancode, bool is_down) override;

    legends_error_t capture_audio(int16_t* buffer, size_t buffer_count, size_t* count_out) override;

    legends_error_t capture_midi_audio(int16_t* buffer, size_t buffer_count, size_t* count_out) override;



    legends_error_t reset() override;

    legends_error_t text_input(std::string_view text) override;

    legends_error_t get_cursor(uint8_t* x_out, uint8_t* y_out, int* visible_out) override;

    legends_error_t joystick_event(uint8_t joystick_id, uint8_t axis_x, uint8_t axis_y, uint8_t buttons) override;

    legends_error_t set_log_callback(legends_log_callback_t callback, void* userdata) override;

    legends_error_t set_midi_device(std::string_view device) override;

    legends_error_t set_midi_soundfont(std::string_view sf2_path) override;

    legends_error_t set_midi_romdir(std::string_view rom_dir) override;

    legends_error_t set_printer_output(std::string_view output_path) override;

    legends_error_t set_ttf_font(std::string_view ttf_path, uint32_t point_size) override;

    legends_error_t ipx_enable(bool enable) override;

    legends_error_t ipx_connect(std::string_view server, uint16_t port) override;

    legends_error_t ipx_disconnect() override;

    legends_error_t glide_enable(bool enable) override;

    legends_error_t glide_set_resolution(uint16_t width, uint16_t height) override;

    legends_error_t set_machine_pc98(bool enable) override;



private:

    legends_handle handle_;

    bool own_handle_;

};



// Factory function

std::unique_ptr<RuntimeHost> create_runtime(const legends_config_t* config);



} // namespace legends



#endif // LEGENDS_RUNTIME_HOST_H
