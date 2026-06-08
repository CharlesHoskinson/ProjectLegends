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
};

// Subclass: InProcessEngineRuntime
class InProcessEngineRuntime : public RuntimeHost {
public:
    explicit InProcessEngineRuntime(legends_handle handle);
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

private:
    legends_handle handle_;
};

// Subclass: IpcEngineRuntime
class IpcEngineRuntime : public RuntimeHost {
public:
    explicit IpcEngineRuntime(legends_handle handle);
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

private:
    legends_handle handle_;
};

// Factory function
std::unique_ptr<RuntimeHost> create_runtime(const legends_config_t* config);

} // namespace legends

#endif // LEGENDS_RUNTIME_HOST_H
