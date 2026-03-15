/**
 * @file vga_bridge.cpp
 * @brief VGA hardware register snapshot/restore for serialization.
 *
 * Bridges between the library mode serialization API and the VGA_Type
 * hardware state. Compiled as C++17 in a separate OBJECT library because
 * vga.h uses default member initializers in unnamed typedef structs
 * (legacy DOSBox-X style) which is a hard error under C++23 (C7626).
 *
 * @copyright GPL-2.0-or-later
 */

// Only include what we need — avoid cpu_bridge.h which transitively
// pulls in error_model.h (needs std::source_location, C++20+).
#include "dosbox/engine_state.h"
#include "vga.h"

#include <cstdint>
#include <cstring>

// In headless/test builds, VGA subsystem files (vga.cpp, vga_memory.cpp, vga_compat.cpp)
// are not linked. Provide stub implementations for symbols referenced here.
#if defined(AIBOX_HEADLESS)
static VGA_Type s_fallback_vga_hw = {};
VGA_Type& vga_get_hw() { return s_fallback_vga_hw; }
void VGA_DetermineMode(void) {}
void VGA_SetupHandlers(void) {}
#endif

namespace dosbox {

bool vga_hw_available() {
    return vga.mem.linear != nullptr;
}

uint8_t* vga_mem_linear() {
    return vga.mem.linear;
}

uint32_t vga_mem_size() {
    return vga.mem.memsize;
}

void vga_post_restore() {
    VGA_DetermineMode();
    VGA_SetupHandlers();
}

void snapshot_vga_registers(EngineStateVgaRegisters& out) {
    std::memset(&out, 0, sizeof(out));

    // Misc output
    out.misc_output = vga.misc_output;
    out.internal_attrindex = vga.internal.attrindex ? 1 : 0;

    // Sequencer
    out.seq_index = vga.seq.index;
    out.seq_reset = vga.seq.reset;
    out.seq_clocking_mode = vga.seq.clocking_mode;
    out.seq_map_mask = vga.seq.map_mask;
    out.seq_character_map_select = vga.seq.character_map_select;
    out.seq_memory_mode = vga.seq.memory_mode;

    // Attribute controller
    std::memcpy(out.attr_palette, vga.attr.palette, 16);
    out.attr_mode_control = vga.attr.mode_control;
    out.attr_horizontal_pel_panning = vga.attr.horizontal_pel_panning;
    out.attr_overscan_color = vga.attr.overscan_color;
    out.attr_color_plane_enable = vga.attr.color_plane_enable;
    out.attr_color_select = vga.attr.color_select;
    out.attr_index = vga.attr.index;
    out.attr_disabled = vga.attr.disabled;

    // CRTC
    out.crtc_horizontal_total = vga.crtc.horizontal_total;
    out.crtc_horizontal_display_end = vga.crtc.horizontal_display_end;
    out.crtc_start_horizontal_blanking = vga.crtc.start_horizontal_blanking;
    out.crtc_end_horizontal_blanking = vga.crtc.end_horizontal_blanking;
    out.crtc_start_horizontal_retrace = vga.crtc.start_horizontal_retrace;
    out.crtc_end_horizontal_retrace = vga.crtc.end_horizontal_retrace;
    out.crtc_vertical_total = vga.crtc.vertical_total;
    out.crtc_overflow = vga.crtc.overflow;
    out.crtc_preset_row_scan = vga.crtc.preset_row_scan;
    out.crtc_maximum_scan_line = vga.crtc.maximum_scan_line;
    out.crtc_cursor_start = vga.crtc.cursor_start;
    out.crtc_cursor_end = vga.crtc.cursor_end;
    out.crtc_start_address_high = vga.crtc.start_address_high;
    out.crtc_start_address_low = vga.crtc.start_address_low;
    out.crtc_cursor_location_high = vga.crtc.cursor_location_high;
    out.crtc_cursor_location_low = vga.crtc.cursor_location_low;
    out.crtc_vertical_retrace_start = vga.crtc.vertical_retrace_start;
    out.crtc_vertical_retrace_end = vga.crtc.vertical_retrace_end;
    out.crtc_vertical_display_end = vga.crtc.vertical_display_end;
    out.crtc_offset = vga.crtc.offset;
    out.crtc_underline_location = vga.crtc.underline_location;
    out.crtc_start_vertical_blanking = vga.crtc.start_vertical_blanking;
    out.crtc_end_vertical_blanking = vga.crtc.end_vertical_blanking;
    out.crtc_mode_control = vga.crtc.mode_control;
    out.crtc_line_compare = vga.crtc.line_compare;
    out.crtc_index = vga.crtc.index;
    out.crtc_read_only = vga.crtc.read_only ? 1 : 0;

    // Graphics controller
    out.gfx_index = vga.gfx.index;
    out.gfx_set_reset = vga.gfx.set_reset;
    out.gfx_enable_set_reset = vga.gfx.enable_set_reset;
    out.gfx_color_compare = vga.gfx.color_compare;
    out.gfx_data_rotate = vga.gfx.data_rotate;
    out.gfx_read_map_select = vga.gfx.read_map_select;
    out.gfx_mode = vga.gfx.mode;
    out.gfx_miscellaneous = vga.gfx.miscellaneous;
    out.gfx_color_dont_care = vga.gfx.color_dont_care;
    out.gfx_bit_mask = vga.gfx.bit_mask;

    // DAC
    out.dac_bits = vga.dac.bits;
    out.dac_pel_mask = vga.dac.pel_mask;
    out.dac_pel_index = vga.dac.pel_index;
    out.dac_state = vga.dac.state;
    out.dac_write_index = vga.dac.write_index;
    out.dac_read_index = vga.dac.read_index;
    out.dac_hidac_counter = vga.dac.hidac_counter;
    out.dac_reg02 = vga.dac.reg02;
    out.dac_first_changed = static_cast<uint32_t>(vga.dac.first_changed);
    std::memcpy(out.dac_combine, vga.dac.combine, 16);
    for (int i = 0; i < 256; ++i) {
        out.dac_rgb[i * 3 + 0] = vga.dac.rgb[i].red;
        out.dac_rgb[i * 3 + 1] = vga.dac.rgb[i].green;
        out.dac_rgb[i * 3 + 2] = vga.dac.rgb[i].blue;
    }
    std::memcpy(out.dac_xlat16, vga.dac.xlat16, sizeof(out.dac_xlat16));
    std::memcpy(out.dac_xlat32, vga.dac.xlat32, sizeof(out.dac_xlat32));

    // Latch
    out.latch = vga.latch.d;

    // VGA_Config
    out.config_display_start = static_cast<uint32_t>(vga.config.display_start);
    out.config_real_start = static_cast<uint32_t>(vga.config.real_start);
    out.config_scan_len = static_cast<uint32_t>(vga.config.scan_len);
    out.config_cursor_start = static_cast<uint32_t>(vga.config.cursor_start);
    out.config_line_compare = static_cast<uint32_t>(vga.config.line_compare);
    out.config_full_bit_mask = vga.config.full_bit_mask;
    out.config_full_map_mask = vga.config.full_map_mask;
    out.config_full_not_map_mask = vga.config.full_not_map_mask;
    out.config_full_set_reset = vga.config.full_set_reset;
    out.config_full_not_enable_set_reset = vga.config.full_not_enable_set_reset;
    out.config_full_enable_set_reset = vga.config.full_enable_set_reset;
    out.config_full_enable_and_set_reset = vga.config.full_enable_and_set_reset;
    out.config_retrace = vga.config.retrace ? 1 : 0;
    out.config_chained = vga.config.chained ? 1 : 0;
    out.config_compatible_chain4 = vga.config.compatible_chain4 ? 1 : 0;
    out.config_pel_panning = vga.config.pel_panning;
    out.config_hlines_skip = vga.config.hlines_skip;
    out.config_bytes_skip = vga.config.bytes_skip;
    out.config_addr_shift = vga.config.addr_shift;
    out.config_read_mode = vga.config.read_mode;
    out.config_write_mode = vga.config.write_mode;
    out.config_read_map_select = vga.config.read_map_select;
    out.config_color_dont_care = vga.config.color_dont_care;
    out.config_color_compare = vga.config.color_compare;
    out.config_data_rotate = vga.config.data_rotate;
    out.config_raster_op = vga.config.raster_op;

    // SVGA bank state
    out.svga_read_start = static_cast<uint32_t>(vga.svga.readStart);
    out.svga_write_start = static_cast<uint32_t>(vga.svga.writeStart);
    out.svga_bank_mask_full = static_cast<uint32_t>(vga.svga.bankMask);
    out.svga_bank_read_full = static_cast<uint32_t>(vga.svga.bank_read_full);
    out.svga_bank_write_full = static_cast<uint32_t>(vga.svga.bank_write_full);
    out.svga_bank_read = vga.svga.bank_read;
    out.svga_bank_write = vga.svga.bank_write;
    out.svga_bank_mask = vga.svga.bank_mask;
    out.svga_bank_size = static_cast<uint32_t>(vga.svga.bank_size);

    // Memory metadata (not VRAM data)
    out.mem_memsize = vga.mem.memsize;
    out.mem_memmask = vga.mem.memmask;
    out.mem_memmask_crtc = vga.mem.memmask_crtc;
    out.mem_memsize_original = vga.mem.memsize_original;
    out.mem_vbe_memsize = vga.mem.vbe_memsize;
}

void restore_vga_registers(const EngineStateVgaRegisters& in) {
    // Misc output
    vga.misc_output = in.misc_output;
    vga.internal.attrindex = in.internal_attrindex != 0;

    // Sequencer
    vga.seq.index = in.seq_index;
    vga.seq.reset = in.seq_reset;
    vga.seq.clocking_mode = in.seq_clocking_mode;
    vga.seq.map_mask = in.seq_map_mask;
    vga.seq.character_map_select = in.seq_character_map_select;
    vga.seq.memory_mode = in.seq_memory_mode;

    // Attribute controller
    std::memcpy(vga.attr.palette, in.attr_palette, 16);
    vga.attr.mode_control = in.attr_mode_control;
    vga.attr.horizontal_pel_panning = in.attr_horizontal_pel_panning;
    vga.attr.overscan_color = in.attr_overscan_color;
    vga.attr.color_plane_enable = in.attr_color_plane_enable;
    vga.attr.color_select = in.attr_color_select;
    vga.attr.index = in.attr_index;
    vga.attr.disabled = in.attr_disabled;

    // CRTC
    vga.crtc.horizontal_total = in.crtc_horizontal_total;
    vga.crtc.horizontal_display_end = in.crtc_horizontal_display_end;
    vga.crtc.start_horizontal_blanking = in.crtc_start_horizontal_blanking;
    vga.crtc.end_horizontal_blanking = in.crtc_end_horizontal_blanking;
    vga.crtc.start_horizontal_retrace = in.crtc_start_horizontal_retrace;
    vga.crtc.end_horizontal_retrace = in.crtc_end_horizontal_retrace;
    vga.crtc.vertical_total = in.crtc_vertical_total;
    vga.crtc.overflow = in.crtc_overflow;
    vga.crtc.preset_row_scan = in.crtc_preset_row_scan;
    vga.crtc.maximum_scan_line = in.crtc_maximum_scan_line;
    vga.crtc.cursor_start = in.crtc_cursor_start;
    vga.crtc.cursor_end = in.crtc_cursor_end;
    vga.crtc.start_address_high = in.crtc_start_address_high;
    vga.crtc.start_address_low = in.crtc_start_address_low;
    vga.crtc.cursor_location_high = in.crtc_cursor_location_high;
    vga.crtc.cursor_location_low = in.crtc_cursor_location_low;
    vga.crtc.vertical_retrace_start = in.crtc_vertical_retrace_start;
    vga.crtc.vertical_retrace_end = in.crtc_vertical_retrace_end;
    vga.crtc.vertical_display_end = in.crtc_vertical_display_end;
    vga.crtc.offset = in.crtc_offset;
    vga.crtc.underline_location = in.crtc_underline_location;
    vga.crtc.start_vertical_blanking = in.crtc_start_vertical_blanking;
    vga.crtc.end_vertical_blanking = in.crtc_end_vertical_blanking;
    vga.crtc.mode_control = in.crtc_mode_control;
    vga.crtc.line_compare = in.crtc_line_compare;
    vga.crtc.index = in.crtc_index;
    vga.crtc.read_only = in.crtc_read_only != 0;

    // Graphics controller
    vga.gfx.index = in.gfx_index;
    vga.gfx.set_reset = in.gfx_set_reset;
    vga.gfx.enable_set_reset = in.gfx_enable_set_reset;
    vga.gfx.color_compare = in.gfx_color_compare;
    vga.gfx.data_rotate = in.gfx_data_rotate;
    vga.gfx.read_map_select = in.gfx_read_map_select;
    vga.gfx.mode = in.gfx_mode;
    vga.gfx.miscellaneous = in.gfx_miscellaneous;
    vga.gfx.color_dont_care = in.gfx_color_dont_care;
    vga.gfx.bit_mask = in.gfx_bit_mask;

    // DAC
    vga.dac.bits = in.dac_bits;
    vga.dac.pel_mask = in.dac_pel_mask;
    vga.dac.pel_index = in.dac_pel_index;
    vga.dac.state = in.dac_state;
    vga.dac.write_index = in.dac_write_index;
    vga.dac.read_index = in.dac_read_index;
    vga.dac.hidac_counter = in.dac_hidac_counter;
    vga.dac.reg02 = in.dac_reg02;
    vga.dac.first_changed = static_cast<Bitu>(in.dac_first_changed);
    std::memcpy(vga.dac.combine, in.dac_combine, 16);
    for (int i = 0; i < 256; ++i) {
        vga.dac.rgb[i].red   = in.dac_rgb[i * 3 + 0];
        vga.dac.rgb[i].green = in.dac_rgb[i * 3 + 1];
        vga.dac.rgb[i].blue  = in.dac_rgb[i * 3 + 2];
    }
    std::memcpy(vga.dac.xlat16, in.dac_xlat16, sizeof(in.dac_xlat16));
    std::memcpy(vga.dac.xlat32, in.dac_xlat32, sizeof(in.dac_xlat32));

    // Latch
    vga.latch.d = in.latch;

    // VGA_Config
    vga.config.display_start = static_cast<Bitu>(in.config_display_start);
    vga.config.real_start = static_cast<Bitu>(in.config_real_start);
    vga.config.scan_len = static_cast<Bitu>(in.config_scan_len);
    vga.config.cursor_start = static_cast<Bitu>(in.config_cursor_start);
    vga.config.line_compare = static_cast<Bitu>(in.config_line_compare);
    vga.config.full_bit_mask = in.config_full_bit_mask;
    vga.config.full_map_mask = in.config_full_map_mask;
    vga.config.full_not_map_mask = in.config_full_not_map_mask;
    vga.config.full_set_reset = in.config_full_set_reset;
    vga.config.full_not_enable_set_reset = in.config_full_not_enable_set_reset;
    vga.config.full_enable_set_reset = in.config_full_enable_set_reset;
    vga.config.full_enable_and_set_reset = in.config_full_enable_and_set_reset;
    vga.config.retrace = in.config_retrace != 0;
    vga.config.chained = in.config_chained != 0;
    vga.config.compatible_chain4 = in.config_compatible_chain4 != 0;
    vga.config.pel_panning = in.config_pel_panning;
    vga.config.hlines_skip = in.config_hlines_skip;
    vga.config.bytes_skip = in.config_bytes_skip;
    vga.config.addr_shift = in.config_addr_shift;
    vga.config.read_mode = in.config_read_mode;
    vga.config.write_mode = in.config_write_mode;
    vga.config.read_map_select = in.config_read_map_select;
    vga.config.color_dont_care = in.config_color_dont_care;
    vga.config.color_compare = in.config_color_compare;
    vga.config.data_rotate = in.config_data_rotate;
    vga.config.raster_op = in.config_raster_op;

    // SVGA bank state
    vga.svga.readStart = static_cast<Bitu>(in.svga_read_start);
    vga.svga.writeStart = static_cast<Bitu>(in.svga_write_start);
    vga.svga.bankMask = static_cast<Bitu>(in.svga_bank_mask_full);
    vga.svga.bank_read_full = static_cast<Bitu>(in.svga_bank_read_full);
    vga.svga.bank_write_full = static_cast<Bitu>(in.svga_bank_write_full);
    vga.svga.bank_read = in.svga_bank_read;
    vga.svga.bank_write = in.svga_bank_write;
    vga.svga.bank_mask = in.svga_bank_mask;
    vga.svga.bank_size = static_cast<Bitu>(in.svga_bank_size);

    // Memory metadata
    vga.mem.memsize = in.mem_memsize;
    vga.mem.memmask = in.mem_memmask;
    vga.mem.memmask_crtc = in.mem_memmask_crtc;
    vga.mem.memsize_original = in.mem_memsize_original;
    vga.mem.vbe_memsize = in.mem_vbe_memsize;
}

} // namespace dosbox
