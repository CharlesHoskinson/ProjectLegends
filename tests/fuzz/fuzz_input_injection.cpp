#include <legends/legends_embed.h>
#include <pal/platform.h>
#include <cstdint>
#include <cstddef>

static legends_handle g_handle = nullptr;
static bool g_initialized = false;

static void ensure_initialized() {
    if (!g_initialized) {
        pal::Platform::shutdown();
        pal::Platform::initialize(pal::Backend::Headless);
        legends_destroy(reinterpret_cast<legends_handle>(1));
        legends_config_t cfg = LEGENDS_CONFIG_INIT;
        legends_create(&cfg, &g_handle);
        g_initialized = true;
    }
}

extern "C" int LLVMFuzzerTestOneInput(const uint8_t* data, size_t size) {
    ensure_initialized();
    size_t offset = 0;
    while (offset + 4 <= size) {
        uint8_t type = data[offset] & 0x03;
        switch (type) {
        case 0: {
            uint8_t scancode = data[offset + 1];
            int pressed = data[offset + 2] & 1;
            legends_key_event(g_handle, scancode, pressed);
            break;
        }
        case 1: {
            int16_t dx = static_cast<int16_t>((data[offset+1] << 8) | data[offset+2]);
            int16_t dy = static_cast<int16_t>((data[offset+2] << 8) | data[offset+3]);
            legends_mouse_event(g_handle, dx, dy, data[offset+3] & 0x07);
            break;
        }
        default:
            break;
        }
        offset += 4;
        legends_step_result_t result;
        legends_step_cycles(g_handle, 100, &result);
    }
    legends_reset(g_handle);
    return 0;
}
