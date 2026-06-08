## Status: IMPLEMENTED

The design has been implemented and is under Codex audit.

## Context

All remaining routable application-layer direct FFI calls must route through `RuntimeHost`. Only `legends_create` and `legends_destroy` will remain as exceptions.

## Decisions

### 1. RuntimeHost Interface Expansion

The following 16 methods will be added as pure virtual overrides to the `RuntimeHost` interface:
```cpp
    virtual legends_error_t reset() = 0;
    virtual legends_error_t text_input(std::string_view text) = 0;
    virtual legends_error_t get_cursor(int* x_out, int* y_out, int* visible_out) = 0;
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
```
Note: In `legends_get_cursor`, the ABI uses `uint8_t* x_out, uint8_t* y_out, int* visible_out`. The signature inside `RuntimeHost` should match this signature to avoid conversion mismatch issues.

### 2. Application Routing

In `Application::init`, FFI calls for mounting, logging, and setting up machines/devices are replaced with `runtime_->*` calls immediately after `runtime_` is allocated.
In `Application::processEvents`, `legends_joystick_event` is routed through `runtime_->joystick_event`.
In Action Handlers: screenshot and save state capture paths will use `runtime_->capture_rgb` instead of direct FFI `legends_capture_rgb`.

### 3. AI Screen Context Routing

In `src/app/ai_screen_context.h` and `src/app/ai_screen_context.cpp`:
Change `captureScreenContext(legends_handle handle...)` to:
`captureScreenContext(RuntimeHost& runtime, uint32_t max_chars = 10000)`
And keep a backwards-compatible overload for raw handles if needed:
`captureScreenContext(legends_handle handle...)` that delegates through a temporary non-owning `InProcessEngineRuntime`.

### 4. Bypass Allowlist Clean

All entries in `docs/architecture/runtimehost-bypass-allowlist.json` will be deleted except for `legends_create` and `legends_destroy`.

## Risks / Trade-offs

- **ABI signature alignment**: Must ensure type matching (e.g. `int` vs `uint8_t` for coordinates) corresponds to the C ABI header `legends_embed.h` declarations.
- **String lifetime**: RuntimeHost methods that accept `std::string_view` must copy to a null-terminated `std::string` before delegating to C ABI functions that accept `const char*`.

## Verification Commands

- `cmake --build --preset dev`
- `build/dev/legends_abi_test.exe`
- `build/dev/legends_unit_tests.exe`
- `python scripts/graphify_projectlegends.py update --repo . --source-only`
- `python scripts/check_graphify_enrichment.py --repo . --overlay graphify-out/projectlegends-enrichment.json --strict --strict-tests fail --allow-missing-graphify`
