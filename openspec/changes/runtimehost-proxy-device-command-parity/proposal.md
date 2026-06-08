## Why

The application service migration routes input, MIDI, printer, IPX, Glide, PC-98, and capability operations through `RuntimeHost`. In process mode these delegate to implemented direct C ABI functions, but proxy mode still reports many of these as unsupported. That prevents the IPC backend from behaving like the in-process backend for app service controls.

## What Changes

Implement request/response proxy parity for command-style APIs that already have direct C ABI implementations:

- `legends_key_event_ext`
- `legends_text_input`
- `legends_joystick_event`
- `legends_midi_set_device`
- `legends_midi_set_soundfont`
- `legends_midi_set_romdir`
- `legends_capture_midi_audio`
- `legends_printer_set_output`
- `legends_printer_is_active`
- `legends_printer_flush`
- `legends_ipx_enable`
- `legends_ipx_connect`
- `legends_ipx_disconnect`
- `legends_ipx_is_connected`
- `legends_glide_enable`
- `legends_glide_set_resolution`
- `legends_set_machine_pc98`
- `legends_is_pc98_mode`
- `legends_has_capability`

## Scope

In scope:

- Simple command messages, string messages, bool/int query responses, and MIDI audio capture payloads.
- Dispatcher forwarding to existing direct APIs.
- Capability truth updates for APIs implemented in this change.

Out of scope:

- `legends_start_video_capture`, `legends_stop_video_capture`, and `legends_is_video_capturing` because direct support is app-owned/stubbed.
- `legends_set_ttf_font` unless direct support is changed from unsupported to real implementation.
- `legends_set_log_callback` and `legends_register_event_callback` because callback delivery requires a distinct async event channel design.

## Audit Strategy

Codex will check that only genuinely implemented direct/proxy pairs are promoted to `proxy-supported`; anything still unsupported must remain truthful in the matrix.
