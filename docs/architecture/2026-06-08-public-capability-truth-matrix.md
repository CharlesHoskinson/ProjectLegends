# Public Capability Truth Matrix: Exported APIs

This document inventories the 50 exported C APIs from `include/legends/legends_embed.h` and classifies the current direct and proxy behavior from `src/legends/legends_embed_api.cpp`, `src/legends_proxy/proxy_api.cpp`, and `src/engine_host/engine_dispatcher.cpp`.

The proxy column is intentionally conservative. A proxy wrapper that only reads shared memory is not marked fully supported unless the engine host also produces that shared memory. A proxy wrapper that sends an IPC message is not marked fully supported unless the engine dispatcher handles that message type.

## Classification Key

| Status | Meaning |
| :--- | :--- |
| `implemented` | Direct path has executable behavior and returns meaningful results. |
| `partial` | Some behavior exists, but the contract is incomplete, misleading, or depends on unwired infrastructure. |
| `unsupported` | Returns `LEGENDS_ERR_NOT_SUPPORTED` or is otherwise unavailable. |
| `stub-success` | Returns success or a fixed value without performing the promised operation. |
| `proxy-supported` | Proxy wrapper and engine dispatcher both implement the API path. |
| `proxy-partial` | Proxy-side code exists, but the engine host, shared-memory producer, or semantic parity is incomplete. |
| `proxy-missing` | Proxy returns unsupported or the engine dispatcher lacks the requested message path. |

## Important Findings

* The proxy runtime is not a complete product path yet. `ProxyConnection::connect()` creates framebuffer/audio shared memory, but `legends_engine_host` does not open or write those regions.
* `src/engine_host/engine_dispatcher.cpp` does not handle save/load, text capture, text input, or Phase 2+ feature messages beyond mount/unmount.
* Direct `legends_has_capability()` is stale: for example it reports `audio_capture = 0` even though `legends_capture_audio()` delegates to `dosbox_lib_get_audio_samples()`.
* Direct `legends_mount_drive()` supports only directories, even though public comments mention image-style mounting elsewhere.

## Lifecycle & Management

| Exported C API | Direct Mode Status | IPC/Proxy Mode Status | Evidence / Notes |
| :--- | :--- | :--- | :--- |
| `legends_get_api_version` | `implemented` | `proxy-supported` | Proxy sends GetApiVersionReq; dispatcher handles it. |
| `legends_create` | `implemented` | `proxy-supported` | Proxy sends CreateReq; dispatcher creates engine singleton. |
| `legends_destroy` | `implemented` | `proxy-supported` | Proxy sends DestroyReq; dispatcher destroys g_handle. |
| `legends_force_destroy` | `implemented` | `proxy-supported` | Proxy maps to DestroyReq; no distinct force semantics in proxy. |
| `legends_reset` | `implemented` | `proxy-supported` | Proxy sends ResetReq; dispatcher handles it. |
| `legends_get_config` | `implemented` | `proxy-supported` | Proxy sends GetConfigReq; dispatcher handles it. |

## Emulation Control

| Exported C API | Direct Mode Status | IPC/Proxy Mode Status | Evidence / Notes |
| :--- | :--- | :--- | :--- |
| `legends_step_ms` | `implemented` | `proxy-supported` | Proxy sends StepMsReq; dispatcher handles it. |
| `legends_step_cycles` | `implemented` | `proxy-supported` | Proxy sends StepCyclesReq; dispatcher handles it. |
| `legends_get_emu_time` | `implemented` | `proxy-supported` | Proxy sends GetEmuTimeReq; dispatcher handles it. |
| `legends_get_total_cycles` | `implemented` | `proxy-supported` | Proxy sends GetTotalCyclesReq; dispatcher handles it. |

## Screen & Frame Capture

| Exported C API | Direct Mode Status | IPC/Proxy Mode Status | Evidence / Notes |
| :--- | :--- | :--- | :--- |
| `legends_capture_text` | `implemented` | `proxy-supported` | Proxy sends CaptureTextReq; dispatcher handles it. |
| `legends_capture_rgb` | `implemented` | `proxy-partial` | Proxy reads framebuffer SHM, but engine host does not open/write framebuffer SHM. |
| `legends_is_frame_dirty` | `implemented` | `proxy-supported` | Proxy sends IsFrameDirtyReq; dispatcher handles it. |
| `legends_get_cursor` | `implemented` | `proxy-supported` | Proxy sends GetCursorReq; dispatcher handles it. |

## Input Injection

| Exported C API | Direct Mode Status | IPC/Proxy Mode Status | Evidence / Notes |
| :--- | :--- | :--- | :--- |
| `legends_key_event` | `implemented` | `proxy-supported` | Proxy sends KeyEventReq; dispatcher handles it. |
| `legends_key_event_ext` | `implemented` | `proxy-supported` | Proxy sends KeyEventExtReq; dispatcher handles it. |
| `legends_text_input` | `implemented` | `proxy-supported` | Proxy sends TextInputReq; dispatcher handles it. |
| `legends_mouse_event` | `implemented` | `proxy-supported` | Proxy sends MouseEventReq; dispatcher handles it. |

## Audio & Media Capture

| Exported C API | Direct Mode Status | IPC/Proxy Mode Status | Evidence / Notes |
| :--- | :--- | :--- | :--- |
| `legends_capture_audio` | `implemented` | `proxy-partial` | Proxy reads audio ring SHM, but engine host does not open/write the audio ring. |
| `legends_is_audio_active` | `implemented` | `proxy-supported` | Proxy sends IsAudioActiveReq; dispatcher handles it. |
| `legends_start_video_capture` | `unsupported` | `proxy-missing` | Proxy returns LEGENDS_ERR_NOT_SUPPORTED directly. |
| `legends_stop_video_capture` | `stub-success` | `proxy-missing` | Proxy returns LEGENDS_ERR_NOT_SUPPORTED directly. |
| `legends_is_video_capturing` | `stub-success` | `proxy-missing` | Proxy returns LEGENDS_ERR_NOT_SUPPORTED directly. |

## Save State & Determinism

| Exported C API | Direct Mode Status | IPC/Proxy Mode Status | Evidence / Notes |
| :--- | :--- | :--- | :--- |
| `legends_save_state` | `implemented` | `proxy-supported` | Proxy sends SaveStateReq; dispatcher handles it. |
| `legends_load_state` | `implemented` | `proxy-supported` | Proxy sends LoadStateReq; dispatcher handles it. |
| `legends_get_state_hash` | `implemented` | `proxy-supported` | Proxy sends GetStateHashReq; dispatcher handles it. |
| `legends_verify_determinism` | `implemented` | `proxy-supported` | Proxy sends VerifyDeterminismReq; dispatcher handles it. |

## Storage, Peripheral, Network, And Diagnostics

| Exported C API | Direct Mode Status | IPC/Proxy Mode Status | Evidence / Notes |
| :--- | :--- | :--- | :--- |
| `legends_get_last_error` | `implemented` | `proxy-supported` | Proxy sends GetLastErrorReq; dispatcher handles it. |
| `legends_mount_drive` | `partial` | `proxy-supported` | Proxy sends MountDriveReq, and dispatcher handles it and forwards to legends_mount_drive. |
| `legends_unmount_drive` | `implemented` | `proxy-supported` | Proxy sends UnmountDriveReq, and dispatcher handles it and forwards to legends_unmount_drive. |
| `legends_joystick_event` | `partial` | `proxy-partial` | Proxy sends JoystickEventReq and dispatcher routes it, but the underlying direct API remains partial. |
| `legends_midi_set_device` | `implemented` | `proxy-supported` | Proxy sends MidiSetDeviceReq; dispatcher handles it. |
| `legends_midi_set_soundfont` | `implemented` | `proxy-supported` | Proxy sends MidiSetSoundfontReq; dispatcher handles it. |
| `legends_midi_set_romdir` | `implemented` | `proxy-supported` | Proxy sends MidiSetRomdirReq; dispatcher handles it. |
| `legends_capture_midi_audio` | `implemented` | `proxy-supported` | Proxy sends CaptureMidiAudioReq; dispatcher handles it. |
| `legends_printer_set_output` | `implemented` | `proxy-supported` | Proxy sends PrinterSetOutputReq; dispatcher handles it. |
| `legends_printer_is_active` | `implemented` | `proxy-supported` | Proxy sends PrinterIsActiveReq; dispatcher handles it. |
| `legends_printer_flush` | `implemented` | `proxy-supported` | Proxy sends PrinterFlushReq; dispatcher handles it. |
| `legends_set_ttf_font` | `unsupported` | `proxy-missing` | Proxy returns LEGENDS_ERR_NOT_SUPPORTED directly. |
| `legends_ipx_enable` | `implemented` | `proxy-supported` | Proxy sends IpxEnableReq; dispatcher handles it. |
| `legends_ipx_connect` | `implemented` | `proxy-supported` | Proxy sends IpxConnectReq; dispatcher handles it. |
| `legends_ipx_disconnect` | `implemented` | `proxy-supported` | Proxy sends IpxDisconnectReq; dispatcher handles it. |
| `legends_ipx_is_connected` | `implemented` | `proxy-supported` | Proxy sends IpxIsConnectedReq; dispatcher handles it. |
| `legends_glide_enable` | `implemented` | `proxy-supported` | Proxy sends GlideEnableReq; dispatcher handles it. |
| `legends_glide_set_resolution` | `implemented` | `proxy-supported` | Proxy sends GlideSetResolutionReq; dispatcher handles it. |
| `legends_set_machine_pc98` | `implemented` | `proxy-supported` | Proxy sends SetMachinePc98Req; dispatcher handles it. |
| `legends_is_pc98_mode` | `implemented` | `proxy-supported` | Proxy sends IsPc98ModeReq; dispatcher handles it. |
| `legends_set_log_callback` | `implemented` | `proxy-missing` | Proxy returns LEGENDS_ERR_NOT_SUPPORTED directly. |
| `legends_register_event_callback` | `implemented` | `proxy-missing` | Proxy returns LEGENDS_ERR_NOT_SUPPORTED directly. |
| `legends_has_capability` | `partial` | `proxy-supported` | Proxy sends HasCapabilityReq; dispatcher handles it. |

## Auditor Notes

The direct API is broad but uneven. The proxy API is a limited control-channel prototype, not parity with the public C ABI. Future work should make capability discovery structured and generated from this matrix, or add tests that fail when a public API is added without direct/proxy classification.
