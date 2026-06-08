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
| `legends_get_api_version` | `implemented` | `proxy-supported` | Proxy sends `GetApiVersionReq`; dispatcher handles it. |
| `legends_create` | `implemented` | `proxy-supported` | Proxy sends `CreateReq`; dispatcher creates one engine singleton. |
| `legends_destroy` | `implemented` | `proxy-supported` | Proxy sends `DestroyReq`; dispatcher destroys `g_handle`. |
| `legends_force_destroy` | `implemented` | `proxy-supported` | Proxy maps to `DestroyReq`; no distinct force semantics in proxy. |
| `legends_reset` | `implemented` | `proxy-supported` | Proxy sends `ResetReq`; dispatcher handles it. |
| `legends_get_config` | `implemented` | `proxy-missing` | Proxy returns `LEGENDS_ERR_NOT_SUPPORTED`. |

## Emulation Control

| Exported C API | Direct Mode Status | IPC/Proxy Mode Status | Evidence / Notes |
| :--- | :--- | :--- | :--- |
| `legends_step_ms` | `implemented` | `proxy-supported` | Proxy sends `StepMsReq`; dispatcher handles it. |
| `legends_step_cycles` | `implemented` | `proxy-supported` | Proxy sends `StepCyclesReq`; dispatcher handles it. |
| `legends_get_emu_time` | `implemented` | `proxy-supported` | Proxy sends `GetEmuTimeReq`; dispatcher handles it. |
| `legends_get_total_cycles` | `implemented` | `proxy-supported` | Proxy sends `GetTotalCyclesReq`; dispatcher handles it. |

## Screen & Frame Capture

| Exported C API | Direct Mode Status | IPC/Proxy Mode Status | Evidence / Notes |
| :--- | :--- | :--- | :--- |
| `legends_capture_text` | `implemented` | `proxy-missing` | Proxy returns `LEGENDS_ERR_NOT_SUPPORTED`. |
| `legends_capture_rgb` | `implemented` | `proxy-partial` | Proxy reads framebuffer SHM, but engine host does not open/write framebuffer SHM. |
| `legends_is_frame_dirty` | `implemented` | `proxy-supported` | Proxy sends `IsFrameDirtyReq`; dispatcher handles it. |
| `legends_get_cursor` | `implemented` | `proxy-supported` | Proxy sends `GetCursorReq`; dispatcher handles it. |

## Input Injection

| Exported C API | Direct Mode Status | IPC/Proxy Mode Status | Evidence / Notes |
| :--- | :--- | :--- | :--- |
| `legends_key_event` | `implemented` | `proxy-supported` | Proxy sends `KeyEventReq`; dispatcher handles it. |
| `legends_key_event_ext` | `implemented` | `proxy-partial` | Proxy aliases to `legends_key_event`; extended E0 semantics are not represented in IPC. |
| `legends_text_input` | `implemented` | `proxy-missing` | Proxy returns `LEGENDS_ERR_NOT_SUPPORTED`. |
| `legends_mouse_event` | `implemented` | `proxy-supported` | Proxy sends `MouseEventReq`; dispatcher handles it. |

## Audio & Media Capture

| Exported C API | Direct Mode Status | IPC/Proxy Mode Status | Evidence / Notes |
| :--- | :--- | :--- | :--- |
| `legends_capture_audio` | `implemented` | `proxy-partial` | Proxy reads audio ring SHM, but engine host does not open/write the audio ring. |
| `legends_is_audio_active` | `implemented` | `proxy-supported` | Proxy sends `IsAudioActiveReq`; dispatcher handles it. |
| `legends_start_video_capture` | `unsupported` | `proxy-missing` | Direct returns `LEGENDS_ERR_NOT_SUPPORTED`; proxy also returns unsupported. |
| `legends_stop_video_capture` | `stub-success` | `proxy-missing` | Direct returns `LEGENDS_OK` without stopping an app capture controller; proxy returns unsupported. |
| `legends_is_video_capturing` | `stub-success` | `proxy-missing` | Direct always reports `0`; proxy returns unsupported. |

## Save State & Determinism

| Exported C API | Direct Mode Status | IPC/Proxy Mode Status | Evidence / Notes |
| :--- | :--- | :--- | :--- |
| `legends_save_state` | `implemented` | `proxy-missing` | Proxy returns `LEGENDS_ERR_NOT_SUPPORTED`; dispatcher has no `SaveStateReq` case. |
| `legends_load_state` | `implemented` | `proxy-missing` | Proxy returns `LEGENDS_ERR_NOT_SUPPORTED`; dispatcher has no `LoadStateReq` case. |
| `legends_get_state_hash` | `implemented` | `proxy-supported` | Proxy sends `GetStateHashReq`; dispatcher handles it. |
| `legends_verify_determinism` | `implemented` | `proxy-missing` | Proxy returns `LEGENDS_ERR_NOT_SUPPORTED`. |

## Storage, Peripheral, Network, And Diagnostics

| Exported C API | Direct Mode Status | IPC/Proxy Mode Status | Evidence / Notes |
| :--- | :--- | :--- | :--- |
| `legends_get_last_error` | `implemented` | `proxy-missing` | Proxy returns `LEGENDS_ERR_NOT_SUPPORTED`. |
| `legends_mount_drive` | `partial` | `proxy-supported` | Direct supports only directory mounts; proxy sends `MountDriveReq`, which is dispatched to the engine host. |
| `legends_unmount_drive` | `implemented` | `proxy-supported` | Proxy sends `UnmountDriveReq`, which is dispatched to the engine host. |
| `legends_joystick_event` | `partial` | `proxy-missing` | Direct mutates BDA then returns `LEGENDS_ERR_NOT_SUPPORTED`; proxy returns unsupported. |
| `legends_midi_set_device` | `implemented` | `proxy-missing` | Proxy returns unsupported. |
| `legends_midi_set_soundfont` | `implemented` | `proxy-missing` | Proxy returns unsupported. |
| `legends_midi_set_romdir` | `implemented` | `proxy-missing` | Proxy returns unsupported. |
| `legends_capture_midi_audio` | `implemented` | `proxy-missing` | Proxy returns unsupported. |
| `legends_printer_set_output` | `implemented` | `proxy-missing` | Proxy returns unsupported. |
| `legends_printer_is_active` | `implemented` | `proxy-missing` | Proxy returns unsupported. |
| `legends_printer_flush` | `implemented` | `proxy-missing` | Proxy returns unsupported. |
| `legends_set_ttf_font` | `unsupported` | `proxy-missing` | Direct returns unsupported because TTF is app-layer owned. |
| `legends_ipx_enable` | `implemented` | `proxy-missing` | Proxy returns unsupported. |
| `legends_ipx_connect` | `implemented` | `proxy-missing` | Proxy returns unsupported. |
| `legends_ipx_disconnect` | `implemented` | `proxy-missing` | Proxy returns unsupported. |
| `legends_ipx_is_connected` | `implemented` | `proxy-missing` | Proxy returns unsupported. |
| `legends_glide_enable` | `implemented` | `proxy-missing` | Proxy returns unsupported. |
| `legends_glide_set_resolution` | `implemented` | `proxy-missing` | Proxy returns unsupported. |
| `legends_set_machine_pc98` | `implemented` | `proxy-missing` | Proxy returns unsupported. |
| `legends_is_pc98_mode` | `implemented` | `proxy-missing` | Proxy returns unsupported. |
| `legends_set_log_callback` | `implemented` | `proxy-missing` | Proxy returns `LEGENDS_ERR_NOT_SUPPORTED`. |
| `legends_register_event_callback` | `implemented` | `proxy-missing` | Proxy returns `LEGENDS_ERR_NOT_SUPPORTED`. |
| `legends_has_capability` | `partial` | `proxy-missing` | Direct table is stale/incomplete; proxy returns unsupported. |

## Auditor Notes

The direct API is broad but uneven. The proxy API is a limited control-channel prototype, not parity with the public C ABI. Future work should make capability discovery structured and generated from this matrix, or add tests that fail when a public API is added without direct/proxy classification.
