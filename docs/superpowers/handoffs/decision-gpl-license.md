# GPL-2.0-Only vs GPL-2.0-or-Later Decision Brief

Prepared: 2026-06-10  
Prepared by: GPT 5.5 Codex  
Resolution status (2026-06-10): the recommended Option A (`GPL-2.0-or-later`) was applied as a **documentation alignment** in the working session — `README.md`, `CONTRIBUTING.md`, and `LICENSE` were updated so the prose matches the source SPDX markers already present (no source marker was changed). This is documentation cleanup, not legal advice; a formal license declaration remains the maintainer's to confirm.

## Facts Verified at HEAD

- The root `LICENSE` explicitly reserves the GPL-only versus GPL-or-later decision: `LICENSE:13-16`.
- `NOTICE:5-7` identifies the vendored DOSBox-X component as "GNU General Public License v2.0".
- Actual SPDX marker scan found 201 files with `SPDX-License-Identifier: GPL-2.0-or-later`.
- Actual SPDX marker scan found 0 source files with `SPDX-License-Identifier: GPL-2.0-only`. The single `GPL-2.0-only` SPDX text occurrence is a documentation example in `CONTRIBUTING.md:232`.
- Current documentation conflicts with the source markers: `README.md:278`, `README.md:288`, `README.md:293`, `README.md:300`, `README.md:302`, `README.md:366`, and `README.md:375` use GPL-only language; `CONTRIBUTING.md:226`, `CONTRIBUTING.md:252-259` also use GPL-only language.
- `DEPENDENCIES.md:18` already describes the project as GPL-2.0-or-later.

Commands used for the source-marker facts:

```powershell
rg -n "^[#/* ]*SPDX-License-Identifier: GPL-2\.0-or-later" --glob "!audit-wiki/**" --glob "!graphify-out/**" --glob "!.git/**"
rg -n "^[#/* ]*SPDX-License-Identifier: GPL-2\.0-only" --glob "!audit-wiki/**" --glob "!graphify-out/**" --glob "!.git/**"
rg -n "GPL-2\.0-only|GPL--2\.0|GPL-2.0-or-later|SPDX expression" README.md CONTRIBUTING.md LICENSE DEPENDENCIES.md
```

## Option A: Choose GPL-2.0-or-Later

This aligns project documentation with the 201 current `GPL-2.0-or-later` SPDX markers and with `DEPENDENCIES.md:18`.

Implications:

- Lowest source churn: no source SPDX headers need to change.
- Documentation should stop saying GPL-2.0-only for project-owned core code.
- The root `LICENSE` would change from "decision reserved" to the chosen project policy while still preserving third-party notices.
- Downstream recipients may use GPL v2 or, at their option, a later GPL version for project-owned GPL-marked files.

Exact file list to change if the owner chooses this option:

- `README.md`
- `CONTRIBUTING.md`
- `LICENSE`

## Option B: Choose GPL-2.0-Only

This aligns project documentation that already says GPL-only, but it requires changing every current `GPL-2.0-or-later` source marker and the docs that currently say or-later.

Implications:

- High source churn across project code, tests, benchmarks, CMake templates, and selected engine-local compatibility files.
- Removes the "or later" permission currently present in source SPDX markers.
- Requires owner/legal confirmation that every file currently marked `GPL-2.0-or-later` can be narrowed.

Exact additional documentation files to change if the owner chooses this option:

- `DEPENDENCIES.md`
- `LICENSE`

Exact SPDX-marker file list to change if the owner chooses this option:

```text
benchmarks/bench_emulation.cpp
benchmarks/bench_pal.cpp
cmake/dependencies.cmake
cmake/legends_version.h.in
cmake/packaging.cmake
cmake/version.cmake
engine/src/hardware/imfc_rom.c
engine/src/hardware/imfc.cpp
engine/src/hardware/memory_compat.cpp
engine/src/hardware/pic_compat.cpp
engine/src/hardware/vga_compat.cpp
engine/src/ints/int10_compat.cpp
engine/src/libs/decoders/flac.c
engine/src/libs/decoders/mp3.cpp
engine/src/libs/zmbv/zmbv_stubs.cpp
engine/tests/dos_files_tests.cpp
engine/tests/drives_tests.cpp
engine/tests/shell_cmds_tests.cpp
external/glad/glad.c
external/glad/glad/glad.h
external/glad/KHR/khrplatform.h
include/legends/legends_export.h
include/legends/runtime_host.h
include/pal/audio_sink.h
include/pal/context.h
include/pal/host_clock.h
include/pal/input_source.h
include/pal/platform.h
include/pal/types.h
include/pal/window.h
scripts/generate_checksums.py
src/app/action_bus.cpp
src/app/action_bus.h
src/app/ai_config.cpp
src/app/ai_config.h
src/app/ai_http_client.cpp
src/app/ai_http_client.h
src/app/ai_panel.cpp
src/app/ai_panel.h
src/app/ai_screen_context.cpp
src/app/ai_screen_context.h
src/app/application.cpp
src/app/application.h
src/app/audio_mixer.cpp
src/app/audio_mixer.h
src/app/capture.cpp
src/app/capture.h
src/app/cli_parser.cpp
src/app/cli_parser.h
src/app/config_parser.cpp
src/app/config_parser.h
src/app/crash_breadcrumb.cpp
src/app/crash_breadcrumb.h
src/app/crash_reporter.cpp
src/app/crash_reporter.h
src/app/error_reporter.cpp
src/app/error_reporter.h
src/app/file_logger.cpp
src/app/file_logger.h
src/app/glide_config.cpp
src/app/glide_config.h
src/app/hotkey_dispatcher.cpp
src/app/hotkey_dispatcher.h
src/app/image_validator.cpp
src/app/image_validator.h
src/app/input_mapper.cpp
src/app/input_mapper.h
src/app/ipx_config.cpp
src/app/ipx_config.h
src/app/joystick_mapper.cpp
src/app/joystick_mapper.h
src/app/mapper_ui.cpp
src/app/mapper_ui.h
src/app/menu_system.cpp
src/app/menu_system.h
src/app/midi_config.cpp
src/app/midi_config.h
src/app/mount_manager.cpp
src/app/mount_manager.h
src/app/overlay_render.cpp
src/app/overlay_render.h
src/app/pc98_config.cpp
src/app/pc98_config.h
src/app/perf_overlay.h
src/app/platform_dirs.cpp
src/app/platform_dirs.h
src/app/portable_mode.cpp
src/app/portable_mode.h
src/app/printer_manager.cpp
src/app/printer_manager.h
src/app/runtime_host.cpp
src/app/save_browser.cpp
src/app/save_browser.h
src/app/save_manager.cpp
src/app/save_manager.h
src/app/scancode_map.cpp
src/app/scancode_map.h
src/app/shader_presets.cpp
src/app/shader_presets.h
src/app/shader_renderer.cpp
src/app/shader_renderer.h
src/app/ttf_renderer.cpp
src/app/ttf_renderer.h
src/app/update_checker_linux.cpp
src/app/update_checker_mac.cpp
src/app/update_checker_win.cpp
src/app/update_checker.cpp
src/app/update_checker.h
src/app/video_capture.cpp
src/app/video_capture.h
src/app/zmbv_codec.cpp
src/app/zmbv_codec.h
src/engine_host/cli_parser.cpp
src/engine_host/cli_parser.h
src/engine_host/engine_dispatcher.cpp
src/engine_host/engine_dispatcher.h
src/engine_host/main.cpp
src/engine_host/version_info.cpp
src/legends/internal/cp437_font_8x16.h
src/main.cpp
src/pal/headless/audio_sink_headless.cpp
src/pal/headless/context_headless.cpp
src/pal/headless/host_clock_headless.cpp
src/pal/headless/input_source_headless.cpp
src/pal/headless/platform_headless.cpp
src/pal/headless/window_headless.cpp
src/pal/sdl2/audio_sink_sdl2.cpp
src/pal/sdl2/context_sdl2.cpp
src/pal/sdl2/host_clock_sdl2.cpp
src/pal/sdl2/input_source_sdl2.cpp
src/pal/sdl2/platform_sdl2.cpp
src/pal/sdl2/window_sdl2.cpp
src/pal/sdl3/audio_sink_sdl3.cpp
src/pal/sdl3/context_sdl3.cpp
src/pal/sdl3/host_clock_sdl3.cpp
src/pal/sdl3/input_source_sdl3.cpp
src/pal/sdl3/platform_sdl3.cpp
src/pal/sdl3/window_sdl3.cpp
tests/fuzz/fuzz_config_parser.cpp
tests/fuzz/fuzz_engine_memory_blob.cpp
tests/integration/test_audio_validation.cpp
tests/integration/test_boot_to_prompt.cpp
tests/integration/test_dynamic_resolution.cpp
tests/integration/test_event_callbacks.cpp
tests/integration/test_full_lifecycle.cpp
tests/integration/test_mount_lifecycle.cpp
tests/integration/test_soak_endurance.cpp
tests/integration/test_utils/integration_fixture.h
tests/integration/test_video_capture_lifecycle.cpp
tests/integration/test_volume_control.cpp
tests/unit/test_action_bus.cpp
tests/unit/test_ai_config.cpp
tests/unit/test_ai_http_client.cpp
tests/unit/test_ai_panel.cpp
tests/unit/test_ai_screen_context.cpp
tests/unit/test_application_events.cpp
tests/unit/test_application_lifecycle.cpp
tests/unit/test_audio_mixer.cpp
tests/unit/test_capture.cpp
tests/unit/test_cli_parser.cpp
tests/unit/test_clipboard_paste.cpp
tests/unit/test_config_parser.cpp
tests/unit/test_contract_gates.cpp
tests/unit/test_crash_breadcrumb.cpp
tests/unit/test_engine_dispatcher.cpp
tests/unit/test_engine_host_cli.cpp
tests/unit/test_fullscreen_toggle.cpp
tests/unit/test_glide_config.cpp
tests/unit/test_hotkey_dispatcher.cpp
tests/unit/test_input_mapper.cpp
tests/unit/test_ipx_config.cpp
tests/unit/test_joystick_mapper.cpp
tests/unit/test_mapper_ui.cpp
tests/unit/test_menu_bar.cpp
tests/unit/test_menu_system.cpp
tests/unit/test_midi_config.cpp
tests/unit/test_mount_manager.cpp
tests/unit/test_pal_audio_sink.cpp
tests/unit/test_pal_context.cpp
tests/unit/test_pal_host_clock.cpp
tests/unit/test_pal_input_source.cpp
tests/unit/test_pal_platform.cpp
tests/unit/test_pal_sdl2_backend.cpp
tests/unit/test_pal_sdl3_backend.cpp
tests/unit/test_pal_types.cpp
tests/unit/test_pal_window.cpp
tests/unit/test_pause_reset.cpp
tests/unit/test_pc98_config.cpp
tests/unit/test_phase3_bridge.cpp
tests/unit/test_platform_dirs.cpp
tests/unit/test_portable_mode.cpp
tests/unit/test_printer_manager.cpp
tests/unit/test_save_browser.cpp
tests/unit/test_save_manager.cpp
tests/unit/test_scancode_mapping.cpp
tests/unit/test_shader_presets.cpp
tests/unit/test_ttf_renderer.cpp
tests/unit/test_utils/pal_headless_fixture.h
tests/unit/test_utils/temp_file_fixture.h
tests/unit/test_video_capture.cpp
tests/unit/test_zmbv_codec.cpp
```

## Recommendation

Recommended owner decision: choose `GPL-2.0-or-later`.

Rationale: this matches the existing source SPDX majority, avoids narrowing current file-level permissions without author review, and requires only documentation cleanup plus a root `LICENSE` update after the owner decision.

## Required Follow-Up After Owner Decision

- If choosing `GPL-2.0-or-later`: update `README.md`, `CONTRIBUTING.md`, and `LICENSE`; do not rewrite existing source SPDX markers.
- If choosing `GPL-2.0-only`: update the 201 SPDX-marker files listed above, update `DEPENDENCIES.md`, and update `LICENSE`; obtain explicit owner/legal confirmation before narrowing any file-level marker.

This brief does not apply either option.
