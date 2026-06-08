# OpenSpec QA Review: RuntimeHost V2 Adoption Handoff

This QA review documents the implementation of the next RuntimeHost adoption slice using the OpenSpec design workflow.

---

## 1. OpenSpec Change Path
`openspec/changes/runtimehost-adoption-next-slice`

---

## 2. OpenSpec Artifacts Created or Modified

- `openspec/changes/runtimehost-adoption-next-slice/.openspec.yaml` (New configuration)
- `openspec/changes/runtimehost-adoption-next-slice/proposal.md` (New proposal detailing why, bypass debt, changes, scope, and audit strategy)
- `openspec/changes/runtimehost-adoption-next-slice/design.md` (New design covering owned/borrowed handles, interface additions, teardown order, and allowlist policy)
- `openspec/changes/runtimehost-adoption-next-slice/tasks.md` (New checklist tracking implementation steps as completed)
- `openspec/changes/runtimehost-adoption-next-slice/specs/runtimehost-adoption/spec.md` (New delta spec outlining requirements and scenarios)

---

## 3. OpenSpec Validation Result
`PASS`
The new change `runtimehost-adoption-next-slice` validates cleanly under strict checks:
`1 change validated, 1 passed, 0 failed, 0 issues.`

---

## 4. Gate Status Table

| Gate | Name | Status | Summary of Work Completed |
| :--- | :--- | :--- | :--- |
| **Gate 1** | OpenSpec Design Alignment | **PASS** | Codex audit correction formalized the implemented sprint requirements, proposal, design, tasks, and delta specs into the OpenSpec change directory. |
| **Gate 2** | RuntimeHost Interface Extension | **PASS** | Added `get_total_cycles`, `is_frame_dirty`, `inject_key_ext`, `capture_audio`, and `capture_midi_audio` virtual methods. Stored/checked `own_handle_` flag in subclass constructors/destructors to control FFI lifetime. |
| **Gate 3** | Application Integration | **PASS** | Integrated borrowed `runtime_` pointer (`own_handle = false`) inside `Application` shell, routing all 15 event, step, frame capture, and audio pump FFI bypass calls to `runtime_`. |
| **Gate 4** | Allowlist Cleanup & Graphify Sync | **PASS** | Retired 15 entries from `runtimehost-bypass-allowlist.json`. Ran the source-only ProjectLegends Graphify overlay refresh and verified that the bypass count dropped to 38. Strict Graphify validation checks passed. |
| **Gate 5** | Test Verification | **PASS** | Both `legends_abi_test.exe` and `legends_unit_tests.exe` executed. 100% ABI and 2677 unit tests passed cleanly with no regressions. |

---

## 5. Files Changed

- [include/legends/runtime_host.h](file:///C:/Users/charl/ProjectLegends/include/legends/runtime_host.h)
- [src/app/runtime_host.cpp](file:///C:/Users/charl/ProjectLegends/src/app/runtime_host.cpp)
- [src/app/application.h](file:///C:/Users/charl/ProjectLegends/src/app/application.h)
- [src/app/application.cpp](file:///C:/Users/charl/ProjectLegends/src/app/application.cpp)
- [docs/architecture/runtimehost-bypass-allowlist.json](file:///C:/Users/charl/ProjectLegends/docs/architecture/runtimehost-bypass-allowlist.json)
- [docs/architecture/graphify-enrichment-report.md](file:///C:/Users/charl/ProjectLegends/docs/architecture/graphify-enrichment-report.md)
- [graphify-out/projectlegends-enrichment.json](file:///C:/Users/charl/ProjectLegends/graphify-out/projectlegends-enrichment.json)
- [docs/superpowers/reviews/2026-06-08-gemini-35-flash-openspec-runtimehost-adoption-qa.md](file:///C:/Users/charl/ProjectLegends/docs/superpowers/reviews/2026-06-08-gemini-35-flash-openspec-runtimehost-adoption-qa.md)

---

## 6. Before/After Graphify Metrics

| Metric | Before Sprint | After Sprint | Delta |
| :--- | :---: | :---: | :---: |
| **RuntimeHost Methods** | 11 | 16 | +5 |
| **App Direct Bypasses** | 53 | 38 | -15 |
| **Allowlisted Bypasses** | 53 | 38 | -15 |
| **App Calls to RuntimeHost** | 0 | 15 | +15 |

---

## 7. RuntimeHost Methods Added or Used

- `get_total_cycles(uint64_t* cycles_out)`
- `is_frame_dirty(int* dirty_out)`
- `inject_key_ext(uint8_t scancode, bool is_down)`
- `capture_audio(int16_t* buffer, size_t buffer_count, size_t* count_out)`
- `capture_midi_audio(int16_t* buffer, size_t buffer_count, size_t* count_out)`

---

## 8. App-layer legends_* Bypasses Removed

- `legends_step_ms` (1 call in `Application::run`)
- `legends_get_total_cycles` (1 call in `Application::run`)
- `legends_key_event` (1 call in `Application::processEvents`)
- `legends_key_event_ext` (1 call in `Application::processEvents`)
- `legends_mouse_event` (2 calls in `Application::processEvents`)
- `legends_is_frame_dirty` (1 call in `Application::renderFrame`)
- `legends_capture_rgb` (2 calls in `Application::renderFrame`)
- `legends_capture_text` (2 calls in `Application::renderFrame`)
- `legends_capture_audio` (2 calls in `Application::pumpAudio`)
- `legends_capture_midi_audio` (2 calls in `Application::pumpAudio`)

---

## 9. Allowlist Keys Removed

- `src/app/application.cpp|Application::renderFrame|legends_is_frame_dirty|legends_is_frame_dirty(engine_, &dirty);|0`
- `src/app/application.cpp|Application::renderFrame|legends_capture_rgb|legends_capture_rgb(engine_, nullptr, 0, &size_needed, &fw, &fh);|0`
- `src/app/application.cpp|Application::renderFrame|legends_capture_rgb|legends_capture_rgb(engine_, rgb_buffer_.data(),|0`
- `src/app/application.cpp|Application::renderFrame|legends_capture_text|legends_capture_text(engine_, nullptr, 0, &cell_count, &tinfo);|0`
- `src/app/application.cpp|Application::renderFrame|legends_capture_text|legends_capture_text(engine_, cells.data(), cells.size(),|0`
- `src/app/application.cpp|Application::pumpAudio|legends_capture_audio|legends_capture_audio(engine_, nullptr, 0, &avail);|0`
- `src/app/application.cpp|Application::pumpAudio|legends_capture_audio|legends_capture_audio(engine_, audio_buffer_.data(), audio_buffer_.size(), &actual);|0`
- `src/app/application.cpp|Application::pumpAudio|legends_capture_midi_audio|legends_capture_midi_audio(engine_, nullptr, 0, &midi_avail);|0`
- `src/app/application.cpp|Application::pumpAudio|legends_capture_midi_audio|legends_capture_midi_audio(engine_, midi_buf.data(), midi_buf.size(), &midi_actual);|0`
- `src/app/application.cpp|Application::run|legends_step_ms|legends_error_t step_err = legends_step_ms(engine_, 16, &step_result);|0`
- `src/app/application.cpp|Application::run|legends_get_total_cycles|legends_get_total_cycles(engine_, &total_cycles);|0`
- `src/app/application.cpp|Application::processEvents|legends_key_event_ext|legends_key_event_ext(engine_, at.code, down ? 1 : 0);|0`
- `src/app/application.cpp|Application::processEvents|legends_key_event|legends_key_event(engine_, at.code, down ? 1 : 0);|0`
- `src/app/application.cpp|Application::processEvents|legends_mouse_event|legends_mouse_event(engine_,|0`
- `src/app/application.cpp|Application::processEvents|legends_mouse_event|legends_mouse_event(engine_, 0, 0, buttons);|0`

---

## 10. Remaining Bypass Categories

The remaining 38 direct FFI bypasses fall into:
- **Lifecycle & Setup**: `legends_create`, `legends_destroy` (2 calls)
- **Logging Callback Configuration**: `legends_set_log_callback` (2 calls)
- **Emulation Config (Drives, Graphics, MIDI, Machine Type)**: `legends_mount_drive`, `legends_midi_set_device`, `legends_midi_set_soundfont`, `legends_midi_set_romdir`, `legends_printer_set_output`, `legends_set_ttf_font`, `legends_ipx_enable`, `legends_ipx_connect`, `legends_glide_enable`, `legends_glide_set_resolution`, `legends_set_machine_pc98` (15 calls in init, 10 calls in action registration handlers)
- **Joystick Input Events**: `legends_joystick_event` (2 calls in `Application::processEvents`)
- **State Save/Load slots**: `legends_save_state`, `legends_load_state` (3 calls in `SaveManager`)
- **AI Screen Context**: `legends_capture_text` (2 calls in `ai_screen_context.cpp`)

---

## 11. Commands Passed

- `openspec list --json`
- `openspec status --change runtimehost-adoption-next-slice --json`
- `openspec validate runtimehost-adoption-next-slice --strict --json`
- `openspec show runtimehost-adoption-next-slice --json`
- `cmake --preset dev`
- `cmake --build --preset dev`
- `build/dev/legends_abi_test.exe`
- `build/dev/legends_unit_tests.exe`
- `python scripts/check_capability_matrix.py --repo .`
- `python scripts/check_conflict_markers.py --path .`
- `python scripts/graphify_projectlegends.py update --repo . --source-only`
- `python scripts/graphify_projectlegends.py runtimehost-bypasses --repo .`
- `python scripts/check_graphify_enrichment.py --repo . --overlay graphify-out/projectlegends-enrichment.json --strict --strict-tests fail --allow-missing-graphify`
- `git diff --check`

---

## 12. Commands Failed Or Blocked

- `openspec validate --all --strict --json`: Failed due to unrelated, incomplete delta requirements on the pre-existing change `phase-iso-process-isolation`.

---

## 13. Top Five Codex Audit Targets

1. **Borrower Lifetime Ordering**: Audit `Application::init` instantiation of `runtime_` with `own_handle = false` and its deletion via `.reset()` in `Application::shutdown` preceding raw engine FFI cleanup.
2. **Subclass Constructor Updates**: Audit [runtime_host.h](file:///C:/Users/charl/ProjectLegends/include/legends/runtime_host.h) and [runtime_host.cpp](file:///C:/Users/charl/ProjectLegends/src/app/runtime_host.cpp) virtual overrides for the 5 new methods.
3. **Event Loop & Pump Routing**: Audit the 15 call-sites replaced within [application.cpp](file:///C:/Users/charl/ProjectLegends/src/app/application.cpp) event pumps.
4. **OpenSpec Spec Compliance**: Audit `openspec/changes/runtimehost-adoption-next-slice/specs/runtimehost-adoption/spec.md` requirements to ensure correctness.
5. **Bypass Reduction & Graphify Report**: Verify that active bypasses are strictly validated as 38 by Graphify checks.
