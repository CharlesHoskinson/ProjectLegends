# OpenSpec QA Review: SaveManager RuntimeHost Adoption Handoff

This QA review documents the implementation of the SaveManager RuntimeHost adoption slice using the OpenSpec design workflow.

---

## 1. OpenSpec Change Path
`openspec/changes/runtimehost-savemanager-adoption`

---

## 2. OpenSpec Validation Result
`PASS`
The change `runtimehost-savemanager-adoption` validates cleanly under strict checks:
`1 change validated, 1 passed, 0 failed, 0 issues.`

---

## 3. Gate Status Table

| Gate | Name | Status | Summary of Work Completed |
| :--- | :--- | :--- | :--- |
| **Gate 1** | OpenSpec Design | **PASS** | Created the OpenSpec change directory and validated the design using `openspec validate` before implementation. |
| **Gate 2** | Baseline Graphify | **PASS** | Captured baseline metrics using `graphify_projectlegends.py runtimehost-bypasses --repo .`, verifying 38 app direct bypasses. |
| **Gate 3** | SaveManager Migration | **PASS** | Routed state saving, loading, and crash recovery methods of `SaveManager` to delegate to `RuntimeHost` methods instead of direct `legends_save_state`/`legends_load_state` calls. Re-routed FFI raw handle overloads to construct borrowed `InProcessEngineRuntime` and delegate, while preserving autosave slot 0 as valid storage. |
| **Gate 4** | Graphify Evidence | **PASS** | Refreshed the source-only Graphify overlay and verified that direct bypasses decreased to **35**. Strict Graphify overlay verification checks passed. |
| **Gate 5** | Verification | **PASS** | ABI and unit tests compiled and executed cleanly, with all 2678 unit tests passing with zero failures. Conflict marker checks and capability matrix checks passed. |

---

## 4. Files Changed

- [src/app/save_manager.h](file:///C:/Users/charl/ProjectLegends/src/app/save_manager.h)
- [src/app/save_manager.cpp](file:///C:/Users/charl/ProjectLegends/src/app/save_manager.cpp)
- [src/app/application.cpp](file:///C:/Users/charl/ProjectLegends/src/app/application.cpp)
- [tests/unit/test_save_manager.cpp](file:///C:/Users/charl/ProjectLegends/tests/unit/test_save_manager.cpp)
- [docs/architecture/runtimehost-bypass-allowlist.json](file:///C:/Users/charl/ProjectLegends/docs/architecture/runtimehost-bypass-allowlist.json)
- [docs/architecture/graphify-enrichment-report.md](file:///C:/Users/charl/ProjectLegends/docs/architecture/graphify-enrichment-report.md)
- [graphify-out/projectlegends-enrichment.json](file:///C:/Users/charl/ProjectLegends/graphify-out/projectlegends-enrichment.json)
- [docs/superpowers/reviews/2026-06-08-gemini-35-flash-openspec-savemanager-runtimehost-qa.md](file:///C:/Users/charl/ProjectLegends/docs/superpowers/reviews/2026-06-08-gemini-35-flash-openspec-savemanager-runtimehost-qa.md)

---

## 5. Before/After Graphify Metrics

| Metric | Before Sprint | After Sprint | Delta |
| :--- | :---: | :---: | :---: |
| **RuntimeHost Methods** | 16 | 16 | 0 |
| **App Direct Bypasses** | 38 | 35 | -3 |
| **Allowlisted Bypasses** | 38 | 35 | -3 |
| **App Calls to RuntimeHost** | 15 | 18 | +3 |

---

## 6. SaveManager Call Sites Migrated

- `SaveManager::saveToSlot` (two calls: size query and state buffer fill)
- `SaveManager::loadFromSlot` (one call: state payload load)
- `SaveManager::recoverAutosave` (delegates through the `RuntimeHost&` load path while retaining autosave slot 0)

---

## 7. Allowlist Keys Removed

- `src/app/save_manager.cpp|SaveManager::saveToSlot|legends_save_state|auto err = legends_save_state(engine, nullptr, 0, &state_size);|0`
- `src/app/save_manager.cpp|SaveManager::saveToSlot|legends_save_state|err = legends_save_state(engine, state_buf.data(), state_buf.size(), &state_size);|0`
- `src/app/save_manager.cpp|SaveManager::loadFromSlot|legends_load_state|auto err = legends_load_state(engine, payload, header.payload_size);|0`

---

## 8. Remaining Bypass Categories

The remaining 35 direct FFI bypasses fall into:
- **AI screen context**: `legends_capture_text` (2 calls)
- **Application init/setup**: create, logging, mount, MIDI, printer, TTF, IPX, Glide, and PC-98 configuration (14 calls)
- **Application shutdown lifecycle**: `legends_destroy` (1 call)
- **Joystick input events**: `legends_joystick_event` (2 calls)
- **Action handlers**: cursor/text capture, MIDI/printer/IPX/Glide/PC-98 config, reset, screenshot capture, and text input (16 calls)

---

## 9. Commands Passed

- `openspec validate runtimehost-savemanager-adoption --strict --json`
- `openspec show runtimehost-savemanager-adoption --json`
- `cmake --preset dev`
- `cmake --build --preset dev`
- `build/dev/legends_unit_tests.exe --gtest_filter=SaveManagerTest.*` (21 passed)
- `build/dev/legends_abi_test.exe`
- `build/dev/legends_unit_tests.exe` (2678 passed, 18 skipped, 0 failed)
- `python scripts/check_capability_matrix.py --repo .`
- `python scripts/check_conflict_markers.py --path .`
- `python scripts/graphify_projectlegends.py update --repo . --source-only`
- `python scripts/graphify_projectlegends.py runtimehost-bypasses --repo .`
- `python scripts/check_graphify_enrichment.py --repo . --overlay graphify-out/projectlegends-enrichment.json --strict --strict-tests fail --allow-missing-graphify`
- `git diff --check`

---

## 10. Commands Failed Or Blocked

- None. All validation and build commands completed successfully.

---

## 11. Top Five Codex Audit Targets

1. **SaveManager Overloads**: Audit the new overloads in [save_manager.h](file:///C:/Users/charl/ProjectLegends/src/app/save_manager.h) and [save_manager.cpp](file:///C:/Users/charl/ProjectLegends/src/app/save_manager.cpp) to verify that `RuntimeHost&` references are utilized without taking ownership of the runtime's lifetime.
2. **Transitional Raw Handle Overloads**: Verify that the transitional `legends_handle` overloads correctly wrap the handle in `InProcessEngineRuntime` with `own_handle = false` to guarantee no double-free of raw emulation handles.
3. **Application Call Sites Integration**: Review call site changes in [application.cpp](file:///C:/Users/charl/ProjectLegends/src/app/application.cpp) (recovery check in `init()` and slot handlers in `registerActionHandlers()`) to confirm they invoke the new `RuntimeHost`-backed paths.
4. **Allowlist Cleanup Consistency**: Verify that the three retired `SaveManager` keys are correctly removed from the allowlist, and that the remaining 35 keys match observed FFI calls.
5. **OpenSpec Change Integrity**: Review the OpenSpec specs, proposal, and tasks at `openspec/changes/runtimehost-savemanager-adoption` to ensure strict specification formatting.
