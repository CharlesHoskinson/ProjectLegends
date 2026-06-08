# RuntimeHost V2 Adoption Handoff Report

## 1. QA Artifact Path
`docs/superpowers/reviews/2026-06-08-gemini-35-flash-runtimehost-adoption-qa.md`

## 2. Gate Status Table

| Gate | Name | Status | Summary of Work Completed |
| :--- | :--- | :--- | :--- |
| **Gate 1** | Build Integrity | **PASS** | Recompiled all targets successfully under the `dev` preset on Windows (MSVC/Clang). |
| **Gate 2** | RuntimeHost Extension | **PASS** | Extended `RuntimeHost` interface and concrete implementations (`InProcessEngineRuntime` and `IpcEngineRuntime`) with 5 new methods (`get_total_cycles`, `is_frame_dirty`, `inject_key_ext`, `capture_audio`, and `capture_midi_audio`). Stored and respected the `own_handle_` flag in subclass constructors and destructors to control engine lifetime ownership correctly. |
| **Gate 3** | Application Integration | **PASS** | Integrated `std::unique_ptr<RuntimeHost> runtime_` in [application.h](file:///C:/Users/charl/ProjectLegends/src/app/application.h). Instantiated it in borrowed mode (`own_handle = false`) during `Application::init` and cleared it safely in `Application::shutdown` before the raw handle is destroyed. Re-routed 15 hot-path bypass calls inside `Application::run`, `processEvents`, `renderFrame`, and `pumpAudio` to use the `runtime_` abstraction. |
| **Gate 4** | Allowlist & Graphify Validation | **PASS** | Removed 15 retired application bypass entries from [runtimehost-bypass-allowlist.json](file:///C:/Users/charl/ProjectLegends/docs/architecture/runtimehost-bypass-allowlist.json). Ran a full Graphify AST update, reducing the bypass count from 53 to 38 (below the target threshold of 39). All automated strict validation checks passed with zero errors and zero warnings. |
| **Gate 5** | ABI & Unit Test Verification | **PASS** | Both `legends_abi_test.exe` and `legends_unit_tests.exe` executed. 100% of ABI tests passed, and all 2677 unit tests passed cleanly (with 18 skipped and 0 failures). |

## 3. Files Changed

- [include/legends/runtime_host.h](file:///C:/Users/charl/ProjectLegends/include/legends/runtime_host.h)
- [src/app/runtime_host.cpp](file:///C:/Users/charl/ProjectLegends/src/app/runtime_host.cpp)
- [src/app/application.h](file:///C:/Users/charl/ProjectLegends/src/app/application.h)
- [src/app/application.cpp](file:///C:/Users/charl/ProjectLegends/src/app/application.cpp)
- [docs/architecture/runtimehost-bypass-allowlist.json](file:///C:/Users/charl/ProjectLegends/docs/architecture/runtimehost-bypass-allowlist.json)
- [docs/architecture/graphify-enrichment-report.md](file:///C:/Users/charl/ProjectLegends/docs/architecture/graphify-enrichment-report.md)
- [graphify-out/projectlegends-enrichment.json](file:///C:/Users/charl/ProjectLegends/graphify-out/projectlegends-enrichment.json)
- [docs/superpowers/reviews/2026-06-08-gemini-35-flash-runtimehost-adoption-qa.md](file:///C:/Users/charl/ProjectLegends/docs/superpowers/reviews/2026-06-08-gemini-35-flash-runtimehost-adoption-qa.md)

## 4. RuntimeHost Architecture & Verification Changes

- **Method Extensions**: Added 5 methods mapping to key capabilities:
  - `get_total_cycles(uint64_t* cycles_out)`
  - `is_frame_dirty(int* dirty_out)`
  - `inject_key_ext(uint8_t scancode, bool is_down)`
  - `capture_audio(int16_t* buffer, size_t buffer_count, size_t* count_out)`
  - `capture_midi_audio(int16_t* buffer, size_t buffer_count, size_t* count_out)`
- **Ownership Lifetime Guard**: Subclass constructors were parameterized with `bool own_handle = true` (defaulting to true for standard FFI use cases). When `Application::init` constructs the runtime using the application-managed engine handle, it passes `own_handle = false` to guarantee the engine handle is not double-freed during application teardown.
- **Application Injection**: Replaced raw FFI `legends_*` calls inside `Application::run`, `Application::processEvents`, `Application::renderFrame`, and `Application::pumpAudio` with matching wrapper calls on `runtime_`.
- **Bypasses Reduction**: Reduced active application-level bypasses down to 38, fully satisfying the target of 39 or fewer.

## 5. Commands Passed

- `cmake --build --preset dev` - Rebuilt successfully; no remaining compiler/linker actions.
- `build/dev/legends_abi_test.exe` - Passed 100% of pure C ABI constraints.
- `build/dev/legends_unit_tests.exe` - Successfully ran all unit tests: 2677 passed, 18 skipped, 0 failed.
- `python scripts/graphify_projectlegends.py update --repo .` - Refreshed AST extraction and rebuilt the JSON metadata overlay.
- `python scripts/check_graphify_enrichment.py --repo . --overlay graphify-out/projectlegends-enrichment.json --strict --strict-tests fail --allow-missing-graphify` - Successfully verified consistency and passed with zero errors or warnings.
- `python scripts/graphify_projectlegends.py runtimehost-bypasses --repo .` - Verified that only 38 active bypasses remain.

## 6. Commands Failed Or Blocked

- None. All validation and build commands executed and completed successfully.

## 7. Top Five Items Codex Should Audit First

1. **Borrower Semantics and Engine Destruction**: Verify `Application::init` constructs `InProcessEngineRuntime` or `IpcEngineRuntime` using `own_handle = false` (preventing double-destruct on `engine_` when `runtime_` is reset in `Application::shutdown`).
2. **New RuntimeHost Implementations**: Review [runtime_host.cpp](file:///C:/Users/charl/ProjectLegends/src/app/runtime_host.cpp) to audit delegation calls to FFI.
3. **Application Call Routing**: Review [application.cpp](file:///C:/Users/charl/ProjectLegends/src/app/application.cpp) diff to confirm the 15 direct FFI calls have been replaced with their respective `runtime_` wrappers.
4. **Allowlist Integrity**: Review the updated [runtimehost-bypass-allowlist.json](file:///C:/Users/charl/ProjectLegends/docs/architecture/runtimehost-bypass-allowlist.json) to verify all 15 retired items have been removed cleanly.
5. **Graphify Validation Overlay**: Audit [projectlegends-enrichment.json](file:///C:/Users/charl/ProjectLegends/graphify-out/projectlegends-enrichment.json) to confirm the new `RuntimeHost` node linkages are correctly updated.
