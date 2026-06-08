# OpenSpec RuntimeHost App Service Adoption QA Report

This report summarizes the verification results for the `runtimehost-app-service-adoption` sprint, reducing direct application-layer FFI bypasses to exactly 2.

## OpenSpec Change Path
`openspec/changes/runtimehost-app-service-adoption/`

## Gate Status Table

| Gate | Name | Status | Notes |
| :--- | :--- | :---: | :--- |
| **Gate 1** | OpenSpec Design | **PASS** | Change validated with `--strict --json` under `openspec.cmd`. |
| **Gate 2** | RuntimeHost Service Surface | **PASS** | 16 new virtual methods added to `RuntimeHost` and overridden in subclasses. |
| **Gate 3** | Application Routing | **PASS** | Routed all 31 configuration, handler, and event FFI bypasses in `application.cpp` through `runtime_`. |
| **Gate 4** | AI Context Routing | **PASS** | Converted `captureScreenContext` to `RuntimeHost`-backed path in `ai_screen_context.cpp`. |
| **Gate 5** | Graphify Enforcement | **PASS** | Graphify overlay updated; direct app bypasses reduced to exactly 2. |
| **Gate 6** | Verification | **PASS** | Compilation successful, C ABI tests, Unit tests, and whitespace checks all passed. |

## Before/After Graphify Metrics

| Metric | Before Sprint | After Sprint | Change |
| :--- | :---: | :---: | :---: |
| **RuntimeHost Virtual Methods** | 16 | 32 | +16 |
| **App Direct RuntimeHost Bypasses** | 35 | 2 | -33 |
| **Allowlisted Bypasses** | 35 | 2 | -33 |
| **App Calls to RuntimeHost** | 18 | 51 | +33 |

## Files Changed
- [include/legends/runtime_host.h](file:///C:/Users/charl/ProjectLegends/include/legends/runtime_host.h)
- [src/app/runtime_host.cpp](file:///C:/Users/charl/ProjectLegends/src/app/runtime_host.cpp)
- [src/app/application.cpp](file:///C:/Users/charl/ProjectLegends/src/app/application.cpp)
- [src/app/ai_screen_context.h](file:///C:/Users/charl/ProjectLegends/src/app/ai_screen_context.h)
- [src/app/ai_screen_context.cpp](file:///C:/Users/charl/ProjectLegends/src/app/ai_screen_context.cpp)
- [tests/unit/test_ai_screen_context.cpp](file:///C:/Users/charl/ProjectLegends/tests/unit/test_ai_screen_context.cpp)
- [docs/architecture/runtimehost-bypass-allowlist.json](file:///C:/Users/charl/ProjectLegends/docs/architecture/runtimehost-bypass-allowlist.json)
- [openspec/changes/runtimehost-app-service-adoption/tasks.md](file:///C:/Users/charl/ProjectLegends/openspec/changes/runtimehost-app-service-adoption/tasks.md)

## Commands Passed
1. `openspec.cmd validate runtimehost-app-service-adoption --strict --json`
2. `cmake --preset dev`
3. `cmake --build --preset dev`
4. `build/dev/legends_abi_test.exe`
5. `build/dev/legends_unit_tests.exe`
6. `python scripts/check_capability_matrix.py --repo .`
7. `python scripts/check_conflict_markers.py --path .`
8. `python scripts/graphify_projectlegends.py update --repo . --source-only`
9. `python scripts/graphify_projectlegends.py runtimehost-bypasses --repo .`
10. `python scripts/check_graphify_enrichment.py --repo . --overlay graphify-out/projectlegends-enrichment.json --strict --strict-tests fail --allow-missing-graphify`
11. `git diff --check`

## Commands Failed Or Blocked
- None (all checks, compilations, and tests passed).

## Remaining Direct Bypasses
Only the two lifecycle exceptions remain:
1. `legends_create` inside `Application::init` (`src/app/application.cpp`)
2. `legends_destroy` inside `Application::shutdown` (`src/app/application.cpp`)

## Top Five Codex Audit Targets
1. **Subclass Method Completeness**: Confirm that both `InProcessEngineRuntime` and `IpcEngineRuntime` correctly delegate the 16 new virtual methods to their underlying FFI functions.
2. **AI Screen Context Transitional Overload**: Audit `captureScreenContext(legends_handle, ...)` to ensure it safely delegates through a stack-instantiated `InProcessEngineRuntime` with `own_handle = false`.
3. **Application Routing Scope**: Ensure no other `legends_*` calls were left behind or added to `src/app/application.cpp` besides the lifecycle calls.
4. **Allowlist Integrity**: Verify that `docs/architecture/runtimehost-bypass-allowlist.json` strictly lists only `legends_create` and `legends_destroy`.
5. **Lifecycle / Resource Safety**: Verify that the creation, override, and deletion of `runtime_` does not cause leaks or affect engine lifecycle semantics.
