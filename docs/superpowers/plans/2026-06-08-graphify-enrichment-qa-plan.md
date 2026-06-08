# Graphify Enrichment And QA Plan: ProjectLegends

## Goal

Build a ProjectLegends-specific enrichment layer over Graphify's AST graph that answers:

```text
public C API -> capability manifest -> proxy MsgType -> dispatcher case -> tests -> CMake targets
```

The enrichment must not mutate `graphify-out/graph.json` in place. Graphify's original nodes and links remain vendor-generated evidence. ProjectLegends enrichment is derived evidence with its own origin, schema, generator, checker, and QA artifact.

## Integration Model

Inputs:

* `graphify-out/graph.json`
* `include/legends/legends_embed.h`
* `src/legends/legends_embed_api.cpp`
* `src/legends_proxy/proxy_api.cpp`
* `src/engine_host/engine_dispatcher.cpp`
* `include/legends_ipc/message_types.h`
* `include/legends_ipc/messages.h`
* `docs/architecture/capability_truth.json`
* `docs/architecture/2026-06-08-public-capability-truth-matrix.md`
* `tests/**/*.cpp`
* `CMakeLists.txt`
* `CMakePresets.json`
* `build/dev/compile_commands.json`
* `build/ipc/compile_commands.json`, when available

Generated outputs:

* `graphify-out/projectlegends-enrichment.json`
* `graphify-out/projectlegends-graph-enriched.json`
* `docs/superpowers/reviews/2026-06-08-graphify-enrichment-qa.md`

Rules:

* Never rewrite `graphify-out/graph.json`.
* Preserve every original Graphify link with `confidence: "EXTRACTED"`.
* Every enrichment node has `_origin: "projectlegends-enrichment"`.
* Every enrichment link has `confidence: "DERIVED"`.
* Enrichment node IDs use a collision-resistant prefix: `pl__<kind>__<stable_name>`.
* The merged graph is disposable and reproducible from the original graph plus the sidecar.

## Enrichment Node Kinds

### API And Capability

`public_c_api`

* ID: `pl__api__legends_create`
* Source: `include/legends/legends_embed.h`
* Required fields: `name`, `kind`, `source_file`, `source_location`, `signature`

`capability_entry`

* ID: `pl__capability__legends_create`
* Source: `docs/architecture/capability_truth.json`
* Required fields: `api`, `direct_status`, `proxy_status`, `notes`, `evidence_files`

`capability_matrix_row`

* ID: `pl__matrix_row__legends_create`
* Source: `docs/architecture/2026-06-08-public-capability-truth-matrix.md`
* Required fields: `api`, `direct_status`, `proxy_status`

### Implementations

`direct_c_api_impl`

* ID: `pl__direct_impl__legends_create`
* Source: `src/legends/legends_embed_api.cpp`
* Required fields: `api`, `source_location`, `body_hash`

`proxy_c_api_impl`

* ID: `pl__proxy_impl__legends_create`
* Source: `src/legends_proxy/proxy_api.cpp`
* Required fields: `api`, `source_location`, `body_hash`, `returns_not_supported`

### IPC

`ipc_msgtype`

* ID: `pl__msgtype__CreateReq`
* Source: `include/legends_ipc/message_types.h`
* Required fields: `name`, `numeric_value`, `category`, `direction`
* `direction` values: `request`, `response`, `control`, `event`, `unknown`

`ipc_message_struct`

* ID: `pl__msgstruct__CreateReq`
* Source: `include/legends_ipc/messages.h`
* Required fields: `name`, `msgtype`, `serialized_size`, `fields`

`dispatcher_case`

* ID: `pl__dispatcher_case__CreateReq`
* Source: `src/engine_host/engine_dispatcher.cpp`
* Required fields: `msgtype`, `source_location`, `called_apis`, `response_msgtype`

### Tests

`test_file`

* ID: `pl__test_file__tests_integration_test_ipc_integration_cpp`
* Source: `tests/**/*.cpp`
* Required fields: `path`, `test_target`

`test_case`

* ID: `pl__test_case__IpcIntegrationTest_FullE2E`
* Source: `tests/**/*.cpp`
* Required fields: `suite`, `name`, `disabled`, `source_file`, `source_location`

### Build System

`cmake_target`

* ID: `pl__cmake_target__legends_proxy`
* Source: `CMakeLists.txt`
* Required fields: `name`, `target_type`, `source_location`, `conditions`

`cmake_source`

* ID: `pl__cmake_source__src_legends_proxy_proxy_api_cpp`
* Source: source path or generated CMake expansion
* Required fields: `path`

`cmake_preset`

* ID: `pl__cmake_preset__dev`
* Source: `CMakePresets.json`
* Required fields: `name`, `binary_dir`, `cache_variables`

## Enrichment Edge Kinds

API/capability edges:

* `has_capability_entry`: `public_c_api -> capability_entry`
* `has_matrix_row`: `public_c_api -> capability_matrix_row`
* `direct_implemented_by`: `public_c_api -> direct_c_api_impl`
* `proxy_implemented_by`: `public_c_api -> proxy_c_api_impl`
* `claims_evidence_file`: `capability_entry -> cmake_source`

Proxy/IPC edges:

* `sends_request`: `proxy_c_api_impl -> ipc_msgtype`
* `aliases_api`: `proxy_c_api_impl -> public_c_api`
* `paired_with_response`: `ipc_msgtype(request) -> ipc_msgtype(response)`
* `typed_by_struct`: `ipc_msgtype -> ipc_message_struct`
* `handled_by_dispatcher`: `ipc_msgtype -> dispatcher_case`
* `dispatcher_returns`: `dispatcher_case -> ipc_msgtype(response)`
* `dispatch_calls_api`: `dispatcher_case -> public_c_api`

Test edges:

* `contains_test_case`: `test_file -> test_case`
* `covers_api_call`: `test_case -> public_c_api`
* `covers_msgtype`: `test_case -> ipc_msgtype`
* `exercises_dispatcher_case`: `test_case -> dispatcher_case`, derived only when a test references a handled `MsgType`

CMake edges:

* `configured_by_preset`: `cmake_target -> cmake_preset`
* `includes_source`: `cmake_target -> cmake_source`
* `links_target`: `cmake_target -> cmake_target`
* `builds_api_impl`: `cmake_target -> direct_c_api_impl`
* `builds_proxy_impl`: `cmake_target -> proxy_c_api_impl`
* `builds_dispatcher`: `cmake_target -> dispatcher_case`
* `builds_test_file`: `cmake_target -> test_file`

## Extraction Rules

### Public C APIs

Reuse the existing rule from `scripts/check_capability_matrix.py`:

```text
\bLEGENDS_API\s+legends_error_t\s+(legends_[a-z0-9_]+)\s*\(
```

Fallback to scanning after each `LEGENDS_API` token for split declarations. Every parsed API must become exactly one `public_c_api` node.

### Direct And Proxy Bodies

Reuse the current brace-matching function parser from `scripts/check_capability_matrix.py`.

For each API:

* direct implementation must resolve from `src/legends/legends_embed_api.cpp`
* proxy implementation must resolve from `src/legends_proxy/proxy_api.cpp`
* store a stable `body_hash` so diffs can explain graph changes
* mark `returns_not_supported` when the body contains `return LEGENDS_ERR_NOT_SUPPORTED;`

### Proxy Request Mapping

Extract request names from proxy bodies with:

* `MsgType::([A-Za-z0-9_]+)`
* `PROXY_REQUEST\(\s*([A-Za-z0-9_]+)`
* `PROXY_EMPTY_REQUEST\(\s*([A-Za-z0-9_]+)`

For macro matches, convert `CreateReq` to `MsgType::CreateReq`. Each match creates `sends_request`.

If a proxy body calls another `legends_*` API directly, create `aliases_api`. This is required for `legends_key_event_ext -> legends_key_event` and similar compatibility aliases.

### MsgType And Message Structs

Parse `enum class MsgType : uint16_t` from `include/legends_ipc/message_types.h`.

* Preserve numeric values.
* Infer request/response pairs by replacing `Req` with `Resp`.
* Infer direction from suffix and control/event exceptions.
* Preserve section comments as `category` when available.

Parse `include/legends_ipc/messages.h` for structs containing:

```text
static constexpr MsgType type = MsgType::<Name>;
```

Create `typed_by_struct` from the enum member to the struct.

### Dispatcher Cases

Parse `src/engine_host/engine_dispatcher.cpp` switch cases:

```text
case MsgType::<Name>:
```

For each case body:

* extract direct `legends_*` calls
* extract returned response `MsgType::*`
* create `handled_by_dispatcher`, `dispatch_calls_api`, and `dispatcher_returns`

The parser should fail closed if a case body cannot be bounded.

### Tests

Parse `TEST(...)` and `TEST_F(...)` macros in `tests/**/*.cpp`.

For each test body:

* `legends_*` mentions create `covers_api_call`
* `MsgType::*` mentions create `covers_msgtype`
* disabled names beginning with `DISABLED_` set `disabled: true`
* `exercises_dispatcher_case` is derived only through an existing `covers_msgtype -> handled_by_dispatcher` path

This is static coverage evidence, not proof that the test executed. Runtime pass/fail stays in the QA artifact.

### CMake Targets

Phase 1 should parse top-level `CMakeLists.txt` for:

* `add_library`
* `add_executable`
* `target_sources`
* `target_link_libraries`
* source-list variables used by ProjectLegends targets

Phase 2 should supplement this with CMake File API or `build/*/compile_commands.json` to reduce regex fragility.

Mandatory targets:

* `legends_core`
* `legends_ipc`
* `legends_proxy`
* `legends_engine_host`
* `legends_app`
* `legends_unit_tests`
* `legends_ipc_integration_tests`
* `legends_abi_test`
* `project_legends`

## QA Layer

Implement:

```powershell
python scripts/enrich_graphify_projectlegends.py --repo . --check
python scripts/check_graphify_enrichment.py --repo .
```

The builder creates the sidecar and merged graph. The checker validates the sidecar, the merged graph, and the extraction invariants.

### Gate 1: Schema And Preservation

Fail if:

* generated JSON is invalid
* node IDs are duplicated
* link endpoints do not exist in the union of original and enrichment nodes
* any generated link uses `confidence: "EXTRACTED"`
* any original Graphify link is changed in the merged output
* merged node/link counts do not equal original plus enrichment, after documented dedupe

### Gate 2: Capability Completeness

Reuse or import the parsing rules from `scripts/check_capability_matrix.py`.

Fail if:

* any `LEGENDS_API` export lacks `public_c_api`, `capability_entry`, `capability_matrix_row`, direct implementation, or proxy implementation
* manifest and Markdown statuses differ
* manifest keys do not exactly match header exports

### Gate 3: Proxy And Dispatcher Parity

Fail if:

* `proxy-supported` API has no `sends_request`
* `proxy-supported` request lacks `handled_by_dispatcher`
* handled request lacks `dispatcher_returns`
* handled request has no `ipc_message_struct`
* request/response pair is missing from `MsgType`
* dispatcher calls an API different from the manifest API without an explicit `aliases_api` edge

Warn, not fail, for `proxy-partial` APIs if their notes explain the gap and the static edges match the partial behavior.

### Gate 4: Test Evidence

Fail if:

* no test graph is generated
* `legends_abi_test` and `legends_ipc_integration_tests` are not represented as CMake targets
* a `proxy-supported` API has neither direct API test evidence nor MsgType test evidence

Warn if:

* the only test evidence is from a disabled test
* coverage is inferred from broad fixture helper calls rather than an explicit test body call

### Gate 5: CMake Boundary Evidence

Fail if:

* `legends_proxy` does not include `src/legends_proxy/proxy_api.cpp`
* `legends_engine_host` does not include `src/engine_host/main.cpp`
* `legends_engine_host` does not link `legends_core` and `legends_ipc`
* IPC build evidence is unavailable and the QA artifact does not record why
* `project_legends` IPC-mode linkage cannot be distinguished from dev-mode linkage

Warn if:

* CMake parsing relies only on regex extraction and not File API or build output
* generator expressions are preserved as raw text

### Gate 6: Query Smoke Tests

Run deterministic graph queries over `projectlegends-graph-enriched.json` without invoking LLM inference.

Required paths:

* `legends_mount_drive -> MountDriveReq -> dispatcher case -> legends_mount_drive`
* `legends_key_event_ext -> aliases_api -> legends_key_event -> KeyEventReq`
* `legends_capture_audio -> proxy-partial -> no dispatcher case or shared-memory caveat`
* `legends_proxy -> proxy_api.cpp -> proxy_c_api_impl nodes`
* `legends_ipc_integration_tests -> test_ipc_integration.cpp -> StepMsReq`

## Implementation Phases

1. Sidecar schema and builder skeleton.
2. API, manifest, proxy, MsgType, and dispatcher extraction.
3. Test and CMake extraction.
4. Checker gates and Markdown QA artifact.
5. Optional CI wiring after the checker is stable locally.

## Risks

* Regex parsing C++ and CMake can drift. Keep extraction scoped, fail closed, and reuse existing checker helpers where possible.
* Static test evidence is not execution evidence. The QA artifact must still record actual test commands and failures.
* Graphify schema can change. The sidecar should depend only on stable `nodes` and `links` fields and preserve unknown fields when merging.
* `graphify-out` is generated and large. Do not require committing the merged graph unless the team explicitly wants generated artifacts in git.
* Windows path normalization can create duplicate nodes. Normalize to repo-relative POSIX-style paths inside the enrichment JSON.
* Disabled tests can create false confidence. Mark them explicitly and treat disabled-only coverage as a warning.

## Recommended Next Step

Ask Gemini/AGY to implement phases 1 and 2 first. That gives Codex an auditable capability-to-dispatcher graph before spending time on lower-confidence CMake and test inference.
