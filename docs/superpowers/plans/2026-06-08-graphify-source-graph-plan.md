# Graphify Source Graph Plan: ProjectLegends

## Current Graph State

Graphify is installed as `graphifyy 0.8.35`.

The first AST-only graph was generated with:

```powershell
& "$env:APPDATA\Python\Python314\Scripts\graphify.exe" update . --no-cluster
```

Output:

* `graphify-out/graph.json`
* `graphify-out/manifest.json`
* `graphify-out/cache/`

Current graph size:

* 38,455 extracted nodes reported during update
* 108,459 raw edges
* 38,273 post-build nodes after diagnostics
* 82,833 post-build edges after diagnostics

Codex integration was installed with:

```powershell
& "$env:APPDATA\Python\Python314\Scripts\graphify.exe" codex install
```

This created `AGENTS.md` and `.codex/hooks.json`.

## Build Variant Inputs

The graph should treat build variants as first-class context:

* `build/dev/compile_commands.json` exists and represents the default monolithic build (`LEGENDS_USE_IPC=OFF`).
* `build/ipc` now configures and builds when Ninja, Clang, and `llvm-rc` are passed explicitly.
* Plain `cmake --preset ipc` may fail in this Windows shell if those tools are not discoverable on `PATH`.

Useful IPC configure command:

```powershell
cmake --preset ipc `
  -DCMAKE_MAKE_PROGRAM=C:/Users/charl/AppData/Local/Microsoft/WinGet/Packages/Ninja-build.Ninja_Microsoft.Winget.Source_8wekyb3d8bbwe/ninja.exe `
  -DCMAKE_C_COMPILER="C:/Program Files/LLVM/bin/clang.exe" `
  -DCMAKE_CXX_COMPILER="C:/Program Files/LLVM/bin/clang++.exe" `
  -DCMAKE_RC_COMPILER="C:/Program Files/LLVM/bin/llvm-rc.exe"
```

## High-Value Graph Views

### Capability API Parity

Target path:

```text
legends_embed.h export
  -> direct implementation
  -> proxy implementation
  -> IPC MsgType
  -> message struct
  -> engine_dispatcher case
  -> capability_truth.json status
  -> Markdown matrix row
  -> tests
  -> CI workflow
```

Primary questions:

* Which public APIs are called by `Application` but are `proxy-missing` or `proxy-partial`?
* Which `proxy-supported` APIs lack active tests?
* Which manifest rows have stale notes after dispatcher changes?

### RuntimeHost Adoption

Target path:

```text
Application call site
  -> RuntimeHost interface
  -> InProcessEngineRuntime or IpcEngineRuntime
  -> linked legends_* implementation
```

Current caveat:

* `src/app/application.cpp` still stores `legends_handle` and calls `legends_*` directly. RuntimeHost adoption is not complete.
* `IpcEngineRuntime` does not own engine-host spawning, proxy connection setup, or shared-memory lifecycle.

Primary questions:

* Which `legends_*` calls still bypass `RuntimeHost`?
* Which app features would regress in `LEGENDS_USE_IPC=ON`?
* Where should `create_runtime()` be introduced first with minimal blast radius?

### IPC Message Coverage

Target path:

```text
MsgType enum
  -> request/response structs
  -> serialize/deserialize code
  -> proxy sender
  -> dispatcher receiver
  -> tests
```

Primary questions:

* Which request/response pairs exist but have no dispatcher case?
* Which variable-payload messages lack bounds tests?
* Which dispatcher cases have no direct unit coverage?

### CMake Boundary And License DAG

Target path:

```text
CMake target
  -> sources
  -> link libraries
  -> compile definitions
  -> preset
  -> CI job
```

Primary questions:

* In `LEGENDS_USE_IPC=ON`, does `project_legends` avoid transitive `legends_core`/`aibox_core` linkage?
* Which targets compile `runtime_host.cpp`, `proxy_api.cpp`, and `engine_dispatcher.cpp`?
* Does CI configure and build the IPC preset?

## Enrichment Backlog

Graphify's AST graph is useful, but ProjectLegends needs domain-specific edges:

* `public_api -> capability_truth_entry`
* `public_api -> direct_implementation`
* `public_api -> proxy_implementation`
* `proxy_implementation -> MsgType`
* `MsgType -> dispatcher_case`
* `dispatcher_case -> direct_c_api_call`
* `test_file -> covered_api_or_message`
* `workflow_step -> validator_script`
* `cmake_target -> source_file`
* `cmake_target -> linked_target`
* `preset -> compile_commands`

The next implementation step should be a small enrichment script that reads:

* `include/legends/legends_embed.h`
* `src/legends/legends_embed_api.cpp`
* `src/legends_proxy/proxy_api.cpp`
* `src/engine_host/engine_dispatcher.cpp`
* `include/legends_ipc/message_types.h`
* `include/legends_ipc/messages.h`
* `docs/architecture/capability_truth.json`
* `.github/workflows/*.yml`
* `CMakeLists.txt`

and emits a supplemental graph or report focused on RuntimeHost/proxy parity.

Detailed implementation and QA planning now lives in:

* `docs/superpowers/plans/2026-06-08-graphify-enrichment-qa-plan.md`
* `docs/superpowers/plans/2026-06-08-graphify-enrichment-qa-layer.md`

The canonical implementation shape is:

```powershell
python scripts/enrich_graphify_projectlegends.py --repo . --graphify graphify-out/graph.json --out graphify-out/projectlegends-enrichment.json --report docs/architecture/graphify-enrichment-report.md
python scripts/check_graphify_enrichment.py --repo . --overlay graphify-out/projectlegends-enrichment.json --strict
```

## Working Commands

Regenerate AST graph:

```powershell
& "$env:APPDATA\Python\Python314\Scripts\graphify.exe" update . --no-cluster
```

Run diagnostics:

```powershell
& "$env:APPDATA\Python\Python314\Scripts\graphify.exe" diagnose multigraph --json --max-examples 3
```

RuntimeHost query:

```powershell
& "$env:APPDATA\Python\Python314\Scripts\graphify.exe" query "RuntimeHost IpcEngineRuntime Application legends_create proxy_api engine_dispatcher" --budget 1200
```

Mount/unmount query:

```powershell
& "$env:APPDATA\Python\Python314\Scripts\graphify.exe" query "MountDriveReq legends_mount_drive engine_dispatcher proxy_api capability_truth" --budget 1200
```

## Audit Rule

Graphify is an orientation layer. It does not replace:

* `python scripts/check_capability_matrix.py --repo .`
* `python scripts/check_conflict_markers.py --path .`
* `cmake --preset dev`
* `cmake --build --preset dev`
* `cmake --build --preset ipc`
* `build/dev/legends_abi_test.exe`
