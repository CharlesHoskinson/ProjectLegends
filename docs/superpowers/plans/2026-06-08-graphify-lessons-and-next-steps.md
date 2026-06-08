# Graphify Lessons And Next Steps

## What We Learned

Graphify is most useful when treated as the base orientation layer, not as the final source of architectural truth. Its AST graph finds broad structure quickly, but ProjectLegends needs domain edges that Graphify cannot infer reliably from syntax alone.

The high-value ProjectLegends graph is the overlay:

```text
public legends_* API
  -> capability truth
  -> direct implementation
  -> proxy implementation
  -> IPC MsgType
  -> dispatcher case
  -> test evidence
  -> CMake target evidence
```

The capability matrix became more valuable once it was machine-checkable. The same pattern should be used for every remaining architecture claim: turn the claim into a source-derived edge, then make a checker reject drift.

The RuntimeHost work also exposed a useful audit distinction:

* Foundation exists when interfaces/classes are present.
* Adoption exists only when application call sites route through them.
* Parity exists only when direct, proxy, dispatcher, tests, and build targets agree.

This distinction should drive the next implementation stages.

## How To Use This For Remaining Steps

Use the graph interface as the first pass for every sprint:

```powershell
python scripts/graphify_projectlegends.py update --repo .
python scripts/graphify_projectlegends.py summary --repo .
python scripts/graphify_projectlegends.py explain-api legends_mount_drive --repo .
```

Then choose work by evidence gaps, not by intuition:

1. RuntimeHost adoption: query which `Application` call sites still bypass `RuntimeHost`, then migrate the smallest coherent slice.
2. Proxy parity: prioritize `proxy-missing` APIs that already have MsgType structs or dispatcher-adjacent code.
3. IPC safety: inspect variable payload messages and ensure deserialize bounds tests exist.
4. GPL isolation: verify CMake target edges for IPC mode before claiming proprietary/GPL separation.
5. CI hardening: keep every architectural truth backed by a source-only validator so CI can run without local Graphify state.

## Commit Strategy

Do not make one giant commit containing all AGY/Codex generated work. The current worktree contains several unrelated sprint layers.

Recommended commit order:

1. Graphify interface and enrichment tooling.
2. Capability matrix and dispatcher parity changes.
3. RuntimeHost foundation and IPC build fixes.
4. Documentation handoffs and plans.

Before committing:

```powershell
python scripts/graphify_projectlegends.py update --repo .
python scripts/check_capability_matrix.py --repo .
python scripts/check_conflict_markers.py --path .
git diff --check
cmake --build --preset dev
cmake --build --preset ipc
build\dev\legends_abi_test.exe
build\ipc\legends_abi_test.exe
```

The full unit suite still needs separate treatment because it had known pre-existing failures.
