# ProjectLegends Agent Workflow

Last updated: 2026-06-09 UTC / 2026-06-08 America/Denver session.

This document is the handoff map for future ProjectLegends agent sessions. It captures the workflow we converged on: Codex writes the design and audits the result; Gemini Flash implements from an XML packet; OpenSpec, Graphify, and CI provide the evidence gates.

## Current Repository State

- Default branch: `master` (`origin/HEAD -> origin/master`).
- Codex role: architect, prompt author, auditor, fixer, CI owner.
- Gemini Flash role: implementation worker only.
- OpenSpec role: canonical sprint requirements before code changes.
- XML prompt role: execution packet that tells Gemini exactly which OpenSpec changes to implement and which QA artifact to return.
- Graphify role: source graph evidence for architecture claims, RuntimeHost bypass enforcement, capability truth checks, and README architecture updates.
- CI role: remote proof after local build, tests, graph checks, and repository hygiene checks pass.

## Sprint Loop

1. Inspect the current tree and remote health.
2. Write or update OpenSpec changes under `openspec/changes/<change-id>`.
3. Validate the OpenSpec changes strictly before implementation:

   ```powershell
   openspec.cmd validate <change-id> --strict --json
   openspec.cmd show <change-id> --json
   ```

4. Create an XML prompt in `docs/superpowers/prompts/` for Gemini Flash.
5. Gemini implements only the scoped OpenSpec changes and returns a QA artifact.
6. Codex audits the QA artifact, diffs, tests, and claims gate by gate.
7. Codex fixes any issues directly, updates specs/docs/gates if needed, and reruns verification.
8. Commit and push only after local gates pass.
9. Verify GitHub Actions on `origin/master`; inspect job logs and fix failures until the latest head is green.
10. Record durable lessons in `docs/superpowers/plans/`, `docs/superpowers/reviews/`, or this workflow file.

## XML Prompt Contract

Every Gemini XML prompt must include:

- The exact repository, branch, and baseline commit or current expected head.
- The OpenSpec change paths to validate and implement.
- Phase-by-phase gates with stop conditions.
- A strict instruction that Gemini is the implementer and Codex is the auditor.
- Required verification commands.
- Required QA artifact path under `docs/superpowers/reviews/`.
- Required QA artifact sections:
  - OpenSpec paths and validation results.
  - Gate status table.
  - Before/after metrics.
  - Files changed.
  - Commands passed.
  - Commands failed or blocked.
  - Remaining known gaps.
  - Top five Codex audit targets.

Do not let the XML prompt grant Gemini authority to mark architecture truth by assertion. Any capability, proxy parity, RuntimeHost, or CI claim must be backed by tests, Graphify evidence, or a deterministic validator.

## Codex Audit Rules

Codex must audit the implementation before accepting it:

- Compare the QA artifact against the actual diff.
- Verify that claimed PASS gates have command evidence.
- Re-run OpenSpec validation for touched changes.
- Re-run capability truth validation after any public API, proxy, or dispatcher change.
- Re-run Graphify after architecture or app/runtime routing changes.
- Inspect negative-path behavior, not just success paths.
- Reject overclaims such as "proxy-supported" when only message routing exists.
- Keep generated reports synchronized with source changes.
- Promote repeated audit findings into scripts or CI gates.

## Graphify Commands

Use Graphify before making architecture claims:

```powershell
python scripts/graphify_projectlegends.py update --repo .
python scripts/graphify_projectlegends.py summary --repo .
python scripts/graphify_projectlegends.py runtimehost-bypasses --repo .
python scripts/graphify_projectlegends.py check --repo . --strict --strict-tests fail
```

CI-compatible source-only mode:

```powershell
python scripts/graphify_projectlegends.py update --repo . --source-only
python scripts/check_graphify_enrichment.py --repo . --overlay graphify-out/projectlegends-enrichment.json --strict --strict-tests fail --allow-missing-graphify
```

Current Graphify audit snapshot from the 2026-06-08/09 pass:

- Raw Graphify graph: `39,172` nodes and `818,069` edges.
- ProjectLegends enrichment: `5,640` nodes and `8,010` links.
- Public C APIs: `50`.
- RuntimeHost methods: `32`.
- IPC dispatcher cases: `43`.
- Test cases scanned: `4,665`.
- CMake targets scanned: `17`.
- App direct RuntimeHost bypasses: `2`, both allowlisted lifecycle calls:
  - `Application::init -> legends_create`
  - `Application::shutdown -> legends_destroy`

The RuntimeHost bypass count must remain exactly two unless an OpenSpec explicitly changes the lifecycle model and updates `docs/architecture/runtimehost-bypass-allowlist.json`.

## Local Verification Gates

Run these before committing implementation work:

```powershell
cmake --preset dev
cmake --build --preset dev
ctest --test-dir build\dev --parallel 4 --output-on-failure
python scripts/check_conflict_markers.py --path .
python scripts/check_capability_matrix.py --repo .
python scripts/graphify_projectlegends.py update --repo . --source-only
python scripts/graphify_projectlegends.py runtimehost-bypasses --repo .
python scripts/check_graphify_enrichment.py --repo . --overlay graphify-out/projectlegends-enrichment.json --strict --strict-tests fail --allow-missing-graphify
git diff --check
```

Use targeted binaries when a sprint touches a narrower subsystem, but do not skip the full local test suite before pushing changes that affect shared architecture, CI, CMake, public APIs, IPC, RuntimeHost, save/load, or PAL.

## CI Strategy

Primary push/PR health is enforced through:

- `CI`: Linux GCC, Linux Clang, Windows MSVC, IPC mode, coverage report generation, C ABI checks.
- `Sprint 2 Checks`: globals migration, GSL bridge usage, conflict marker guard, capability matrix guard, Graphify source-only enrichment guard.
- `Module DAG`: CMake module dependency policy.
- `Optional PAL CI`: headless, SDL2, SDL3, contract gates, ASan lifecycle, pure C ABI, Windows headless.

CI rules:

- Push to `origin/master` only after local gates pass.
- After push, use `gh run list` and `gh run view` to inspect the latest head, not stale earlier failures.
- When a job fails, inspect the concrete job log before editing.
- Keep optional workflows path-filtered, but ensure tests for an optional subsystem trigger that subsystem's workflow.
- Coverage is currently report-only; do not enforce a percentage threshold until a measured baseline is established.
- Optional research/heavy lanes such as fuzzing, dependency scanning, TLA+, static analysis, and packaging should stay scheduled, manual, or tag-gated unless intentionally promoted.

## Artifact Locations

- OpenSpec changes: `openspec/changes/`.
- XML prompts: `docs/superpowers/prompts/`.
- Gemini QA artifacts: `docs/superpowers/reviews/`.
- Codex audit reports: `docs/superpowers/reviews/`.
- Planning notes: `docs/superpowers/plans/`.
- Graphify interface docs: `docs/architecture/graphify-interface.md`.
- Graphify generated report: `docs/architecture/graphify-enrichment-report.md`.
- Capability truth manifest: `docs/architecture/capability_truth.json`.
- Capability truth matrix: `docs/architecture/2026-06-08-public-capability-truth-matrix.md`.
- RuntimeHost bypass allowlist: `docs/architecture/runtimehost-bypass-allowlist.json`.

## Resume Checklist

At the start of a future session:

1. `git status -sb`
2. `git log --oneline -5`
3. `gh run list --repo CharlesHoskinson/ProjectLegends --branch master --limit 10`
4. Read this file.
5. Read the latest relevant OpenSpec changes.
6. Read the latest QA artifact in `docs/superpowers/reviews/`.
7. Run `python scripts/graphify_projectlegends.py summary --repo .`.
8. Decide the next sprint only after current tree, graph, and CI health are known.
