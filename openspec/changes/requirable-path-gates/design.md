## Context

`ci.yml` triggers unfiltered (`.github/workflows/ci.yml:18-27`); the other three workflows filter at `on.paths` (`pal-ci.yml:3-24`, `module-dag.yml:18-45`, `sprint2-checks.yml:3-27`). GitHub's documented behavior: a workflow skipped by `paths:` leaves its checks Pending forever, blocking any PR that requires them; a job skipped by a job-level `if:` reports a conclusion and satisfies branch protection (audit-wiki/wiki/sources/CI Design for C++-CMake Monorepos (2026-06).md, practice 3). So none of the script, include-rules, DAG, or PAL gates can join the `master-ruleset-required-checks` required set as written (Recommendation Review (2026-06).md, M-3/G-3).

Filter rot, against `cmake/ModuleManifest.cmake:10-51` (CI Gate Coverage Map):
- `openspec/**` appears in no workflow's paths; `scripts/check_openspec_staleness.py` runs only when an unrelated path triggers sprint2 (`sprint2-checks.yml:62-63`).
- `cmake/**` does not trigger sprint2 (its list has only `CMakeLists.txt` and `CMakePresets.json`, `sprint2-checks.yml:6-7,18-19`) while it does trigger pal-ci's full backend builds (`pal-ci.yml:10,19`), which contain no cmake-specific check.
- pal-ci triggers on all of `include/**` though its subject is the PAL module (`include/pal`, `src/pal`) plus contract gates on `legends_core`.
- sprint2 pushes fire on any branch (`sprint2-checks.yml:4-14`); the other three restrict to `main`/`master`/`develop`.
- `module-dag.yml` claims "All violations block PRs immediately" (`module-dag.yml:10-12`) while being structurally unable to be required.

## Goals / Non-Goals

**Goals:**
- Every gate job in `module-dag.yml` and `sprint2-checks.yml` reports a conclusion on every PR to protected branches — eligible for the required set.
- Changed-path scoping moves from workflow-level `paths:` to a first job plus job-level `if:`; unrecognized paths run everything.
- Path families hand-aligned with `cmake/ModuleManifest.cmake`; `openspec/**` and `cmake/**` attach to the gates written for them.
- `ci.yml` build jobs stop running full builds for docs/wiki-only changes.
- pal-ci's trigger set narrows to its actual subject.

**Non-Goals:**
- Restructuring pal-ci into changed-paths form — deferred to `consolidate-workflows-policy` (R8); its jobs stay non-requirable and "Optional" until then (Recommendation Review, G-3).
- A generator that derives the filter map from the manifest — deferred until this changed-paths job exists to consume it (Recommendation Review, M-4).
- Extending the master ruleset's required-check list — that is a follow-up under `master-ruleset-required-checks`'s name-sync rule; this change only makes candidates eligible.
- `concurrency:` groups, `timeout-minutes`, `permissions:` on the non-ci.yml workflows — R8 (`consolidate-workflows-policy`).
- Test selection from the DAG (deferred T-2, CI-THESIS.md).

## Decisions

**D1 — Job-level `if:` skips behind broad triggers, not workflow-level `paths:`.** This is the GitHub-documented asymmetry: skipped-by-`if` reports, skipped-by-`paths` pends (CI Design for C++-CMake Monorepos (2026-06).md, practice 3). Alternative rejected: keeping `paths:` and registering the checks as required anyway — deadlocks every non-matching PR.

**D2 — One `changed-paths` job per workflow, logic in `scripts/ci_changed_paths.py`.** The job checks out with enough history to diff, runs the script, and publishes one boolean output per path family via `GITHUB_OUTPUT`. The script (not inline YAML) holds the family map so it is unit-testable and locally runnable, consistent with the gate-logic-leaves-YAML direction of `preflight-gate-entrypoint` (R3). Alternative rejected: a third-party paths-filter action — adds a supply-chain dependency ahead of `workflow-lint-pinning` (R13) for logic that is a `git diff` plus a prefix match.

**D3 — Diff base per event.** `pull_request`: `github.event.pull_request.base.sha` against the PR head. `push`: `github.event.before` against `github.sha`. If the base is unusable (forced push, `before` all-zeros, new branch) or the event is `schedule`/`workflow_dispatch`/tag push: classify nothing and set every output true.

**D4 — Fail open: unrecognized paths run everything.** Any changed file not matching the family map sets all outputs true. A wrong skip silently un-gates a merge; a wrong run costs minutes. The family map therefore only ever narrows known-safe families, and new top-level directories are run-everything by default until explicitly mapped (CI-THESIS.md, R6).

**D5 — Path families hand-aligned with `cmake/ModuleManifest.cmake:10-51`, maintained by hand.** Families and consumers:
- `core` (`include/legends/**`, `src/legends/**`), `pal` (`include/pal/**`, `src/pal/**`), `engine` (`engine/**`), `ipc` (`include/legends_ipc/**`, `src/legends_ipc/**`, `src/legends_proxy/**`, `src/engine_host/**`), `tests` (`tests/**`), `build` (`CMakeLists.txt`, `CMakePresets.json`, `cmake/**`), `scripts` (`scripts/**`), `openspec` (`openspec/**`), `docs-architecture` (`docs/architecture/**`), `workflows` (`.github/**`), `docs-only` (`docs/**` else, `audit-wiki/**`, `llm-wiki/**`, `*.md` at root).
- module-dag `include-rules` and `cmake-dag`: run unless the change is docs-only (include rules and the configure-time DAG span every module, so any code/build/scripts family runs them).
- sprint2 `globals-registry`: runs on `core`/`pal`/`engine`/`ipc`/`tests`/`build`/`scripts`/`openspec`/`docs-architecture`/`workflows` — `openspec` now reaches `check_openspec_staleness.py` and `build` reaches the cmake-adjacent checks, closing the M-4 gaps.
- sprint2 `multi-instance-tests`: runs on code/build/tests families; skips on `openspec`-, `docs-architecture`-, or docs-only changes.
- ci.yml `linux`, `linux-ipc`, `windows`, `coverage`, `abi-check`, `sanitizers`, `fuzz`: skip only when the change is docs-only; everything else runs them (these are R2's required checks — their scope only narrows by the family the Coverage Map shows has no content gate).

**D6 — module-dag's `Summary` becomes the requirable aggregate.** `summary` already runs `if: always()` with `needs` on all four jobs (`module-dag.yml:182-216`). Its pass condition changes from `success` to success-or-skipped for `include-rules` and `cmake-dag` (it already accepts skipped for the nightly builds). Required-set candidates from this workflow: register `Summary` alone — one name, stable under matrix or job additions. Alternative rejected: requiring `Include Rules` and `CMake DAG` individually — works (skipped satisfies), but two names to keep in sync for no gain.

**D7 — sprint2 jobs are individually requirable.** Two jobs, no aggregate exists; with `paths:` removed and `if:` skips reporting, `Globals Registry Validation` and `Multi-Instance Smoke Tests` can be required by exact name. No new summary job — adding one belongs to R8 consolidation.

**D8 — sprint2 push trigger gets `branches: [main, master, develop]`.** Aligns with the other three workflows (`sprint2-checks.yml:4-14` vs `ci.yml:18-23`); feature-branch pushes stop running it, PRs still cover those changes.

**D9 — pal-ci narrows but keeps `on.paths`.** New filter: `src/pal/**`, `include/pal/**`, `include/legends/**`, `src/legends/**` (contract-gates inspects `liblegends_core.a` symbols, `pal-ci.yml:138-181` — today it is reachable only via the over-broad `include/**`), `tests/unit/test_pal_*.cpp`, and the workflow file itself. Dropped: `cmake/**`, `CMakeLists.txt`, the rest of `include/**`. Build-system breakage of PAL remains covered by the unfiltered `ci.yml` and module-dag's `cmake-dag`. The workflow stays non-requirable by design until R8 restructures it (Recommendation Review, G-3).

## Risks / Trade-offs

- [Misclassified family skips a gate that should have run] → fail-open default (D4); families only narrow paths the CI Gate Coverage Map shows are otherwise unguarded or fully covered by ci.yml; the classifier is a reviewed, unit-tested script, not per-workflow YAML.
- [Docs-only PRs merge with build checks skipped] → intended: skipped satisfies branch protection, and the Coverage Map records no content gate for those paths today — the change converts a 3-hour build of unrelated code into an explicit, visible skip.
- [`changed-paths` job itself fails and blocks everything] → it is a sub-minute git-diff job; its failure fails the workflow loudly (fail-closed), which is the correct direction for a gate precondition.
- [`github.event.before` unusable on force pushes] → detected in the script; falls back to run-everything (D3).
- [Family map drifts from `ModuleManifest.cmake` again] → the map lives in one script with a comment block citing the manifest; the deferred generator (M-4) replaces hand maintenance once this consumer exists.
- [Skipped required checks read as "passed" in the UI and mislead reviewers] → merge-policy documentation in `master-ruleset-required-checks` records the semantics; the skip reason is visible on the check run.
- [pal-ci narrowing reduces incidental coverage of `cmake/**` changes] → those changes still run ci.yml (unfiltered, all build jobs) and module-dag `cmake-dag`; pal-ci's backend builds added duplicate coverage, not unique coverage (CI Workflows (GitHub Actions).md, duplication list).

## Migration Plan

1. Land `scripts/ci_changed_paths.py` with unit tests, then the four workflow edits in one PR (the workflows self-trigger on their own files, so the PR exercises them).
2. Verify on probe PRs before any ruleset change: a docs-only PR (gates report skipped, not absent), an `openspec/**`-only PR (`globals-registry` runs), a `src/**` PR (all gates run).
3. Only after verification: extend the master ruleset's required set (separate change under `master-ruleset-required-checks`'s name-sync rule) with `Summary`, `Globals Registry Validation`, `Multi-Instance Smoke Tests`.
4. Rollback: revert the workflow edits; `on.paths` filters restore the old behavior verbatim; no server-side state changes in this change.

## Open Questions

- None blocking. Whether `multi-instance-tests` should also skip on `scripts`-only changes is decided at implementation by what its build consumes; the conservative default (run) costs one duplicate build.
