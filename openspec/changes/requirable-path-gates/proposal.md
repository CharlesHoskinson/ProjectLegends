## Why

Three of the four workflows are workflow-level path-filtered (`pal-ci.yml:3-24`, `module-dag.yml:18-45`, `sprint2-checks.yml:3-27`), and a path-filtered workflow leaves its checks Pending forever on non-matching PRs — a required check that never reports blocks every merge (audit-wiki/wiki/sources/CI Design for C++-CMake Monorepos (2026-06).md, practice 3). The script and DAG gates are therefore structurally ineligible for the `master-ruleset-required-checks` required set (CI-THESIS.md, R6). The filter sets have also rotted away from `cmake/ModuleManifest.cmake`: `openspec/**` triggers nothing although `check_openspec_staleness.py` exists for it (`sprint2-checks.yml:62-63`; CI Gate Coverage Map, openspec row), `cmake/**` does not trigger sprint2's checks, and pal-ci fires on `cmake/**` + `CMakeLists.txt` + all of `include/**` (Recommendation Review (2026-06).md, M-3/M-4/G-3).

## What Changes

- Remove workflow-level `paths:` filters from `module-dag.yml` and `sprint2-checks.yml`; both trigger broadly like `ci.yml`.
- Add a cheap first job (`changed-paths`) to `ci.yml`, `module-dag.yml`, and `sprint2-checks.yml` that classifies the changed files into path families and exposes boolean outputs; downstream gate jobs skip via job-level `if:` on those outputs. A job skipped by `if:` reports a conclusion and satisfies branch protection; a workflow skipped by `paths:` reports nothing.
- Unrecognized paths default to run-everything: any changed file outside the known family map sets every output true. Non-diffable events (schedule, dispatch, force-push with unusable `before` SHA) also run everything.
- Hand-align the path families with `cmake/ModuleManifest.cmake`: `openspec/**` attaches to the sprint2 `globals-registry` job (which runs `check_openspec_staleness.py`), `cmake/**` attaches to `globals-registry` and module-dag's `cmake-dag`. The filter-map generator is deferred until this changed-paths job exists to consume it (Recommendation Review, M-4).
- `ci.yml` build jobs skip on docs/wiki-only changes (`docs/**` outside `docs/architecture/**`, `audit-wiki/**`, `llm-wiki/**`) — paths the CI Gate Coverage Map shows have no content gate.
- `pal-ci.yml` keeps its workflow-level filter (restructuring is deferred to workflow consolidation per Recommendation Review, G-3) but the filter narrows to the PAL and legends module boundaries from the manifest; `cmake/**` and `CMakeLists.txt` drop out.
- `sprint2-checks.yml` push trigger gains a branch filter (`main`, `master`, `develop`) — today it fires on pushes to any branch (`sprint2-checks.yml:4-14`).
- `module-dag.yml`'s `summary` job accepts success-or-skipped from `include-rules` and `cmake-dag`, making `Summary` the single requirable aggregate for that workflow.
- Verify required-check eligibility: after the change, every gate job intended for the required set reports a conclusion (success or skipped) on every PR to protected branches.

## Capabilities

### New Capabilities
- `path-gating`: how CI workflows scope work to changed paths without losing required-check eligibility — broad triggers, first-job changed-path classification, job-level skips, fail-open defaults, manifest-aligned path families, aggregate-check semantics.

### Modified Capabilities

(none — `openspec/specs/ci-stabilization` governs lane stability and tiering, not trigger plumbing; no existing spec's requirements change)

## Impact

- `.github/workflows/module-dag.yml`, `.github/workflows/sprint2-checks.yml` — filters removed, `changed-paths` job added, job-level `if:` skips, summary semantics.
- `.github/workflows/ci.yml` — `changed-paths` job added; build jobs gain docs/wiki-only skips.
- `.github/workflows/pal-ci.yml` — trigger paths narrowed only; no structural change.
- `scripts/ci_changed_paths.py` — new, the classification logic (kept out of YAML; locally runnable).
- Enables `master-ruleset-required-checks` (R2) to later extend its required set with the script/DAG gates; check names there are unaffected by this change.
- Sequencing: after `ci-stabilize-mandatory-lanes` (R1) and `master-ruleset-required-checks` (R2) per CI-THESIS.md adoption order step 5; `consolidate-workflows-policy` (R8) later absorbs pal-ci's restructuring.
