## Why

Master has no branch protection and no ruleset — verified server-side: `gh api .../rules/branches/master` returns `[]` and the branch-protection endpoint 404s (audit-wiki/wiki/syntheses/Recommendation Review (2026-06).md, G-2). 233 of 397 retained Actions runs are direct pushes; green verdicts bind nothing (CI-THESIS.md, R2). This change makes green a precondition of merging.

## What Changes

- **BREAKING (workflow):** direct pushes to `master` are rejected; all changes land via PR with the required checks green and the branch up to date.
- Add an active GitHub ruleset targeting exactly `master` (no wildcard): require pull requests; require the five exact-name checks that already run unconditionally in `ci.yml` — `Linux (gcc)`, `Linux (clang)`, `Linux IPC (gcc)`, `Windows (MSVC)`, `C ABI Verification`; require branches up to date before merge; forbid force pushes and deletions.
- Commit the ruleset configuration as a reviewable JSON document (`docs/ci/master-ruleset.json`) with the `gh api` command that applies it — the server-side setting gets a repo-tracked source of truth.
- Add a policy doc (`docs/ci/merge-policy.md`) covering the required-check set, the up-to-date rule, bypass discipline, and the maintenance rule: required-check names update in the same change whenever workflow consolidation (R8) renames jobs.
- Defer the merge queue: at current PR volume, require-up-to-date delivers the never-merge-red invariant, and no workflow has a `merge_group` trigger (audit-wiki/wiki/sources/Merge Queues & Required Checks (2026-06).md, P10; Recommendation Review G-4).
- Prerequisite gate: applies only after `ci-stabilize-mandatory-lanes` (R1) lands — protection before green freezes all merging.

## Capabilities

### New Capabilities
- `merge-gating`: master ruleset semantics — PR requirement, exact-name required checks, up-to-date enforcement, force-push prohibition, repo-tracked ruleset config, name-sync maintenance rule, merge-queue deferral condition.

### Modified Capabilities

(none — `openspec/specs/ci-stabilization` defines which lanes are primary vs optional; this change binds the already-primary lanes to merging without altering those requirements)

## Impact

- Server-side repository settings (GitHub ruleset on `master`) — applied via `gh api`, not a file in the repo.
- `docs/ci/master-ruleset.json` — new, the exact ruleset payload.
- `docs/ci/merge-policy.md` — new, the documented policy.
- No workflow files change: the five required checks are existing unconditional `ci.yml` job names (`.github/workflows/ci.yml:37,96,190,407`).
- Sequencing: blocked on R1 (`ci-stabilize-mandatory-lanes`); R6 (`requirable-path-gates`) may later extend the required set; R8 (`consolidate-workflows-policy`) must update check names here in the same change if it renames jobs.
