## Why

The four workflow files are the only source files in the repository that no gate validates: a typo, a broken `if:` expression, or a renamed job in 1,526 lines of YAML reaches `master` unchecked, and the failure surfaces only as the next confusing run — the `Optional Linux SDL3 (${{ matrix.compiler }})` job recorded in run history under its unexpanded template name, never executing as such (CI-THESIS.md R13; audit-wiki/wiki/syntheses/Gap Analysis — Maintainability (2026-06).md finding 8). Every `uses:` reference is a mutable tag, `permissions:` exists only in ci.yml, and no dependency updater exists anywhere in the repo (Recommendation Review A-8; audit-wiki/wiki/entities/CI Workflows (GitHub Actions).md).

## What Changes

- **New lint lane** `.github/workflows/lint.yml`: actionlint (pinned release binary, checksum-verified, shellcheck integration on) runs on every push and PR — no path filters, so the check always reports and stays eligible to become required (the pend-forever hazard from Merge Queues & Required Checks P4 is designed out from birth). The lane carries `permissions: contents: read`, `timeout-minutes`, and a `concurrency:` group from its first commit.
- **Mechanical policy checks inside the lint lane**: a step fails the lane if any workflow file lacks a top-level `permissions:` block; a step fails the lane if any third-party `uses:` reference is not a full-length commit SHA.
- **Permissions blocks** added to `pal-ci.yml`, `module-dag.yml`, `sprint2-checks.yml` if still absent. Boundary with `consolidate-workflows-policy`: its hygiene group (task 1.4, `workflow-hygiene` capability) makes the identical edit. The edit is idempotent — whichever change lands first performs it, the other verifies and skips. This change owns the *enforcement* (the lint-lane check); `consolidate-workflows-policy` owns the *policy requirement* ("Every workflow declares least-privilege permissions"). Neither change blocks on the other.
- **SHA-pin third-party actions** — today the inventory is exactly one: `codecov/codecov-action@v4` (`ci.yml:761`); first-party `actions/*` references stay on major tags. Pins carry a trailing version comment. Landed **in the same PR** as `.github/dependabot.yml` (`package-ecosystem: github-actions`), per the A-8 binding: pinning without an updater becomes stale-pin rot. Dependabot also covers future third-party actions (R14's ccache/sccache actions arrive pre-bound to this policy).
- **Out of scope**: versioned runner labels (A-8: optional); adding the lint check to the master ruleset (owned by `master-ruleset-required-checks` / R2's extension procedure).

## Capabilities

### New Capabilities
- `workflow-lint`: workflow YAML is linted on every change; the lint lane mechanically enforces the permissions-block and SHA-pin policies.
- `action-pinning`: third-party actions are pinned to commit SHAs and an automated updater keeps the pins current; pins and updater land together.

### Modified Capabilities

(none — `openspec/specs/ci-stabilization` is untouched: the lint lane adds a validation, it does not change which build/test lanes run at which tier. The least-privilege permissions *policy* requirement lives in `consolidate-workflows-policy`'s pending `workflow-hygiene` capability and is not restated here; this change adds only its enforcement.)

## Impact

- New files: `.github/workflows/lint.yml`, `.github/dependabot.yml`.
- `.github/workflows/ci.yml` — `codecov/codecov-action@v4` pinned to SHA.
- `.github/workflows/pal-ci.yml`, `module-dag.yml`, `sprint2-checks.yml` — top-level `permissions: contents: read` added if `consolidate-workflows-policy`'s hygiene group has not already landed it.
- Sequencing: no prerequisites; CI-THESIS.md adoption order step 9 (lands as the earlier steps settle, conflicts with none of them). Future workflows (e.g. `build-and-test.yml` from `consolidate-workflows-policy`) are linted automatically on arrival.
