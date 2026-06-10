# Change: coverage-diff-gate

## Why

The coverage lane measures but never gates: the per-PR `coverage` job filters lcov output without excluding the vendored engine (.github/workflows/ci.yml:744-747), then writes "Coverage policy: report-only; no minimum threshold is enforced by CI yet." (.github/workflows/ci.yml:749). The only numeric threshold in the repo — 80% on `*/src/app/*` — lives in `release-validation` behind `if: startsWith(github.ref, 'refs/tags/v')` (.github/workflows/ci.yml:879, 907-921) and has never executed because the repo has no tags. This implements CI-THESIS.md recommendation R9: enforce coverage without freezing development, by gating the lines a PR touches rather than the legacy total.

## What Changes

- Exclude the vendored engine from the policy denominator: add `'*/engine/*'` to the `lcov --remove` list (.github/workflows/ci.yml:744-747) so `coverage.filtered.info` covers only first-party code. Prerequisite for every other number meaning anything (audit-wiki/wiki/sources/Coverage Policy Ratcheting (2026-06).md, practice 4).
- **BREAKING**: gate PRs on diff coverage of new/changed lines using the artifact the job already produces — diff-cover consumes LCov natively; one step (`diff-cover coverage.filtered.info --compare-branch=origin/master --fail-under=<target>`) replaces the report-only echo. Requires a non-shallow checkout (`fetch-depth: 0`) so the merge base exists (Recommendation Review rows T-3, G-10). One informational PR cycle precedes enforcement.
- Commit per-module ratchet floors aligned to the module DAG: a floor file with one line per `src/` module, seeded from the first post-engine-exclusion measurement on master, enforced by an `lcov --extract` loop; floors never decrease without a tracked issue.
- Widen `release-validation`'s tag-only `if:` (.github/workflows/ci.yml:879) to admit `workflow_dispatch`, with the packaging-artifact check guarded to tag runs, so the 80% threshold job can be rehearsed by dispatch before it gates a real release (Recommendation Review row G-10).
- Enforcement is token-free: the gate runs unconditionally in the workflow; Codecov upload stays conditional (`if: env.CODECOV_TOKEN != ''`, .github/workflows/ci.yml:759-764) as reporting UI only.

## Capabilities

### New Capabilities

- `coverage-gating`: PR diff-coverage gate, first-party-only policy denominator, committed per-module ratchet floors, and a rehearsable release coverage threshold.

### Modified Capabilities

- `ci-stabilization`: the Coverage Signal requirement currently mandates the policy be "explicitly documented as report-only until a baseline is established" (openspec/specs/ci-stabilization/spec.md). This change establishes that baseline and replaces report-only with enforced diff coverage plus ratchet floors; the published artifact's denominator excludes the vendored engine.

## Impact

- `.github/workflows/ci.yml` — `coverage` job (lcov filter, checkout depth, diff-cover step, floor-check loop, policy text) and `release-validation` job (`if:` condition, artifact-check guard).
- New committed floor file (`.ci/coverage-floors.txt`) seeded after the engine exclusion lands.
- New dev dependency in the coverage job: `diff-cover` (pip).
- Downstream: the `coverage` job only binds once it joins the required-check set (CI-THESIS.md R2); per-module floors reuse the DAG module list that R6/R7 also consume.
