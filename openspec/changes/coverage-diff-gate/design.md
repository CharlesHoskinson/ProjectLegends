# Design: coverage-diff-gate

## Context

The `coverage` job (.github/workflows/ci.yml:707-764) runs on every trigger tier: gcc-13 `--coverage` build, full ctest, lcov capture, then a filter that removes only `/usr/*`, `*/build/_deps/*`, `*/tests/*` (.github/workflows/ci.yml:744-747) — the vendored engine tree stays in the denominator. The policy step is an echo (.github/workflows/ci.yml:749); Codecov upload is conditional on a token secret (.github/workflows/ci.yml:759-764), and Codecov's `if_not_found` default is `success`, so any policy delegated there vanishes silently when the secret is absent. The only enforced threshold — 80% on `*/src/app/*` (.github/workflows/ci.yml:907-921) — sits in `release-validation` behind a tag-only `if:` (.github/workflows/ci.yml:879) that has never fired (no tags exist). The checkout in the coverage job is shallow (default `actions/checkout@v4`, .github/workflows/ci.yml:715), so no merge base is available for diff computation. Research basis: audit-wiki/wiki/sources/Coverage Policy Ratcheting (2026-06).md; current lane reality: audit-wiki/wiki/entities/Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism).md, Coverage section; binding modifications: audit-wiki/wiki/syntheses/Recommendation Review (2026-06).md rows T-3, G-10.

## Goals / Non-Goals

**Goals:**
- `coverage.filtered.info` measures first-party code only; the vendored engine leaves the policy denominator.
- Every PR is gated on diff coverage of its new/changed lines, computed from the existing lcov artifact, token-free.
- A committed per-module floor file makes absolute coverage a ratchet: regressions fail CI, improvements are locked in by raising the floor.
- The release 80% threshold is rehearsable by `workflow_dispatch` before its first execution on a real tag.

**Non-Goals:**
- Making the `coverage` job a required status check (CI-THESIS.md R2 owns the ruleset; an enforced step in a non-required job binds only when R2 adds it).
- Raising any module's coverage; this change prices new lines, not legacy debt.
- Codecov configuration (components, patch status) — Codecov remains optional reporting UI; the gate never depends on it.
- Engine coverage policy — excluded, not measured-and-gated; engine-touching PRs are not held to first-party standards.

## Decisions

**D1 — Engine exclusion lands first; every number downstream depends on it.**
Add `'*/engine/*'` to the `lcov --remove` list (.github/workflows/ci.yml:744-747). The vendored DOSBox-X tree dominates any whole-repo percentage and no PR-level policy can move it (Coverage Policy Ratcheting, practice 4). The same exclusion is passed to diff-cover (`--exclude 'engine/**'`) so engine-touching PRs contribute no engine lines to the diff denominator. Alternative rejected: keeping the engine in the artifact and filtering only at gate time — then the published artifact and the gated number disagree, and the floor seeding would bake in engine noise. If engine visibility is ever wanted, it is a separate informational Codecov component, never a gate input.

**D2 — Diff gate via diff-cover on the existing artifact; token-free by construction.**
After the lcov filter step, run `diff-cover coverage.filtered.info --compare-branch=origin/master --fail-under=<target>` unconditionally — no Codecov dependency, satisfying the review binding that enforcement must not ride on the token (Recommendation Review T-3/G-10; Coverage Policy Ratcheting, practices 1 and 5). diff-cover reads LCov natively. Prerequisites wired in the same step group: `fetch-depth: 0` on the job's checkout (merge-base computation needs history; shallow clones break `--compare-branch`), `git fetch origin master` when the event is a PR, and `pip install diff-cover`. The step runs only on `pull_request` events; pushes, nightly, and dispatch have no diff to measure and fall through to the floor check (D3). Two known C++ caveats are accepted: lcov path strings must match git-diff paths (both are repo-relative here since lcov runs at the workspace root), and multi-line statements may undercount (the XML-only `--expand-coverage-report` workaround is unavailable for LCov input) — undercounting fails toward stricter, which is the safe direction. Alternatives rejected: Codecov `codecov/patch` status (rides on the token, `if_not_found: success` fails open); genhtml `--baseline-file`/`--diff-file` differential coverage (no baseline tracking infrastructure exists yet; revisit if diff-cover's line/statement mismatch bites).

**D3 — Ratchet floor: committed file, seeded from measurement, never decreased silently.**
A committed `.ci/coverage-floors.txt`, one line per module: `<module> <line-percent>` for the seven DAG-verified module directories (`src/app`, `src/legends`, `src/legends_ipc`, `src/legends_proxy`, `src/engine_host`, `src/pal`, `src/libs` — the same set `module-dag.yml` enforces include rules over). Seeding procedure: after D1 merges, take the first master run of the `coverage` job, read each module's line percentage from the per-module extract loop output, and commit those numbers verbatim (rounded down to one decimal) as the initial floors. No placeholder or aspirational number is ever committed. Enforcement: a workflow step loops `lcov --extract coverage.filtered.info "*/src/<module>/*"` + `lcov --summary` percentage extraction — the exact shell that already exists single-module at .github/workflows/ci.yml:912-917 — and fails if any module measures more than 0.5 points below its floor (slack absorbs gcov template/inline link-order noise; Coverage Policy Ratcheting, practice 2 conflict note). Above-floor measurements print a prompt to raise the floor; the raise is a manual commit, not an auto-bump (auto-bumping on noisy gcov data manufactures flaky reds). Lowering a floor is a lane demotion and inherits the ci-stabilization demotion rule: tracked issue with exit criterion required. Alternative rejected: single whole-`src/` floor — it lets a regression in `src/legends_ipc` hide behind an improvement in `src/app`; the per-module loop is what aligns the policy to the DAG (CI-THESIS.md R9).

**D4 — Release rehearsal: widen the `if:`, guard the artifact steps, handle the skipped dependency.**
Change `release-validation`'s condition (.github/workflows/ci.yml:879) to fire on tags or `workflow_dispatch`. Two mechanics follow. First, `needs: [linux, packaging]` (.github/workflows/ci.yml:880) — `packaging` is itself tag-only (.github/workflows/ci.yml:804), so on a dispatch run it is skipped and the default `success()` in `needs` evaluation would skip `release-validation` too; the widened `if:` must therefore use explicit `needs.*.result` checks: require `needs.linux.result == 'success'` always, and `needs.packaging.result == 'success'` only when the ref is a tag. Second, the artifact download/verify steps (.github/workflows/ci.yml:923-929 and onward) get `if: startsWith(github.ref, 'refs/tags/v')` so a dispatch rehearsal exercises exactly the build/test/coverage-threshold path and skips the packaging-artifact assertions — the guarded-artifact-check binding from Recommendation Review G-10. Rationale: a threshold that has never run is a gate never verified to fail; nobody knows today whether `src/app` clears 80% (Coverage Policy Ratcheting, practice 6). The rehearsal answers that before a release hangs on it. Alternative rejected: pushing a throwaway prerelease tag — it pollutes tag history and triggers the full packaging matrix for no reason.

**D5 — Staged enforcement: informational first, then fail.**
Sequence inside the rollout: (1) D1 engine exclusion plus the diff-cover step printing its report without `--fail-under` (informational) for one PR cycle; (2) flip to `--fail-under` at a modest target once the report shape is confirmed against real PRs; (3) seed and enforce floors; (4) release rehearsal by dispatch. The deliberate-red verification applies at each flip: a gate is trusted only after it has been observed to fail on a seeded violation (Coverage Policy Ratcheting, practice 6). The initial `--fail-under` target is set at flip time from the informational cycle's observed diff-coverage values — committed in the workflow file, adjustable by PR like any other policy.

**D6 — The policy echo becomes a policy statement.**
Replace the apology at .github/workflows/ci.yml:749 with text generated from what actually ran: the diff-cover verdict and the floor-check verdict are written into `coverage-policy.txt` so the uploaded artifact (.github/workflows/ci.yml:751-757) documents the enforced policy, not the absence of one.

## Risks / Trade-offs

- [gcov line attribution for templates/inline functions is link-order sensitive; floors flake] → 0.5-point slack in the floor comparison; floors round down at seeding; slack value lives in one shell variable, adjustable by PR.
- [diff-cover path mismatch between lcov `SF:` entries and git diff paths yields a vacuous 100% pass] → Verification task asserts the gate fails on a seeded uncovered-line PR before enforcement flips on; a vacuously green gate never reaches required status.
- [`--compare-branch=origin/master` drifts when master moves during a PR] → diff-cover uses the triple-dot merge-base comparison, matching PR semantics; R2's require-up-to-date setting bounds the drift window independently.
- [Floor file rots: modules added to the DAG but not the floor file] → The floor-check loop derives its module list from the floor file and fails if a `src/` module directory present in the manifest set has no floor line — adding a module forces a seeded floor entry.
- [Dispatch rehearsal of release-validation passes while a real tag run later fails on the artifact steps] → Accepted: the rehearsal scopes to the coverage threshold by design; packaging artifact verification is exercised only by real tags, and the guarded steps are skip-marked, not silently absent, in the dispatch run's log.
- [coverage job is not a required check, so the new gate does not yet block merges] → Accepted and explicit: this change makes the lane honest; R2 makes it binding. The job name stays stable so R2 can require it without rename churn.

## Migration Plan

1. PR 1: engine exclusion (D1) + `fetch-depth: 0` + diff-cover step in informational mode (D5 stage 1) + policy-text replacement (D6).
2. After the first post-merge master run: read per-module percentages, commit `.ci/coverage-floors.txt` (D3 seeding) and the floor-check loop, fail-below-floor active immediately (floors are by construction at current reality).
3. PR 3: flip diff-cover to `--fail-under` after the informational cycle; verify with a seeded uncovered-line PR that the gate goes red.
4. PR 4: release-validation `if:` widening + artifact-step guards (D4); run one dispatch rehearsal; record whether `src/app` clears 80% and file the gap issue if not.
Rollback at every step is a revert of that step's PR; reverting PR 2 or 3 returns the lane to report-only without touching the artifact pipeline.

## Open Questions

- Initial `--fail-under` value for diff-cover: chosen from the informational cycle's data at flip time (D5). 80 is the conventional starting point; the decision is deferred to observed PR reality, not committed here.
- Whether `src/libs` warrants a floor or an exemption line (it may be header-only/trivial); decided at seeding from what the extract loop actually measures.
- Where the release-validation 80%/`src/app` threshold migrates long-term — per-module floors at PR tier may supersede it entirely; out of scope here, noted for R8 consolidation.
