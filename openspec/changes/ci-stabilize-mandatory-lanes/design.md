# Design: ci-stabilize-mandatory-lanes

## Context

The `sanitizers` job (.github/workflows/ci.yml:328-401) runs a four-way matrix (`address`, `undefined`, `thread`, `memory`) on PRs, pushes to master, nightly, and dispatch. All four legs failed every sampled execution (audit-wiki/wiki/entities/Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism).md). TSan and MSan carry `allow_failure: true` (.github/workflows/ci.yml:361, 373) fed into `continue-on-error` (.github/workflows/ci.yml:332); their exit plans are YAML comments (.github/workflows/ci.yml:354-356, 366-367). The fuzz job (.github/workflows/ci.yml:478-578) is enforced and red. `dependency-scan` (.github/workflows/ci.yml:769-794) is muted twice: `|| true` on both scanner invocations (.github/workflows/ci.yml:784-786) and `continue-on-error: true` (.github/workflows/ci.yml:787). Researched practice for each lane: audit-wiki/wiki/sources/Sanitizer Lane Strategy (2026-06).md. Binding modifications from the adversarial review: audit-wiki/wiki/syntheses/Recommendation Review (2026-06).md rows G-1, G-7.

## Goals / Non-Goals

**Goals:**
- ASan, UBSan, and fuzz legs pass deterministically at their existing trigger tier, with root causes fixed or quarantined under tracked issues.
- TSan gates on new races: known races suppressed via a checked-in, issue-linked `tsan-suppressions.txt`; `allow_failure` removed.
- MSan leg removed, with a tracked issue stating the re-entry condition (MSan-instrumented libc++).
- `dependency-scan` invocation produces real results; mutes removed once the invocation works.
- Lane demotion without a tracked exit criterion becomes a spec violation, not a YAML edit.

**Non-Goals:**
- Branch ruleset / required checks (CI-THESIS.md R2; sequenced strictly after this change).
- Preset migration (R5), corpus persistence and nightly fuzz funding (R10), flake quarantine convention (R11) — this change only brings the existing fuzz smoke runs to green.
- Fixing the suppressed races themselves (Sprint 7 REQ-TH-004 work; this change converts that work into suppression-entry burndown).
- Collapsing the `address`/`undefined` legs into one combined build (an R5/R8 concern).

## Decisions

**D1 — TSan: suppress-to-green, then enforce; not defer-to-red, not fix-everything-first.**
A `tsan-suppressions.txt` at repo root, wired via `TSAN_OPTIONS=suppressions=` in the `thread` matrix env (.github/workflows/ci.yml:360), one entry per known race, each preceded by a comment linking its tracking issue. Then delete `allow_failure: true` (.github/workflows/ci.yml:361). Rationale: the Firefox/Chromium pattern — a green enforced lane catches regressions; a red advisory lane is read by nobody (Sanitizer Lane Strategy, sections 2-3). Alternative rejected: keeping `allow_failure` until all races are fixed repeats the current state (exit plan deferred indefinitely in a comment). The three known race families map directly: `race:g_active_instance` (globals need only the variable name), a function-frame entry for `CrashBreadcrumb::add()`, and the intentional wrong-thread tests gated in code (`#if defined(__SANITIZE_THREAD__)`/feature-detect) or excluded by CTest label in the tsan leg — suppressing deliberate races would mask real ones in the same paths.

**D2 — Symbolizer is a hard dependency of D1.**
Runtime suppressions silently fail to match without in-process symbolization; the job installs only `clang-18 libc++-18-dev libc++abi-18-dev` (.github/workflows/ci.yml:379-381). Add `llvm-18` so `llvm-symbolizer` is on PATH. Without this, the lane would go green for the wrong reason or stay red with suppressions apparently ignored (Sanitizer Lane Strategy, section 3).

**D3 — Local/CI agreement: the `tsan` preset grows the same suppressions option.**
`CMakePresets.json` `tsan` test environment gains `TSAN_OPTIONS=suppressions=${sourceDir}/tsan-suppressions.txt` so a local run reproduces CI's known-race set. Alternative rejected: CI-only wiring — developers would see local reds CI doesn't, re-creating the divergence this audit exists to close.

**D4 — MSan: retire now; re-entry is a tracked condition, not a comment.**
Delete the `memory` matrix entry (.github/workflows/ci.yml:362-373). The leg links stock libc++, crashes on startup by construction, and verifies nothing while burning a runner per PR (Verification Lanes, MSan section). File the re-entry issue before deleting: condition is an MSan-instrumented libc++ (and instrumented SDL/engine dependency surface), placement on re-entry is nightly-only. Rationale: OSS-Fuzz ships address+undefined by default and treats memory as opt-in for projects that funded the instrumentation; Chromium keeps MSan off the pre-commit set even with prebuilt instrumented libraries (Sanitizer Lane Strategy, section 4). Alternative rejected: building instrumented libc++ now — the vendored DOSBox-X engine and SDL surface all need the same treatment; that is real work with no current owner, and a lane that cannot run is not coverage being lost. Per Recommendation Review G-7/M-2: no `msan` preset is added by any later preset work.

**D5 — Dependency-scan: fix the invocation before unmuting.**
`osv-scanner --lockfile cmake/dependencies.cmake` (.github/workflows/ci.yml:784) is bogus — that file is not a lockfile format osv-scanner parses, so the first command has never produced a result. Replace with what the tool supports: recursive scan of the vendored trees (`-r engine/` already present at line 786) plus vendored-directory scanning for the remaining vendored code; emit JSON output so the existing artifact upload (.github/workflows/ci.yml:789-794) captures findings. Rehearse via `workflow_dispatch` (already in the job's `if:`, line 773); triage findings into issues; then remove `|| true` and `continue-on-error: true` in the same PR that proves a green dispatch run. Rationale (Recommendation Review G-7): unmuting first manufactures a permanently red nightly, which is the failure mode this whole change exists to end. The job keeps its nightly/dispatch tier; its `Optional` display name (line 770) is dropped because the name must not promise non-enforcement the spec no longer grants.

**D6 — ASan/UBSan/fuzz triage: root cause or tracked quarantine, never assertion deletion.**
Reproduce each red locally (`asan` preset, `fuzz-quick` target), fix what is fixable, and quarantine the rest under issue-linked `DISABLED_` (the repo's one existing precedent: `tests/integration/test_ipc_integration.cpp:42`) so the lane itself is deterministically green. Constraint inherited from CI-THESIS.md R11: a deleted assertion is a forbidden fix. Fuzz crashes found during triage get reproducer files attached to their issues; corpus/artifact persistence mechanics stay in R10.

**D7 — Demotion rule lives in the spec, not in culture.**
Add a requirement to the `ci-stabilization` capability: any demotion (allow-failure, mute, retirement, trigger-tier narrowing, assertion relaxation) MUST carry a tracked issue stating the exit criterion. This is the generalization of what went wrong in the 2026-06-08 demotion (gates removed to achieve green; audit-wiki/wiki/concepts/Quality Gate Demotion (2026-06-08).md) and is stated verbatim in R1: "No lane is ever demoted again without a tracked exit criterion."

## Risks / Trade-offs

- [TSan is inherently intermittent; a pre-existing race may surface only occasionally after enforcement] → Each new detection produces a suppression entry plus issue in a small PR — never a revert to `allow_failure` (Sanitizer Lane Strategy, section 5).
- [Over-broad suppressions mask new races] → Hygiene policy in the file header: one entry per race or common root cause, comment with issue link mandatory, no module-wide `race:` globs; reviewed like code (Chromium practice, Sanitizer Lane Strategy, section 3).
- [Suppression symbolization slows the TSan leg] → Acceptable inside the existing `timeout-minutes: 20` (.github/workflows/ci.yml:331); if breached, the entry count is the burndown metric, not the timeout.
- [ASan/UBSan reds may trace to deep engine bugs not fixable in this change] → Quarantine path in D6 keeps the lane green without losing the record; each quarantined test carries an issue.
- [osv-scanner finds real CVEs in vendored DOSBox-X on first honest run] → Findings become issues before unmute; the gate's first enforced run starts from a triaged baseline.
- [Retiring MSan reads as losing coverage] → It cannot regress and cannot improve today; the re-entry issue plus the spec's demotion rule make the retirement auditable rather than silent.

## Migration Plan

1. Land suppression file + symbolizer + preset wiring with TSan still allow-failure; confirm via dispatch that the leg passes with suppressions active.
2. Same PR or immediate follow-up: drop `allow_failure` (TSan), delete the MSan entry (re-entry issue already filed).
3. ASan/UBSan/fuzz triage PRs as roots are found; lane is green when the last lands.
4. Dependency-scan: fix invocation → green dispatch run → remove mutes.
Rollback for any step is a revert of that step's PR; the suppression file degrades gracefully (extra entries are inert once races are fixed).

## Open Questions

- Issue tracker granularity for the suppression entries: one issue per race family vs. one Sprint-7 umbrella with checkboxes. Default: one per family (matches "delete suppression entry" = "close issue").
- Whether the wrong-thread tests are excluded via compile-time guard or a `tsan-excluded` CTest label — decided during triage by whichever keeps the non-TSan lanes running them unchanged.
