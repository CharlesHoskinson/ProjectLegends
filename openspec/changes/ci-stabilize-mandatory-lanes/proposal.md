# Change: ci-stabilize-mandatory-lanes

## Why

The sanitizer and fuzz lanes produce no gating signal: every sampled execution of all four sanitizer legs and the fuzz job failed (audit-wiki/wiki/entities/Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism).md), TSan and MSan are muted by `allow_failure: true` with exit plans living only in YAML comments (.github/workflows/ci.yml:354-356, 362-367), and dependency-scan is double-muted by `|| true` plus `continue-on-error` (.github/workflows/ci.yml:784-787). This implements CI-THESIS.md recommendation R1, the prerequisite for binding merges to green (R2): lanes must be able to fail honestly before their verdicts can mean anything.

## What Changes

- Triage the enforced ASan/UBSan legs (.github/workflows/ci.yml:343-350) and the fuzz job (.github/workflows/ci.yml:478-578) to deterministic green — fix root causes; never delete assertions or mute lanes to get there.
- Add a checked-in `tsan-suppressions.txt` with one issue-linked entry per known race (engine `g_active_instance`, `CrashBreadcrumb::add()`, intentional wrong-thread tests — .github/workflows/ci.yml:351-354), wired via `TSAN_OPTIONS=suppressions=`, then **BREAKING**: drop `allow_failure: true` from the TSan matrix entry (.github/workflows/ci.yml:361) so TSan gates on new races.
- **BREAKING**: retire the MSan matrix entry (.github/workflows/ci.yml:368-373). It links stock libc++, so test executables crash on startup by construction and the leg verifies nothing (audit-wiki/wiki/sources/Sanitizer Lane Strategy (2026-06).md, section 4). Retirement carries a tracked re-entry issue whose condition is an MSan-instrumented libc++ — per Recommendation Review row G-7's no-demotion-without-exit rule. No `msan` CMake preset is ever added.
- Fix the broken osv-scanner invocation (`--lockfile cmake/dependencies.cmake` is not a format osv-scanner parses, .github/workflows/ci.yml:784) before removing `|| true` and `continue-on-error` — unmuting without fixing makes a permanently red nightly (Recommendation Review row G-7).
- Establish the demotion rule as a spec requirement: no lane is demoted (allow-failure, muted, retired, assertion-relaxed) without a tracked issue stating its exit criterion.

## Capabilities

### New Capabilities

(none)

### Modified Capabilities

- `ci-stabilization`: the Optional Validation Lanes requirement currently classes sanitizers, fuzzing, and dependency scanning as "clearly optional" (openspec/specs/ci-stabilization/spec.md). This change re-tiers them: sanitizer (ASan/UBSan/TSan) and fuzz lanes become enforced-and-green at their existing PR/master trigger tier, MSan is retired with a tracked re-entry condition, dependency-scan becomes enforceable on its nightly/dispatch tier, and a lane-demotion requirement is added.

## Impact

- `.github/workflows/ci.yml` — `sanitizers` job (matrix entries, TSAN_OPTIONS, symbolizer install), `fuzz` job, `dependency-scan` job.
- New repo file `tsan-suppressions.txt`; `tsan` preset in `CMakePresets.json` gains the same `suppressions=` option so local runs and CI agree on the known-race set.
- Tracker: one issue per TSan suppression entry; one MSan re-entry issue; one issue per remaining red root cause found during triage.
- Downstream: CI-THESIS.md R2 (branch ruleset) is sequenced strictly after this change; R5 presets exclude `msan`.
