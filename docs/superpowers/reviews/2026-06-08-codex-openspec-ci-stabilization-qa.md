# 2026-06-08 Codex OpenSpec CI Stabilization QA

## 1. OpenSpec Change Path

`openspec/changes/ci-stabilization-and-coverage-control`

## 2. Gate Status Table

| Gate | Name | Status | Evidence |
|---|---|---|---|
| 1 | Baseline Evidence | PASS | Remote failures were confirmed as stale against `757255e`; local tree is ahead/dirty and needs a new push for remote proof. |
| 2 | SDL/PAL Compile Hygiene | PASS | Raw PAL SDL `gsl-lite` includes/usages were replaced with the project GSL bridge and Linux SDL3 X11 dependency coverage was added. |
| 3 | Repository Hygiene | PASS | Tracked `.claude/worktrees/*` gitlinks were removed from the index and `.claude/worktrees/` is ignored; `git submodule status` exits cleanly. |
| 4 | Windows Test Warning Policy | PASS | Production strict warnings remain intact; MSVC `/wd4834` is scoped to test targets and documented as follow-up debt. |
| 5 | Determinism | PASS | `DeterminismTest.SaveLoadWithLongerExecution` was reproduced, fixed, and the full determinism binary now passes. |
| 6 | CI Topology | PASS | Optional backend/research lanes are scheduled/manual/tag/path oriented; primary push/PR checks remain focused. |
| 7 | Coverage Policy | PASS | Coverage is report-only, independent from optional backend lanes, and publishes `coverage.filtered.info` plus policy text when generated. |
| 8 | Local Verification | PASS | Full local build/test and architecture checks passed. |

## 3. Files Changed

Primary areas changed:

- `.github/workflows/ci.yml`
- `.github/workflows/module-dag.yml`
- `.github/workflows/pal-ci.yml`
- `.gitignore`
- `CMakeLists.txt`
- `CIFix.md`
- `engine/include/dosbox/cpu_bridge.h`
- `engine/include/dosbox/engine_state.h`
- `engine/src/cpu/cpu.cpp`
- `engine/src/misc/cpu_bridge.cpp`
- `engine/src/misc/dosbox_library.cpp`
- `engine/tests/determinism/determinism_harness.h`
- `src/pal/sdl2/*`
- `src/pal/sdl3/*`
- `openspec/changes/ci-stabilization-and-coverage-control/*`

## 4. Commands Passed

- `openspec.cmd validate ci-stabilization-and-coverage-control --strict --json`
- `openspec.cmd show ci-stabilization-and-coverage-control --json`
- `rg -n -P "<gsl-lite/gsl-lite\\.hpp>|(?<!legends::)\\bgsl::" src\pal` returned no matches
- `git submodule status`
- `python scripts/check_conflict_markers.py --path .`
- `python scripts/check_capability_matrix.py --repo .`
- `python scripts/graphify_projectlegends.py update --repo . --source-only`
- `python scripts/graphify_projectlegends.py runtimehost-bypasses --repo .`
- `python scripts/check_graphify_enrichment.py --repo . --overlay graphify-out/projectlegends-enrichment.json --strict --strict-tests fail --allow-missing-graphify`
- `cmake --preset dev`
- `cmake --build --preset dev`
- `build/dev/legends_abi_test.exe`
- `build/dev/engine/tests/determinism/aibox_determinism_tests.exe --gtest_brief=1`
- `ctest --test-dir build\dev --output-on-failure` with `4497` passed, `43` skipped, `0` failed

## 5. Commands Failed Or Blocked

- Remote GitHub Actions validation is blocked until this local work is committed and pushed.
- `scripts/__pycache__/` is local generated Python cache and should remain untracked.

## 6. Remaining CI Debt

- Push the branch and verify the new remote Linux, Windows, Sprint 2, Module DAG, and coverage runs.
- Replace MSVC test-target `/wd4834` containment with explicit assertions/consumption in tests when convenient.
- Establish a measured coverage baseline before enforcing any percentage threshold.
- Continue hardening optional sanitizer, fuzz, TLA+, PAL, SDL, and macOS lanes on scheduled/manual runs.

## 7. Top Five Follow-Up Audit Targets

1. Confirm GitHub Actions runs against the new pushed commit and no longer reports stale `757255e` failures.
2. Check that coverage artifacts include both `coverage.filtered.info` and the policy text.
3. Inspect optional workflow labels and triggers for accidental required-check regressions.
4. Audit the save-state V5 context metadata fields for ABI/layout stability.
5. Track removal of the temporary MSVC `/wd4834` containment once test call sites are cleaned individually.
