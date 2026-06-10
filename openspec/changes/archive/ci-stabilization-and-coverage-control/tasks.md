## 1. Baseline Evidence

- [x] 1.1 Confirm latest remote CI runs and commit SHAs.
- [x] 1.2 Record failing workflows and first root-cause failures.
- [x] 1.3 Confirm local branch state relative to `origin/master`.

## 2. CI Failure Fixes

- [x] 2.1 Replace raw PAL SDL `gsl-lite` includes/usages with the project GSL bridge.
- [x] 2.2 Add missing Linux SDL3 X11 dependency `libxss-dev`.
- [x] 2.3 Remove tracked `.claude/worktrees/*` gitlinks and ignore local worktrees.
- [x] 2.4 Add documented MSVC test-only `/wd4834` containment while preserving production strict warnings.

## 3. Determinism

- [x] 3.1 Reproduce the save/load determinism failure locally.
- [x] 3.2 Add diagnostics that identify immediate restore mismatches and component-level divergence.
- [x] 3.3 Serialize and restore missing hash-relevant lightweight context metadata.
- [x] 3.4 Synchronize CPU bridge globals with context CPU state during execution, init, reset, save, and load.
- [x] 3.5 Verify all determinism tests pass.

## 4. CI Topology

- [x] 4.1 Keep normal push/PR CI focused on Linux headless, Windows headless, ABI, coverage, Sprint 2 checks, and Module DAG architecture checks.
- [x] 4.2 Move SDL/PAL, macOS, sanitizer, fuzz, TLA+, dependency scan, and duplicate Module DAG full builds to optional scheduled/manual/tag-oriented lanes.
- [x] 4.3 Label optional jobs clearly.

## 5. Coverage

- [x] 5.1 Make coverage independent from optional backend lanes.
- [x] 5.2 Upload `coverage.filtered.info` and policy text as artifacts.
- [x] 5.3 Document coverage as report-only with no enforced percentage threshold.
- [x] 5.4 Skip Codecov upload when no token is configured.

## 6. Verification

- [x] 6.1 `cmake --preset dev`
- [x] 6.2 `cmake --build --preset dev`
- [x] 6.3 `ctest --test-dir build/dev --output-on-failure`
- [x] 6.4 `build/dev/legends_abi_test.exe`
- [x] 6.5 `build/dev/engine/tests/determinism/aibox_determinism_tests.exe --gtest_brief=1`
- [x] 6.6 `python scripts/check_conflict_markers.py --path .`
- [x] 6.7 `python scripts/check_capability_matrix.py --repo .`
- [x] 6.8 `python scripts/graphify_projectlegends.py update --repo . --source-only`
- [x] 6.9 `python scripts/check_graphify_enrichment.py --repo . --overlay graphify-out/projectlegends-enrichment.json --strict --strict-tests fail --allow-missing-graphify`
- [x] 6.10 `git diff --check`
