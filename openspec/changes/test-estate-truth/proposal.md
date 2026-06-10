# Change: test-estate-truth

## Why

The test estate reports green for work it does not do: `ctest -L soak` selects zero tests because the label is applied nowhere (`CMakeLists.txt:1021-1028` defers to a `cmake/SoakTestLabels.cmake` that does not exist), `--label-exclude soak` therefore excludes nothing, three integration sources are compiled into no target at all, the determinism suite is selected by no workflow, and the state hash it would compare is hardcoded to `Fast` at the library entry point (`engine/src/misc/dosbox_library.cpp:685`) — the oracle is weakest exactly where the product's determinism claim is strongest (audit-wiki/wiki/entities/Project Legends Test Suite.md; audit-wiki/wiki/entities/Determinism Oracle Weakness.md). This implements CI-THESIS.md recommendation R12 (M-6, T-1, T-5, T-6, T-7, T-8).

## What Changes

- Module-level CTest labels inside the monolithic suites (all ~4,600 unit tests currently share the single label `unit`), attached at `gtest_discover_tests` discovery time per the existing constraint note (`CMakeLists.txt:1023-1028`), with anchored regexes given CTest's substring `-L` semantics (audit-wiki/wiki/sources/Test Impact Analysis & Selection (2026-06).md, practice 1). Workflow gtest string filters (`sprint2-checks.yml:111`, `pal-ci.yml:162`) move to `ctest -L`, preserving the `--gtest_repeat=3` semantics of the asan-lifecycle step (`pal-ci.yml:213-214`) (Recommendation Review row M-6). The monolith binary split is a follow-on change, not this one.
- Nonzero-selection guard on every `ctest -L` step, new and existing: a `-L` invocation that selects zero tests fails the step. The repo already shipped one vacuous label (`soak`) — the guard makes that class of silent no-op impossible (Recommendation Review row T-1).
- A PR-tier determinism job selecting the existing `determinism` label (`engine/tests/determinism/CMakeLists.txt:33-45` — label and `test-determinism` target exist, no workflow runs them), with a canary proving the oracle can fail, and `dosbox_lib_get_state_hash` switched off hardcoded `HashMode::Fast` at the library entry point. Extending `Full` beyond conventional memory to VGA/devices (`engine/src/misc/state_hash.cpp:296-305`) is engine serialization work, scoped separately (Recommendation Review row T-5).
- Compile `tests/integration/test_dual_ffi.cpp` (viable); rewrite-or-delete the two bit-rotted orphans `test_context_synchronization.cpp` and `test_error_propagation.cpp` — they call a nonexistent `legends_init(handle)` and pass 3 args to the 4-parameter `legends_get_last_error` (`include/legends/legends_embed.h:644-649`) — with any removal recorded (Recommendation Review row T-7).
- Visible `stub` labels on the skip-stub integration tests (8 of 33 registered integration files are one-line `GTEST_SKIP()` stubs that report green), each tied to a tracked issue (Recommendation Review row T-6).
- Make the `soak` label real and run soak nightly: apply the label to the endurance tests, export the env gate (`GTEST_SKIP` unless `LEGENDS_SOAK_ENABLED=1`, `tests/integration/test_soak_endurance.cpp:76-83`) in the nightly job, and bound durations to the runner cap — the `test-soak` target's 46800 s timeout (`CMakeLists.txt:1037-1041`) exceeds the 6-hour GitHub-hosted cap (Recommendation Review row T-8).

## Capabilities

### New Capabilities

- `test-selection-integrity`: module-level labels, nonzero-selection guards on every label-selected step, anchored label regexes, and visible stub labels.
- `determinism-gating`: the PR-tier determinism job, the canary that proves the oracle can fail, and the library entry point's hash-mode switch.
- `test-registration-integrity`: every test source on disk is compiled into a CTest-visible target or consciously removed with the removal recorded.
- `soak-endurance`: a real `soak` label, the nightly soak job with its env gate exported, and durations bounded to the runner cap.

### Modified Capabilities

(none — the required-check set and lane tiers are owned by `ci-stabilization` via `master-ruleset-required-checks`; this change creates jobs and labels, it does not move gating policy. The `Deterministic Save/Load` requirement in `ci-stabilization` states the engine property; this change adds the CI machinery that exercises it, without altering that requirement.)

## Impact

- `CMakeLists.txt` — label attachment at the discovery calls (`CMakeLists.txt:819-824, 853-856, 886-888, 929-932, 1014-1019`), soak label application replacing the dead `SoakTestLabels.cmake` deferral (`CMakeLists.txt:1021-1028`), `test-soak` timeout (`CMakeLists.txt:1037-1041`), integration source list (`CMakeLists.txt:944-984`) for the orphan reconciliation.
- `engine/tests/determinism/CMakeLists.txt`, `engine/tests/CMakeLists.txt` — engine-side labels; determinism canary registration.
- `engine/src/misc/dosbox_library.cpp:685` — hash-mode parameter replacing hardcoded `HashMode::Fast`.
- `.github/workflows/ci.yml`, `pal-ci.yml`, `sprint2-checks.yml` — `ctest -L` swaps with guards; new PR-tier determinism job; new nightly soak job exporting `LEGENDS_SOAK_ENABLED`.
- `tests/integration/` — `test_dual_ffi.cpp` joins a target; the two rotted orphans are rewritten against the current API or deleted with the removal recorded; stub files gain the `stub` label.
- Dependencies: sequenced after `ci-stabilize-mandatory-lanes` (R1 green baseline); independent of the other R-series changes (CI-THESIS.md adoption order, step 8). Engine work explicitly out: extending `Full` hash coverage to VGA/devices belongs to Phase B serialization (`phase-b-serialization`).
- Downstream: module labels are the substrate for the deferred DAG-driven test selection (CI-THESIS.md, "Deferred — test selection (T-2)").
