# Tasks: test-estate-truth

## 1. Labels and guards (D1, D2)

- [ ] 1.1 Add module-level labels to the `legends_unit_tests` discovery path, aligned with `cmake/ModuleManifest.cmake` module prefixes (e.g. `mod_ipc`, `mod_pal`, `mod_core`), attached at `gtest_discover_tests` discovery time; verify with `ctest --print-labels` and `ctest -N -L '^mod_ipc$'` on a configured build
- [ ] 1.2 Add the nonzero-selection guard (helper script or CMake function: `ctest -N -L <expr>` count check, fail on zero) and wire it into `legends-test-unit`, `test-integration`, `test-abi`, `test-toolchain`, `test-determinism`, `test-soak` (CMakeLists.txt:894-906, 934-938, 1030-1041; engine/tests/CMakeLists.txt:149-153; engine/tests/determinism/CMakeLists.txt:41-45)
- [ ] 1.3 Anchor every `-L`/`--label-exclude` regex in custom targets and workflows (`-L '^unit$'` form); audit all existing expressions for substring over-match
- [ ] 1.4 Prove the guard fails closed: run a guard step against a label that matches nothing and confirm the step fails

## 2. Workflow filter conversion (D3)

- [ ] 2.1 Apply discovery-time labels covering the sprint2 selection (`MultiInstance*:Sprint2*:GslContract*:ContractGates*`) and the pal contract-gate selection (`ContractGate*`); convert `sprint2-checks.yml:111` and `pal-ci.yml:162` to guarded `ctest -L` invocations
- [ ] 2.2 Keep the asan-lifecycle step (`pal-ci.yml:213-214`) as a direct binary invocation with `--gtest_repeat=3`; add a filter-count check (`--gtest_list_tests` through the same filter, fail on zero matches)

## 3. Soak made real (D6)

- [ ] 3.1 Apply `LABELS "integration;soak"` to the soak endurance tests via a discovery-compatible mechanism; delete the dead `SoakTestLabels.cmake` deferral comment block (CMakeLists.txt:1021-1028); verify `ctest -N -L '^soak$'` is nonempty and `test-integration` now excludes the soak tests
- [ ] 3.2 Reduce the `test-soak` ctest `--timeout 46800` (CMakeLists.txt:1038) to a value inside the 6-hour runner cap
- [ ] 3.3 Add the nightly soak job: cron trigger, build, guarded `ctest -L '^soak$'` with `LEGENDS_SOAK_ENABLED=1` exported and `LEGENDS_SOAK_DURATION_HOURS` set so build + tests fit the runner cap
- [ ] 3.4 Make a fully-skipped soak selection fail the nightly job (parse the ctest/gtest skip counts; 100% skipped means the env gate regressed)

## 4. Registration integrity (D5)

- [ ] 4.1 Add `tests/integration/test_dual_ffi.cpp` to the `legends_integration_tests` source list (CMakeLists.txt:944-984); confirm it compiles and its tests register under `ctest -N`
- [ ] 4.2 Decide rewrite-vs-delete for `tests/integration/test_context_synchronization.cpp` against the current embed API; if rewritten, assert cross-context synchronization through real API calls (`legends_create`, 4-arg `legends_get_last_error`); if deleted, record file and reason in the commit
- [ ] 4.3 Same for `tests/integration/test_error_propagation.cpp` (scenario intent: error-code propagation fidelity across the FFI boundary)
- [ ] 4.4 Sweep `tests/**/*.cpp` against the CMake source lists; confirm no remaining uncompiled test source (fixture headers/utils excepted)
- [ ] 4.5 Add the `stub` label plus a tracked-issue reference in the `GTEST_SKIP()` message for each of the 8 skip-stub integration files; verify `ctest -N -L '^stub$'` lists exactly those tests

## 5. Determinism gate (D4)

- [ ] 5.1 Replace the hardcoded `HashMode::Fast` at `dosbox_lib_get_state_hash` (engine/src/misc/dosbox_library.cpp:685) with caller-selected mode, default preserving current behavior; coordinate the surface with `abi-parity-negative-gates` constraints
- [ ] 5.2 Switch the determinism harness to request `HashMode::Full`; raise the suite TIMEOUT (engine/tests/determinism/CMakeLists.txt:37) in the same commit if Full-mode hashing trips it
- [ ] 5.3 Add the canary test: mutate conventional memory (state `Full` provably hashes, engine/src/misc/state_hash.cpp:296-305) between two hash computations and assert the hashes differ
- [ ] 5.4 Add the PR-tier determinism job: build engine tests, guarded `ctest -L '^determinism$'`; required-check membership deferred to `master-ruleset-required-checks`
- [ ] 5.5 Negative-test the canary: temporarily blind the hash to the mutated region in a scratch build and confirm the canary fails

## 6. Verification

- [ ] 6.1 Full local pass: `legends-test-all`, `test-integration`, `test-soak` (short duration), `test-determinism` — all guards green, no empty selections
- [ ] 6.2 Confirm exclusion symmetry: count of tests in `-L '^integration$'` equals `test-integration` selection plus `-L '^soak$'` selection
- [ ] 6.3 CI run on a branch exercising sprint2-checks, pal-ci (incl. asan-lifecycle), the determinism job, and a dispatch of the nightly soak job
