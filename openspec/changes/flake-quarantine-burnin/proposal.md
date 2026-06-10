# Change: flake-quarantine-burnin

## Why

The repo's only response to flaky tests so far has been to delete the failing assertions: commits 911692f and 8fdd4c6 turned `EXPECT_EQ(count, 0u)` after `input->poll(events, 10)` into `(void)input->poll(events, 10)` in both SDL backend test files, so the tests now report green while verifying nothing about startup event behavior (tests/unit/test_pal_sdl2_backend.cpp:144, tests/unit/test_pal_sdl3_backend.cpp:147; audit-wiki/wiki/sources/Flaky-Test Detection & Quarantine (2026-06).md, practice 4). No quarantine convention exists — one ad-hoc `DISABLED_` with no ticket (tests/integration/test_ipc_integration.cpp:42), no `flaky` label, no burn-in lane, no flake ledger (Recommendation Review row G-9). This implements CI-THESIS.md recommendation R11.

## What Changes

- Adopt a quarantine convention: a flaky test is quarantined via `DISABLED_` prefix plus a linked GitHub issue, or a `flaky` CTest label excluded from gating lanes (`ctest -LE flaky`) and run in a non-blocking nightly lane. Quarantine entry requires an owner and an exit criterion; exit requires surviving `ctest --repeat until-fail:N`.
- Add a nightly burn-in lane to `.github/workflows/ci.yml` on the existing 03:00 cron (.github/workflows/ci.yml:24-27): `ctest --repeat until-fail:N` over the discovered suites plus `--gtest_shuffle` with a logged `--gtest_random_seed` on `legends_unit_tests` — active flake detection that does not depend on the missing rerun history (Flaky-Test Detection & Quarantine, practice 1).
- Keep a flake ledger: a scheduled job snapshots `run_attempt > 1` runs and which jobs flipped between attempts, published as workflow artifacts — via artifacts/issues, not bot commits (Recommendation Review row G-9 binding modification).
- Resolve the relaxed SDL tests per test, not as a blanket restore: for each of `tests/unit/test_pal_sdl2_backend.cpp` and `tests/unit/test_pal_sdl3_backend.cpp`, decide whether the deleted `count == 0` assertion was a real invariant. The 911692f comment claims init events are legitimate SDL behavior; where that holds, the original assertion was wrong-by-spec and is replaced with a typed assertion (every event polled at init is in the legitimate startup set); where it does not hold, the strict assertion is restored and the test quarantined with owner and exit criterion. Never delete an assertion to make CI pass.

## Capabilities

### New Capabilities

- `flake-management`: the quarantine convention (entry metadata, gate exclusion, non-blocking quarantine lane, exit criterion), the nightly burn-in lane, the run-attempt flake ledger, and the restored-or-retyped SDL startup assertions.

### Modified Capabilities

(none — gating-tier membership and required checks are owned by `ci-stabilization` and the `master-ruleset-required-checks` change; this change defines how individual flaky tests leave and re-enter gates, not which lanes gate)

## Impact

- `.github/workflows/ci.yml` — new nightly burn-in job and quarantine-lane step on the existing cron; new scheduled flake-ledger job using the Actions per-attempt API.
- `tests/unit/test_pal_sdl2_backend.cpp`, `tests/unit/test_pal_sdl3_backend.cpp` — `InputSourceInitializes` assertion decision (typed assertion or restore-and-quarantine).
- `tests/integration/test_ipc_integration.cpp:42` — the existing bare `DISABLED_FullE2E` is retrofitted to the convention (linked issue, owner, exit criterion).
- `CMakeLists.txt` / CONTRIBUTING — `flaky` label wiring where the label option is used; the convention documented where contributors find it.
- Dependencies: independent of the other R-series changes (CI-THESIS.md adoption-order step 8); the burn-in lane reuses the lane structure consolidated by `consolidate-workflows-policy` if that lands first, but does not require it. The `--gtest_repeat=3` asan-lifecycle step (.github/workflows/pal-ci.yml:208-214) is the existing miniature of the burn-in pattern this generalizes.
- Downstream: `test-estate-truth` (R12) label discipline applies to the `flaky` label (nonzero-selection guard); any future test-impact selection (deferred T-2) depends on the flake containment this change provides.
