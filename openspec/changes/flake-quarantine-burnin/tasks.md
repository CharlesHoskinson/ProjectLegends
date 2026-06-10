# Tasks: flake-quarantine-burnin

Independent of the other R-series changes (CI-THESIS.md adoption-order step 8). All lanes added here are non-gating; nothing below alters required checks.

## 1. Convention and retrofit

- [ ] 1.1 Document the quarantine convention in CONTRIBUTING.md (or tests/ README): mechanism choice (`DISABLED_` per test, `flaky` label per target — design D1), mandatory entry metadata (linked issue, owner, exit criterion), gate exclusion `ctest -LE flaky`, exit gate `--repeat until-fail:10`, and the rule that assertions are never deleted or weakened to stabilize a flake. Verify: a contributor can quarantine a test using only this document.
- [ ] 1.2 Retrofit `DISABLED_FullE2E` (tests/integration/test_ipc_integration.cpp:42): open the issue, name owner and exit criterion, link it in the comment — or decide to delete the test with the removal recorded on an issue. Verify: grep for `DISABLED_` finds no site without a linked issue.
- [ ] 1.3 Add `ctest -LE flaky` to every gating CTest invocation (.github/workflows/ci.yml:77,127,207,279,401,738; pal-ci.yml:51,79,119,265) so the label is exclusion-ready before anything carries it. Verify: each gating ctest step carries `-LE flaky` (or an equivalent label-exclude) and total selected-test count is unchanged while nothing is labeled.

## 2. Burn-in lane

- [ ] 2.1 Add a `burn-in` job to `.github/workflows/ci.yml` on the existing 03:00 cron (ci.yml:24-27) plus `workflow_dispatch`: build the dev configuration, run `ctest --repeat until-fail:5 -LE flaky` over the discovered suites, upload the CTest log/JUnit output as artifacts, non-gating. Start with `unit`-labeled targets if the full-suite repetition exceeds the nightly window (design open question); record the measured duration. Verify: dispatch run completes, artifacts present, a deliberately intermittent scratch test (e.g. fails on a time-seeded coin flip) is caught by the repetition.
- [ ] 2.2 Add the shuffle step to the same job: `legends_unit_tests --gtest_shuffle` with `--gtest_random_seed=0` (gtest picks and prints a time-based seed) and the seed extracted into the job summary. Verify: the seed appears in the log and re-running with `--gtest_random_seed=<seed>` reproduces the same order.
- [ ] 2.3 Add the quarantine-lane step to the same job: `ctest -L flaky --output-on-failure` plus a `GTEST_ALSO_RUN_DISABLED_TESTS=1` run of the gtest binaries that contain `DISABLED_` tests, `continue-on-error`, results uploaded. Emit the quarantine-size count (grep `DISABLED_` occurrences plus `flaky`-labeled target count) into the job summary. Verify: with task 1.2's disabled test present, the step runs it and the count is nonzero and correct.
- [ ] 2.4 Add a dispatch input to the burn-in job for exit qualification: a test-name filter that runs `ctest --repeat until-fail:10 -R <name>` (design D6). Verify: a dispatch run against a stable test passes 10/10 and the log shows ten executions.

## 3. Flake ledger

- [ ] 3.1 Add a scheduled ledger job: query the Actions API for runs with `run_attempt > 1` since the previous snapshot, fetch per-attempt job outcomes via the per-attempt endpoints, record run id, job names, and outcome flips. Publish as a workflow artifact; no commits (Recommendation Review G-9 binding modification). Verify: re-run a scratch workflow once; the next ledger snapshot contains that run with its attempt outcomes.
- [ ] 3.2 Document ledger triage in the convention doc: a job flipping outcome across snapshots gets a tracked issue; the issue feeds quarantine per section 1. Verify: triage path written next to the convention, not in a separate location.

## 4. SDL assertion decision (per test — design D7)

- [ ] 4.1 Establish the decision inputs for SDL2: what the PAL input contract documents for `poll` immediately after `initialize`; what SDL2 documents about events emitted on subsystem init; burn-in dispatch (task 2.4) of `SDL2BackendTest.InputSourceInitializes` with the strict `count == 0` assertion temporarily restored on a scratch branch, in both headless and windowed environments. Record the evidence on the decision issue. Verify: issue states the contract reading, the SDL2 documented behavior, and the burn-in outcomes.
- [ ] 4.2 Apply the SDL2 outcome to tests/unit/test_pal_sdl2_backend.cpp:142-145: if init events are legitimate — typed assertion that every event returned by the init-time poll is in the enumerated legitimate startup set (window/device lifecycle), failing on key/mouse/axis events; if not — restore `EXPECT_EQ(count, 0u)` and quarantine per section 1 with owner and exit criterion. Verify: the `(void)input->poll(events, 10)` discard is gone; the test asserts a property of the polled events; injected spurious input event fails it (typed branch) or the quarantine site carries metadata (restore branch).
- [ ] 4.3 Repeat 4.1 for SDL3 independently (different event model; host_clock_sdl3.cpp was separately rewritten in 8fdd4c6). Verify: same evidence recorded on its own issue; outcome justified against SDL3 behavior, not copied from SDL2.
- [ ] 4.4 Apply the SDL3 outcome to tests/unit/test_pal_sdl3_backend.cpp:144-148 under the same acceptance as 4.2. Verify: same checks as 4.2.
- [ ] 4.5 If the typed branch is taken for both backends and the legitimate sets coincide, factor the allowed-event-set predicate into tests/unit/test_utils/ (design open question); otherwise keep per-test enumerations. Verify: no divergent copies of the same set.

## 5. Exit path and bookkeeping

- [ ] 5.1 Exercise one full de-quarantine end to end on the first eligible entry: fix, `until-fail:10` dispatch evidence, marker removal and issue closure in one change. Verify: the convention's exit path has a worked example linked from the convention doc.
- [ ] 5.2 End-to-end check: nightly run shows burn-in repetition, logged shuffle seed, quarantine lane with size count, and ledger artifact; gating lanes all carry `-LE flaky`; grep finds no quarantine site without an issue and no `(void)...poll` discard in the SDL tests. Verify: one nightly cycle observed with all artifacts present.
- [ ] 5.3 Update audit-wiki (Project Legends Test Suite entity; Flaky-Test Detection & Quarantine applicability notes) and CI-THESIS.md R11 status once the lanes hold: the no-convention, no-burn-in, no-ledger facts and the relaxed-assertion finding need their resolution recorded. Verify: wiki pages cite the new workflow jobs and test assertions by path.
