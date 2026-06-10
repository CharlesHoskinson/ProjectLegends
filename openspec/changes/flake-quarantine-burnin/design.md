# Design: flake-quarantine-burnin

## Context

The suite has no mechanism between "test gates" and "test gone". Commits 911692f ("Relax SDL backend startup event tests") and 8fdd4c6 ("Stabilize optional SDL backend CI") stabilized CI by deleting assertions: in `tests/unit/test_pal_sdl2_backend.cpp` (line 144) and `tests/unit/test_pal_sdl3_backend.cpp` (line 147), `EXPECT_EQ(count, 0u)` after `input->poll(events, 10)` became `(void)input->poll(events, 10)` — the tests still run and report green while the property they checked (no spurious events queued at init) is untested on every backend (audit-wiki/wiki/sources/Flaky-Test Detection & Quarantine (2026-06).md, practice 4). 8fdd4c6 also rewrote `src/pal/sdl2/host_clock_sdl2.cpp` and `host_clock_sdl3.cpp`, so a real product-side race may have been half-fixed without a test to confirm it.

The rest of the flake apparatus is absent: one ad-hoc `DISABLED_` with no ticket (`tests/integration/test_ipc_integration.cpp:42`), no `flaky` label, no burn-in lane, no rerun ledger. The collected CI run history could not see reruns because the default Actions list endpoint returns latest-attempt records only; per-attempt queries keyed on `run_attempt` recover them (Flaky-Test Detection & Quarantine, practice 2 conflict note). The existing primitives are sufficient: `gtest_discover_tests` attaches labels per target (CMakeLists.txt:819-824 and siblings), `ctest --repeat until-fail:N` is the burn-in mode, `--gtest_shuffle` with a logged seed reproduces order-dependence, and the asan-lifecycle step (`pal-ci.yml:208-214`, `--gtest_repeat=3` over `ContractGate_Lifecycle*`) is already a miniature burn-in probe. The 03:00 nightly cron exists (`.github/workflows/ci.yml:24-27`).

Binding modifications from the adversarial review (audit-wiki/wiki/syntheses/Recommendation Review (2026-06).md row G-9): decide per test whether `count==0` was a real invariant — the 911692f comment claims init events are legitimate SDL behavior, which would make the original assertion wrong-by-spec, not flaky; ledger via artifacts/issues, not bot commits.

## Goals / Non-Goals

**Goals:**
- One documented quarantine convention with entry metadata (issue, owner, exit criterion), gate exclusion, continued non-blocking execution, and a statistical exit gate.
- A scheduled burn-in lane that detects flakes actively, without rerun history.
- An ongoing flake ledger from per-attempt Actions data, retained as artifacts.
- The SDL startup-event property is tested again — by the correct assertion, decided per test.

**Non-Goals:**
- Gating-tier policy and required checks (`ci-stabilize-mandatory-lanes`, `master-ruleset-required-checks`).
- Auto-detection-and-suppression services (the Slack model) — at this repo's scale the workflow is a convention, not a service.
- In-pipeline retries on gating lanes (`--repeat until-pass`) — see D5.
- Per-module label taxonomy and nonzero-selection guards in general (`test-estate-truth`, R12); this change guards only the `flaky` label it introduces.
- Fixing the underlying SDL/clock races; this change restores honest signal about them.

## Decisions

**D1 — Dual quarantine mechanism: `DISABLED_` for single tests, `flaky` CTest label for whole suites; both with mandatory entry metadata.**
GoogleTest `DISABLED_` is the per-test tool: still compiled (no rot), counted in a banner, runnable in a scheduled lane via `--gtest_also_run_disabled_tests`, greppable as a quarantine-size metric. The `flaky` CTest label is the per-target tool: `gtest_discover_tests` labels apply at target granularity, so a single flaky test in `legends_unit_tests` cannot be labeled alone — but an environment-conditioned suite can be excluded wholesale with `ctest -LE flaky` and run with `ctest -L flaky` in a non-blocking step. Entry metadata is uniform: a comment at the quarantine site linking a GitHub issue that names the owner (blame-derived) and the exit criterion. Rationale: both primitives are native to the stack (Flaky-Test Detection & Quarantine, practice 3); the granularity mismatch is real and forcing one mechanism would either explode targets or quarantine too coarsely. Alternative rejected: result-filtering (suppress failures in reporting) — Slack rolled this back because failures leaked and state changes became invisible.

**D2 — Quarantined tests keep running, off the critical path.**
A non-blocking nightly step runs `ctest -L flaky` and the disabled set (`GTEST_ALSO_RUN_DISABLED_TESTS=1`), uploading results as artifacts. Quarantine means removing from the gate, not from existence: continued execution generates the evidence the exit gate needs and catches the moment a flaky test becomes a hard failure (practice 3, Google's reliability-suite variant). The step reports failure status without failing the workflow (`continue-on-error` or equivalent), because a red quarantine lane is information, not a gate.

**D3 — Burn-in lane: `ctest --repeat until-fail:N` plus shuffle, on the existing 03:00 cron.**
A nightly job builds the dev configuration and runs (a) `ctest --repeat until-fail:5 -LE flaky` over the discovered suites, and (b) `legends_unit_tests --gtest_shuffle` with the seed logged, so order-dependence reproduces deterministically. N=5 nightly is the floor; N=10 is the on-demand dispatch value for exit qualification (D6). Rationale: detection must not wait for the rerun history the repo does not collect; deterministic re-execution is the standard substitute (practice 1). The lane generalizes the asan-lifecycle probe from one gtest filter to the whole suite via CTest. Alternative rejected: burn-in on PRs — repetition multiplies PR latency by N and the cron already exists.

**D4 — Flake ledger: scheduled snapshot of `run_attempt > 1` data into workflow artifacts.**
A scheduled job queries the Actions API per-attempt endpoints for runs with `run_attempt > 1` since the last snapshot, records which jobs flipped between attempts, and uploads the result as a workflow artifact; recurring flips get a tracked issue. Collection must be ongoing — the default retention window makes retrospective mining impossible (practice 2). G-9 binding modification: artifacts and issues, not bot commits — a bot committing ledger updates to master would contend with the ruleset work and pollute history. Attempt counts are the lagging indicator; the burn-in lane (D3) is the active detector. Alternative rejected: relying on rerun mining alone — GitHub's own baseline caught 25% of flaky failures this way.

**D5 — No `until-pass` retries on gating lanes.**
Gating lanes keep hard failure semantics. The sources' reconciliation: retries are legitimate as a detector feeding a ledger, illegitimate as terminal mitigation; for Legends, `until-pass:2` would be acceptable only with per-event flake logging, and the simpler discipline — hard failure plus quarantine plus ledger — achieves the same containment without teaching developers to ignore red (practice 6 conflict note, Micco's criticism of mark-as-flaky).

**D6 — Exit is statistical: survive `until-fail:10`, then de-quarantine and close the issue.**
A workflow-dispatch input on the burn-in lane (or a local run) executes the candidate test with `ctest --repeat until-fail:10` (`-R` selecting the test, label/prefix temporarily lifted on the branch). Ten consecutive passes is the documented re-qualification gate (practice 5); the de-quarantine commit removes the `DISABLED_` prefix or label and closes the linked issue in the same change. Slack's rot warning sets the review cadence: quarantined entries older than a quarter are re-triaged — fix, delete-with-record, or re-justify.

**D7 — SDL assertion decision is per test, with a stated decision criterion.**
For each backend's `InputSourceInitializes`, the question is whether "no events at init" was ever a contract of the PAL input interface or an accident of the environments the test first ran in. Decision procedure: (a) check what the PAL interface contract documents for `poll` immediately after `initialize`; (b) check SDL2/SDL3 documented startup behavior (window/device add events on init are documented SDL behavior — the 911692f comment's claim); (c) run the strict assertion under the burn-in lane in a headless and a windowed environment. Outcomes: if init events are legitimate for that backend, the original `count == 0` was wrong-by-spec — replace the deleted assertion with a typed assertion that every event returned by the init-time poll is in the legitimate startup set (window/device lifecycle events), so spurious input events (key, mouse, axis) still fail; if init events are not legitimate, restore `EXPECT_EQ(count, 0u)` and quarantine per D1 with owner and exit criterion. The two backends may resolve differently — SDL2 and SDL3 have different event models and separate host-clock rewrites in 8fdd4c6. Never delete an assertion to make CI pass; this change ends with the property tested in both files, under whichever assertion is correct. Alternative rejected: blanket restore-and-quarantine of both — if init events are wrong-by-spec for neither backend, that quarantines two correct-behavior failures forever and the exit criterion can never be met.

**D8 — Retrofit the existing ad-hoc quarantine.**
`DISABLED_FullE2E` (`tests/integration/test_ipc_integration.cpp:42`) predates the convention: no issue, no owner, no exit criterion. It gets the entry metadata or a decision to delete-with-record; conventions with grandfathered exceptions do not hold.

## Risks / Trade-offs

- [Quarantine becomes a roach motel — tests enter, never leave] → Exit criterion is mandatory at entry; the quarantine lane keeps generating evidence; the grep/banner count is reported per burn-in run; quarterly re-triage per D6. Spotify's finding: visibility alone reduced flakiness — publishing the count is itself a control.
- [Burn-in lane N=5 misses low-probability flakes] → The ledger (D4) catches what repetition misses, from real-traffic reruns; N is a dial — raise it if the lane runs well under its timeout. Detection layers are complementary by design.
- [Burn-in lane itself flakes red and gets ignored] → It is non-gating by design; its output is a report consumed by triage, not a checkmark. Recurring reds become quarantine entries with owners — the lane's failures feed the mechanism rather than eroding it.
- [`flaky` label at target granularity over-quarantines: one flaky test mutes a whole suite from gates] → Prefer `DISABLED_` for single tests; label use is reserved for environment-conditioned suites where the whole target's verdict is untrustworthy. The label is excluded from gates only where applied, and `test-estate-truth`'s nonzero-selection guard keeps it honest.
- [Ledger job depends on API pagination/retention quirks] → Snapshot frequency beats retention windows (weekly is sufficient against a three-month window); the job is additive observability — its failure loses ledger continuity, never test signal.
- [Typed assertion is written too loosely and becomes the relaxation antipattern with extra steps] → The typed assertion must enumerate the allowed event types and fail on anything else; "any event is fine" is exactly 911692f and is rejected by review. The spec scenario pins this: spurious input events fail.
- [Shuffle seed surfaces order-dependent failures unrelated to SDL] → Intended. Each is a real defect in test isolation; the logged seed makes it reproducible, and it enters quarantine like any other flake.

## Migration Plan

1. Document the convention (CONTRIBUTING or tests/ README): entry metadata, mechanism choice (D1), exit gate (D6). Retrofit `DISABLED_FullE2E` (D8).
2. Add the burn-in job to `ci.yml` on the existing cron: `until-fail:5 -LE flaky`, shuffle with logged seed, quarantine-lane step (D2/D3), artifacts uploaded. Non-gating from day one.
3. Add the ledger job (D4): scheduled `run_attempt` snapshot to artifacts.
4. Run the SDL decision procedure (D7) per backend using the burn-in lane; land the typed assertion or restore-and-quarantine per outcome.
5. First de-quarantine exercised end to end (any entry that passes `until-fail:10`), proving the exit path.
Rollback: every piece is additive — removing the burn-in or ledger job restores the status quo; the SDL assertion change reverts independently per file.

## Open Questions

- Burn-in scope vs. runner budget: whether `until-fail:5` over all discovered suites (including `legends_integration_tests` at TIMEOUT 60 per test) fits the nightly window, or the first iteration restricts repetition to `unit`-labeled targets and widens after timing data exists.
- Whether the quarantine-size count should eventually ratchet (fail the burn-in lane if quarantine grows) — deferred until the convention has a population to measure.
- Where the typed startup-event set lives if both backends need it: per-test enumeration vs. a shared helper in `tests/unit/test_utils/` — decided at implementation by whether the legitimate sets actually coincide.
