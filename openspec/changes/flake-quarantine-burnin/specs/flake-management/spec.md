# flake-management

## ADDED Requirements

### Requirement: Quarantine Convention
A flaky test SHALL be quarantined by exactly one of two mechanisms: the GoogleTest `DISABLED_` prefix (single test) or the `flaky` CTest label (whole target). Every quarantine site SHALL carry a comment linking a GitHub issue that names an owner and an exit criterion. Gating lanes SHALL exclude the `flaky` label (`ctest -LE flaky`). Assertions SHALL NOT be deleted or weakened to stabilize a flaky test.

#### Scenario: Quarantine entry carries metadata
- **GIVEN** a test is identified as flaky
- **WHEN** it is quarantined
- **THEN** the quarantine site SHALL link a GitHub issue naming an owner and an exit criterion

#### Scenario: Gating lanes exclude quarantined targets
- **GIVEN** a target carries the `flaky` label
- **WHEN** a gating lane invokes CTest
- **THEN** the invocation SHALL exclude the `flaky` label and the target's verdict SHALL NOT affect the gate

#### Scenario: Assertion deletion is rejected
- **GIVEN** a change that removes or weakens a test assertion in response to intermittent failure
- **WHEN** the change is reviewed
- **THEN** it SHALL be rejected in favor of quarantine with entry metadata

#### Scenario: No unticketed quarantine
- **GIVEN** the test tree
- **WHEN** quarantine sites are enumerated (grep for `DISABLED_` and the `flaky` label)
- **THEN** every site SHALL resolve to an open linked issue, including the pre-existing `DISABLED_FullE2E` (tests/integration/test_ipc_integration.cpp:42)

### Requirement: Quarantined Tests Keep Running
Quarantined tests SHALL continue to execute in a scheduled non-blocking lane — `ctest -L flaky` for labeled targets and `--gtest_also_run_disabled_tests` for `DISABLED_` tests — with results uploaded as workflow artifacts. The lane SHALL NOT gate any merge or workflow verdict. The lane SHALL report the current quarantine size.

#### Scenario: Quarantine lane runs nightly
- **WHEN** the scheduled quarantine lane executes
- **THEN** all quarantined tests SHALL run and their results SHALL be uploaded as artifacts

#### Scenario: Quarantine failure does not gate
- **GIVEN** a quarantined test fails in the quarantine lane
- **WHEN** the workflow concludes
- **THEN** the workflow verdict SHALL NOT fail on that account

#### Scenario: Quarantine size is visible
- **WHEN** the quarantine lane completes
- **THEN** its output SHALL state the count of `DISABLED_` tests and `flaky`-labeled targets

### Requirement: Nightly Burn-In Lane
A scheduled job in `.github/workflows/ci.yml` SHALL run the non-quarantined suites under `ctest --repeat until-fail:N` (N ≥ 5) and SHALL run `legends_unit_tests` under `--gtest_shuffle` with the random seed logged. The lane SHALL be non-gating, SHALL upload its results as artifacts, and SHALL be invocable on demand via workflow dispatch.

#### Scenario: Repetition detects sporadic failure
- **GIVEN** a test that fails intermittently
- **WHEN** the burn-in lane repeats it under `--repeat until-fail:N`
- **THEN** a single failure in N repetitions SHALL surface as a burn-in finding attributed to that test

#### Scenario: Order dependence is reproducible
- **GIVEN** a test that fails only under a particular execution order
- **WHEN** the shuffled run fails
- **THEN** the logged `--gtest_random_seed` SHALL reproduce the failing order deterministically

#### Scenario: Burn-in findings feed quarantine
- **GIVEN** a burn-in finding
- **WHEN** it is triaged
- **THEN** the outcome SHALL be a fix or a quarantine entry with metadata — never a weakened assertion

### Requirement: Flake Ledger From Run Attempts
A scheduled job SHALL snapshot workflow runs with `run_attempt > 1` via the Actions per-attempt API, record which jobs changed outcome between attempts, and publish the snapshot as a workflow artifact. Ledger data SHALL be kept as artifacts and tracked issues, not as bot commits. Collection SHALL be ongoing, not retrospective.

#### Scenario: Rerun flip is recorded
- **GIVEN** a workflow run that was re-run and changed outcome between attempts
- **WHEN** the ledger job next executes
- **THEN** the run, the flipped jobs, and the attempt outcomes SHALL appear in the published artifact

#### Scenario: Recurring flips become issues
- **GIVEN** the same job flips outcome across multiple ledger snapshots
- **WHEN** the ledger is triaged
- **THEN** a tracked issue SHALL exist for the recurring flake

#### Scenario: No bot commits
- **WHEN** the ledger job publishes a snapshot
- **THEN** it SHALL NOT create commits in the repository

### Requirement: SDL Startup Assertion Decision
For each of `tests/unit/test_pal_sdl2_backend.cpp` and `tests/unit/test_pal_sdl3_backend.cpp`, the `InputSourceInitializes` test SHALL again assert a property of the events polled immediately after `initialize()`. The decision SHALL be made per test: where startup events are legitimate documented behavior for that backend, the test SHALL assert that every polled event belongs to the legitimate startup set and SHALL fail on any other event type; where they are not, the original zero-events assertion SHALL be restored and the test quarantined per the convention. An unconditional discard of the poll result SHALL NOT remain in either test.

#### Scenario: Typed assertion where init events are legitimate
- **GIVEN** a backend whose documented behavior legitimately emits window or device events during init
- **WHEN** the init-time poll returns events
- **THEN** the test SHALL pass only if every returned event is in the legitimate startup set
- **AND** a spurious input event (key, mouse, or axis) SHALL fail the test

#### Scenario: Restore and quarantine where init events are not legitimate
- **GIVEN** a backend for which no startup events are legitimate
- **WHEN** the assertion decision is applied
- **THEN** `EXPECT_EQ(count, 0u)` SHALL be restored
- **AND** if it flakes, the test SHALL be quarantined with owner and exit criterion rather than weakened

#### Scenario: Per-backend independence
- **WHEN** the decisions for SDL2 and SDL3 are made
- **THEN** each SHALL be justified against that backend's documented startup behavior, and the two outcomes MAY differ

### Requirement: Statistical Quarantine Exit
A quarantined test SHALL be re-enabled only after the candidate fix survives `ctest --repeat until-fail:10` for that test. The de-quarantine change SHALL remove the `DISABLED_` prefix or `flaky` label and close the linked issue together. Quarantine entries SHALL be re-triaged on a recurring cadence so stale entries are fixed, deleted with the removal recorded, or re-justified.

#### Scenario: Exit requires consecutive passes
- **GIVEN** a candidate fix for a quarantined test
- **WHEN** re-enablement is proposed
- **THEN** evidence of ten consecutive passes under `--repeat until-fail:10` SHALL accompany the change

#### Scenario: De-quarantine closes the loop
- **WHEN** a test is de-quarantined
- **THEN** the same change SHALL remove the quarantine marker and the linked issue SHALL be closed

#### Scenario: Stale quarantine is re-triaged
- **GIVEN** a quarantine entry older than the re-triage cadence
- **WHEN** re-triage occurs
- **THEN** the entry SHALL be fixed, deleted with the removal recorded, or re-justified on the issue
