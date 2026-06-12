## Purpose

Define the CI signal contract: which validation lanes are required for ordinary
pushes and pull requests, which are optional, and what each lane must guarantee
(deterministic save/load, repository hygiene, coverage reporting).
## Requirements
### Requirement: Primary CI Signal
Normal source pushes and pull requests SHALL have one high-signal required validation set: Linux headless, Windows headless, ABI verification, coverage artifact generation, Sprint 2 checks, and Module DAG architecture checks.

#### Scenario: Normal source push
- **GIVEN** a push modifies source, headers, tests, scripts, CMake, or workflow files
- **WHEN** GitHub Actions runs
- **THEN** primary headless Linux and Windows checks SHALL run
- **AND** optional backend and research checks SHALL NOT duplicate the same headless failure as separate required failures

### Requirement: Optional Validation Lanes
PAL backends, SDL backends, macOS, TLA+, and duplicate full Module DAG builds SHALL be clearly optional for ordinary pushes. Sanitizer lanes (ASan, UBSan, TSan), fuzz smoke runs, and dependency scanning SHALL NOT be classed as optional: sanitizers and fuzz gate at their pull-request/master tier, and dependency scanning gates at its nightly/dispatch tier.

#### Scenario: Optional lanes
- **GIVEN** ordinary source changes are pushed
- **WHEN** optional validation is not explicitly requested
- **THEN** the optional lanes SHALL run only when path-gated, scheduled, manually dispatched, or tag-oriented
- **AND** their job names SHALL identify them as optional

#### Scenario: Enforced lanes are not named optional
- **GIVEN** a lane gates at any trigger tier
- **WHEN** its job name is rendered in the Actions UI
- **THEN** the name SHALL NOT contain "Optional"

### Requirement: Deterministic Save/Load
Save/load and replay determinism SHALL preserve the hash-relevant CPU and lightweight context state.

#### Scenario: Save and load from an execution checkpoint
- **GIVEN** an initialized engine has executed to a save point
- **WHEN** state is saved, execution continues, and the saved state is restored
- **THEN** the immediate post-load hash SHALL match the saved hash
- **AND** replaying the same interval SHALL produce the same final hash

### Requirement: Repository Hygiene
Local agent worktrees SHALL NOT be tracked as repository content.

#### Scenario: Checkout cleanup
- **GIVEN** GitHub Actions checks out the repository
- **WHEN** post-job cleanup runs
- **THEN** there SHALL be no missing submodule mapping warning for `.claude/worktrees/*`

### Requirement: Coverage Signal
Coverage SHALL run independently from optional backend lanes and SHALL publish artifacts when generated.

#### Scenario: Coverage job
- **GIVEN** the coverage workflow job builds and tests successfully
- **WHEN** coverage is captured
- **THEN** `coverage.filtered.info` SHALL be uploaded
- **AND** the coverage threshold policy SHALL be explicitly documented as report-only until a baseline is established

### Requirement: Mandatory Lanes Are Deterministically Green
The ASan, UBSan, and fuzz lanes in `.github/workflows/ci.yml` SHALL pass deterministically at their existing trigger tier. Red runs SHALL be resolved by fixing the root cause or by quarantining the affected test under an issue-linked `DISABLED_` marker; deleting or weakening an assertion to obtain green SHALL NOT be an accepted fix.

#### Scenario: Clean change passes the sanitizer and fuzz lanes
- **GIVEN** a pull request that introduces no memory error, undefined behavior, or fuzz-reachable crash
- **WHEN** the `sanitizers` (address, undefined) and `fuzz` jobs run
- **THEN** both jobs SHALL conclude success

#### Scenario: Quarantine preserves the record
- **WHEN** a failing test is quarantined instead of fixed
- **THEN** the test SHALL carry a `DISABLED_` marker referencing a tracked issue stating the exit criterion

### Requirement: TSan Gates via Suppression File
A `tsan-suppressions.txt` SHALL be checked into the repository, containing one entry per known race, each annotated with its tracking issue. The TSan matrix entry SHALL load it via `TSAN_OPTIONS=suppressions=` and SHALL NOT carry `allow_failure`. The CI job SHALL install a symbolizer (`llvm-symbolizer`) so suppressions can match. The `tsan` CMake preset SHALL apply the same suppression file so local runs and CI agree on the known-race set.

#### Scenario: New race fails the lane
- **GIVEN** a pull request introducing a data race not matched by `tsan-suppressions.txt`
- **WHEN** the `thread` sanitizer matrix entry runs
- **THEN** the job SHALL fail and the workflow conclusion SHALL be failure

#### Scenario: Known race is suppressed and tracked
- **GIVEN** a race entry present in `tsan-suppressions.txt`
- **WHEN** the entry is read
- **THEN** it SHALL be preceded by a comment linking a tracked issue whose closure removes the entry

#### Scenario: Local reproduction matches CI
- **WHEN** the `tsan` test preset runs locally
- **THEN** the same suppression file SHALL be in effect as in the CI `thread` matrix entry

### Requirement: MSan Leg Retired with Re-entry Condition
The `memory` sanitizer matrix entry SHALL be removed from `.github/workflows/ci.yml`. A tracked issue SHALL record the retirement and its re-entry condition: an MSan-instrumented libc++ (and instrumented dependency surface), with any re-introduced lane placed at the nightly tier. No `msan` CMake preset SHALL be added while the lane is retired.

#### Scenario: No MSan execution after retirement
- **WHEN** the `sanitizers` job matrix is expanded on any trigger
- **THEN** no `memory` entry SHALL be present

#### Scenario: Re-entry is auditable
- **WHEN** the retirement lands
- **THEN** a tracked issue SHALL exist stating the instrumented-libc++ re-entry condition

### Requirement: Dependency Scan Produces an Honest Verdict
The `dependency-scan` job SHALL invoke osv-scanner only in modes the tool supports (no unparseable `--lockfile` input), SHALL upload its findings as artifacts, and SHALL NOT mute failures via `|| true` or `continue-on-error` once the invocation is fixed and a triaged green dispatch run is recorded.

#### Scenario: Vulnerability fails the scheduled run
- **GIVEN** the fixed invocation and a dependency with a known unsuppressed vulnerability
- **WHEN** the nightly or dispatched `dependency-scan` job runs
- **THEN** the job SHALL conclude failure and its findings SHALL be uploaded as an artifact

#### Scenario: Unmute only after rehearsal
- **WHEN** the mutes are removed
- **THEN** a prior `workflow_dispatch` run of the fixed invocation SHALL have concluded success

### Requirement: Lane Demotion Requires a Tracked Exit Criterion
No CI lane SHALL be demoted — marked allow-failure, muted, retired, narrowed in trigger tier, or relaxed in its assertions — without a tracked issue stating the demotion and the criterion for restoring enforcement. YAML comments SHALL NOT substitute for the tracked issue.

#### Scenario: Demotion carries its exit
- **GIVEN** a change that sets `continue-on-error`/`allow_failure`, removes a lane, or narrows a lane's triggers
- **WHEN** the change is reviewed
- **THEN** it SHALL reference a tracked issue stating the exit criterion, and a change lacking one SHALL be rejected

