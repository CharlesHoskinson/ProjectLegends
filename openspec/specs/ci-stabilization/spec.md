## ADDED Requirements

### Requirement: Primary CI Signal
Normal source pushes and pull requests SHALL have one high-signal required validation set: Linux headless, Windows headless, ABI verification, coverage artifact generation, Sprint 2 checks, and Module DAG architecture checks.

#### Scenario: Normal source push
- **GIVEN** a push modifies source, headers, tests, scripts, CMake, or workflow files
- **WHEN** GitHub Actions runs
- **THEN** primary headless Linux and Windows checks SHALL run
- **AND** optional backend and research checks SHALL NOT duplicate the same headless failure as separate required failures

### Requirement: Optional Validation Lanes
PAL backends, SDL backends, macOS, sanitizers, fuzzing, TLA+, dependency scanning, and duplicate full Module DAG builds SHALL be clearly optional for ordinary pushes.

#### Scenario: Optional lanes
- **GIVEN** ordinary source changes are pushed
- **WHEN** optional validation is not explicitly requested
- **THEN** these lanes SHALL run only when path-gated, scheduled, manually dispatched, or tag-oriented
- **AND** their job names SHALL identify them as optional

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
