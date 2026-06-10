# soak-endurance

## ADDED Requirements

### Requirement: The soak Label Is Applied
The soak endurance tests in `tests/integration/test_soak_endurance.cpp` SHALL carry the CTest label `soak` (in addition to `integration`), applied through a mechanism that works with `gtest_discover_tests` discovery-time registration. The dead deferral to `cmake/SoakTestLabels.cmake` (CMakeLists.txt:1021-1028) SHALL be removed.

#### Scenario: soak selects the endurance tests
- **GIVEN** a configured build with `LEGENDS_BUILD_TESTS=ON`
- **WHEN** `ctest -N -L '^soak$'` is run
- **THEN** the selection SHALL contain the soak endurance tests and SHALL NOT be empty

#### Scenario: Exclusions exclude something
- **WHEN** `test-integration`, `legends-test-all`, or the release-validation ctest step runs with `--label-exclude soak`
- **THEN** the soak endurance tests SHALL be excluded from the run

### Requirement: Nightly Soak Job With the Env Gate Exported
A scheduled (nightly cron) CI job SHALL run `ctest -L '^soak$'` under the nonzero-selection guard with `LEGENDS_SOAK_ENABLED=1` exported, so the soak tests execute instead of hitting their `GTEST_SKIP` env gate (tests/integration/test_soak_endurance.cpp:76-83).

#### Scenario: Soak tests actually run nightly
- **GIVEN** the nightly soak job executes
- **WHEN** a soak test starts
- **THEN** it SHALL NOT skip on the `LEGENDS_SOAK_ENABLED` gate and SHALL run its endurance body

#### Scenario: Unexported gate is detectable
- **GIVEN** the env gate is not exported in the job
- **WHEN** the job's results are inspected
- **THEN** every soak test reports skipped — the job SHALL surface a 100%-skipped soak selection as a failure, not a pass

### Requirement: Soak Durations Bounded to the Runner Cap
Soak durations in CI SHALL be bounded so the nightly job (build plus all soak tests) completes within the 6-hour GitHub-hosted runner cap: the job SHALL set `LEGENDS_SOAK_DURATION_HOURS` accordingly, and the `test-soak` target's ctest `--timeout` SHALL NOT exceed the cap (replacing the current 46800 s at CMakeLists.txt:1038). Longer soaks remain available off-CI by overriding the duration env var.

#### Scenario: Nightly fits the runner
- **WHEN** the nightly soak job runs with its configured durations
- **THEN** the total job runtime SHALL fit within the runner's 6-hour limit rather than being killed at the cap

#### Scenario: Per-test timeout is consistent
- **WHEN** the soak selection runs in CI
- **THEN** no per-test timeout SHALL exceed the runner cap
