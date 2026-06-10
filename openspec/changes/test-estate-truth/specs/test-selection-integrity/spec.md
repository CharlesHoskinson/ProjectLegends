# test-selection-integrity

## ADDED Requirements

### Requirement: Module-Level Labels Inside Monolithic Suites
Tests compiled into the monolithic suites SHALL carry module-level CTest labels aligned with the module prefixes in `cmake/ModuleManifest.cmake`, in addition to their suite-level label. Labels SHALL be attached at `gtest_discover_tests` discovery time, since discovered tests cannot be relabeled at configure time.

#### Scenario: Module subset is selectable
- **GIVEN** a configured build with `LEGENDS_BUILD_TESTS=ON`
- **WHEN** `ctest -N -L '^mod_ipc$'` is run
- **THEN** the selection SHALL contain the IPC unit tests and no tests from other modules

#### Scenario: Labels survive discovery
- **GIVEN** a test registered via `gtest_discover_tests`
- **WHEN** `ctest --print-labels` is run after the test step's discovery
- **THEN** the module-level labels SHALL appear in the label list

### Requirement: Nonzero-Selection Guard on Label-Selected Steps
Every CTest invocation that selects by label (`-L`), in workflows and in custom targets, SHALL fail if the label expression selects zero tests. A label referenced by any selection or exclusion expression SHALL be applied to at least one registered test.

#### Scenario: Vacuous label fails the step
- **GIVEN** a `ctest -L` step whose label expression matches no registered test
- **WHEN** the step executes
- **THEN** the step SHALL fail rather than report success over an empty set

#### Scenario: Guard covers existing custom targets
- **WHEN** any of the label-selecting custom targets (`legends-test-unit`, `test-integration`, `test-abi`, `test-toolchain`, `test-determinism`, `test-soak`) runs
- **THEN** an empty selection SHALL cause the target to fail

### Requirement: Anchored Label Expressions
Label selection and exclusion expressions in workflows and custom targets SHALL be anchored regexes (e.g. `-L '^unit$'`), because CTest label matching is regex-substring and unanchored short labels over-match.

#### Scenario: Substring over-match is prevented
- **GIVEN** labels `unit` and `unit_slow` both exist
- **WHEN** the unit-tier step selects with its anchored expression
- **THEN** only tests labeled exactly `unit` SHALL be selected

### Requirement: Workflow Selection Goes Through CTest Labels
Workflow test steps SHALL select tests via `ctest -L` label expressions rather than raw `--gtest_filter` invocations of the test binary, except where a step requires gtest execution semantics CTest cannot express. The asan-lifecycle step SHALL retain direct binary invocation with `--gtest_repeat=3`, and SHALL verify its filter matches a nonzero number of tests.

#### Scenario: Sprint 2 checks select by label
- **WHEN** the sprint2-checks test step runs
- **THEN** it SHALL invoke `ctest` with an anchored label expression under the nonzero-selection guard, not `--gtest_filter` on the binary

#### Scenario: Lifecycle repeat semantics preserved
- **WHEN** the asan-lifecycle step runs
- **THEN** it SHALL execute the lifecycle tests with `--gtest_repeat=3` in a single process
- **AND** it SHALL fail if its test filter matches zero tests

### Requirement: Skip-Stubs Are Visibly Labeled
Every integration test file whose body is a `GTEST_SKIP()` stub SHALL carry the label `stub` in addition to its suite label, and each stub SHALL reference a tracked issue in its skip message. Excluding stubs from a gate SHALL use an explicit `-LE '^stub$'` so the exclusion is visible in the invocation.

#### Scenario: Stub debt is enumerable
- **WHEN** `ctest -N -L '^stub$'` is run on a configured build
- **THEN** the selection SHALL list every skip-stub test and nothing else

#### Scenario: Stub skip names its issue
- **GIVEN** a skip-stub test executes
- **WHEN** its skip message is emitted
- **THEN** the message SHALL reference the tracked issue for implementing the test
