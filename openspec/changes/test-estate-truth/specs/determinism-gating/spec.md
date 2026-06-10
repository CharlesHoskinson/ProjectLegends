# determinism-gating

## ADDED Requirements

### Requirement: PR-Tier Determinism Job
A pull-request-tier CI job SHALL build the engine determinism suite and run it via `ctest -L '^determinism$'` under the nonzero-selection guard. The job SHALL use the existing `determinism` label and `aibox_determinism_tests` registration (engine/tests/determinism/CMakeLists.txt:33-45).

#### Scenario: Determinism runs on pull requests
- **GIVEN** a pull request triggers CI
- **WHEN** the determinism job runs
- **THEN** the tests labeled `determinism` SHALL execute and report pass/fail on the PR

#### Scenario: Empty determinism selection is a failure
- **GIVEN** the `determinism` label matches no registered tests in the build
- **WHEN** the determinism job runs
- **THEN** the job SHALL fail

### Requirement: Canary Proves the Oracle Can Fail
The determinism suite SHALL contain a canary test that mutates state covered by the `Full` hash between two hash computations and asserts the hashes differ. The canary SHALL run in the PR-tier determinism job.

#### Scenario: Oracle distinguishes a mutated machine
- **GIVEN** an initialized engine and a baseline `Full` hash
- **WHEN** the canary mutates hashed state (conventional memory) and recomputes the hash
- **THEN** the two hashes SHALL differ

#### Scenario: A blinded oracle turns the lane red
- **GIVEN** a regression causes the hash to ignore the mutated state
- **WHEN** the canary runs in CI
- **THEN** the determinism job SHALL fail

### Requirement: Hash Mode Selected by the Caller
`dosbox_lib_get_state_hash` SHALL NOT hardcode `HashMode::Fast`; the hash mode SHALL be selectable by the caller, with the default preserving current behavior for existing callers. The determinism test harness SHALL request `HashMode::Full`.

#### Scenario: Determinism harness hashes in Full mode
- **WHEN** the determinism suite computes state hashes through the library entry point
- **THEN** the computation SHALL use `HashMode::Full`, covering conventional memory in addition to CPU and context state

#### Scenario: Existing callers are unchanged
- **GIVEN** a caller that does not request a hash mode
- **WHEN** it invokes the state-hash entry point
- **THEN** the result SHALL match the pre-change `Fast`-mode behavior

#### Scenario: Full-coverage extension is out of scope
- **WHEN** this capability is implemented
- **THEN** the content of `HashMode::Full` (conventional memory; no VGA/device state, engine/src/misc/state_hash.cpp:296-305) SHALL be unchanged — widening it is engine serialization work owned elsewhere
