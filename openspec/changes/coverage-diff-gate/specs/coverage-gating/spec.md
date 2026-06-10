## ADDED Requirements

### Requirement: First-Party Coverage Denominator
The coverage policy artifact `coverage.filtered.info` SHALL exclude the vendored engine tree: the lcov filter in the `coverage` job SHALL remove `*/engine/*` in addition to the existing `/usr/*`, `*/build/_deps/*`, and `*/tests/*` patterns. Every coverage policy decision (diff gate, ratchet floors, release threshold inputs derived from this artifact) SHALL be computed over first-party code only.

#### Scenario: Engine files absent from the policy artifact
- **WHEN** the `coverage` job generates `coverage.filtered.info`
- **THEN** the artifact SHALL contain no `SF:` record whose path lies under `engine/`

#### Scenario: Engine-touching PR not held to first-party standards
- **GIVEN** a pull request whose only changes are under `engine/`
- **WHEN** the diff coverage gate runs
- **THEN** the engine lines SHALL contribute nothing to the diff denominator and the gate SHALL pass on the first-party diff (which is empty)

### Requirement: Diff Coverage Gates Pull Requests
Pull requests SHALL be gated on the coverage of their new and changed first-party lines, computed by diff-cover from `coverage.filtered.info` against the merge base with `origin/master`. The `coverage` job SHALL check out with full history (`fetch-depth: 0`) so the merge base exists. The gate step SHALL run unconditionally on pull-request events and SHALL NOT depend on the Codecov token or any external service. Enforcement SHALL be staged: one informational cycle (report printed, no failure) precedes flipping to `--fail-under`.

#### Scenario: Uncovered new lines fail the gate
- **GIVEN** enforcement is active and a pull request adds first-party lines below the fail-under target
- **WHEN** the diff coverage step runs
- **THEN** the step SHALL exit non-zero and the `coverage` job SHALL fail

#### Scenario: Covered changes pass regardless of legacy total
- **GIVEN** a pull request whose new/changed lines meet the target
- **WHEN** the diff coverage step runs
- **THEN** the gate SHALL pass even if absolute project coverage is below any historical value

#### Scenario: Gate verified to fail before enforcement
- **WHEN** enforcement is flipped from informational to `--fail-under`
- **THEN** a seeded pull request with uncovered new lines SHALL have been observed to turn the gate red first

#### Scenario: Absent Codecov token does not weaken the gate
- **GIVEN** the `CODECOV_TOKEN` secret is empty
- **WHEN** the `coverage` job runs on a pull request
- **THEN** the diff coverage gate SHALL execute and enforce identically; only the Codecov upload step SHALL be skipped

### Requirement: Per-Module Ratchet Floors
A committed floor file (`.ci/coverage-floors.txt`) SHALL record one line-coverage floor per first-party module directory aligned to the module DAG (`src/app`, `src/legends`, `src/legends_ipc`, `src/legends_proxy`, `src/engine_host`, `src/pal`, `src/libs`). Floors SHALL be seeded from the first post-engine-exclusion measurement on master — measured values rounded down, never placeholder targets. The `coverage` job SHALL extract each module's coverage via `lcov --extract` and fail if any module measures more than the noise slack (0.5 points) below its floor. Raising a floor SHALL be a manual commit. Lowering a floor SHALL require a tracked issue stating the exit criterion, per the lane-demotion rule.

#### Scenario: Module regression fails the job
- **GIVEN** seeded floors and a change that drops a module's line coverage more than 0.5 points below its floor
- **WHEN** the floor-check loop runs
- **THEN** the `coverage` job SHALL fail naming the module, its floor, and its measured value

#### Scenario: Floors reflect measurement, not aspiration
- **WHEN** the floor file is first committed
- **THEN** every floor value SHALL equal the corresponding module's measured line coverage from a recorded master run of the `coverage` job after engine exclusion

#### Scenario: Improvement prompts a ratchet raise
- **GIVEN** a module measures above its floor
- **WHEN** the floor-check loop runs
- **THEN** the job SHALL pass and print the measured value with a prompt to raise the committed floor

#### Scenario: New module without a floor is rejected
- **GIVEN** a `src/` module directory in the DAG-verified module set with no line in the floor file
- **WHEN** the floor-check loop runs
- **THEN** the job SHALL fail until a seeded floor entry is committed

#### Scenario: Silent floor lowering is rejected
- **WHEN** a change lowers a floor value without referencing a tracked issue with an exit criterion
- **THEN** review SHALL reject the change

### Requirement: Release Coverage Threshold Is Rehearsable
The `release-validation` job SHALL run on `v*` tag pushes and on `workflow_dispatch`. On dispatch runs the job SHALL execute the build, test, and coverage-threshold steps; the packaging-artifact download and verification steps SHALL be guarded to tag refs. The job's `needs` evaluation SHALL tolerate the tag-only `packaging` job being skipped on dispatch (explicit `needs.*.result` checks rather than the default success propagation).

#### Scenario: Dispatch rehearses the threshold
- **WHEN** the workflow is manually dispatched
- **THEN** `release-validation` SHALL run its coverage-threshold check and SHALL skip the packaging-artifact verification steps

#### Scenario: Tag run remains complete
- **GIVEN** a `v*` tag push
- **WHEN** `release-validation` runs
- **THEN** it SHALL execute both the coverage threshold and the packaging-artifact verification, requiring `packaging` to have succeeded

#### Scenario: Rehearsal precedes the first real tag
- **WHEN** the first `v*` tag is pushed after this change
- **THEN** at least one dispatch run of `release-validation` SHALL already have executed the threshold check

### Requirement: Coverage Policy Artifact States the Enforced Policy
The `coverage-policy.txt` artifact SHALL record the verdicts the job actually enforced (diff-cover result, per-module floor-check results) and SHALL NOT describe the policy as report-only once enforcement is active.

#### Scenario: Policy text reflects enforcement
- **GIVEN** the diff gate and floor checks are active
- **WHEN** the coverage artifact is uploaded
- **THEN** `coverage-policy.txt` SHALL contain the diff-coverage verdict and each module's floor comparison, and SHALL NOT contain the report-only disclaimer
