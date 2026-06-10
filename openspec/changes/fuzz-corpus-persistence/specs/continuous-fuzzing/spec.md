# continuous-fuzzing

## ADDED Requirements

### Requirement: Corpus Persists Across CI Runs
The fuzz lane SHALL persist the generated corpus across CI runs via a per-target cache over `build/tests/fuzz/corpus/<target>`. The `generate_fuzz_corpus` tool SHALL run only when the cache for a target is absent (cold start); it SHALL NOT overwrite a restored corpus. The nightly run SHALL prune the corpus with libFuzzer `-merge=1` before the cache is saved.

#### Scenario: Warm run reuses prior coverage
- **GIVEN** a previous run populated the corpus cache for a target
- **WHEN** the fuzz job runs again
- **THEN** the target SHALL start from the restored corpus and `generate_fuzz_corpus` SHALL NOT overwrite it

#### Scenario: Cold start seeds from the generator
- **GIVEN** no cache entry exists for a target
- **WHEN** the fuzz job runs
- **THEN** `generate_fuzz_corpus` SHALL seed that target's corpus directory before fuzzing

#### Scenario: Nightly prune bounds the cache
- **WHEN** the scheduled fuzz run completes its exploration steps
- **THEN** each target's corpus SHALL be minimized via `-merge=1` before the cache entry is saved

### Requirement: Reproducer Seeds Are Committed
Curated seed inputs — including minimized crash reproducers for every fixed fuzz finding — SHALL be committed under `tests/fuzz/corpus/<target>/`, the directory consumed by the existing CMake copy hook (tests/fuzz/CMakeLists.txt:46-49). Every fuzz target, including `fuzz_input_injection`, SHALL be invoked with a corpus directory.

#### Scenario: Copy hook activates
- **GIVEN** committed seeds exist under `tests/fuzz/corpus/`
- **WHEN** the fuzz tree is configured and built
- **THEN** the seeds SHALL be copied into the build-tree corpus directory consumed by the harnesses

#### Scenario: Fixed crash becomes a permanent seed
- **GIVEN** a fuzz-found crash whose fix has landed
- **WHEN** the fix is reviewed
- **THEN** the minimized reproducer SHALL be present under `tests/fuzz/corpus/<target>/`

#### Scenario: No corpus-less target
- **WHEN** any fuzz target is invoked by CI
- **THEN** the invocation SHALL include a corpus directory argument

### Requirement: Crash Artifacts Survive the Runner
Every fuzzer invocation in CI SHALL set `-artifact_prefix` to a job-local artifact directory, and the fuzz job SHALL upload that directory as a workflow artifact when the job fails. Each invocation SHALL set explicit `-rss_limit_mb` and per-input `-timeout` values consistent with its `-max_len`, so OOM and slow-input artifacts are distinguishable from memory-safety crashes.

#### Scenario: Crash input is downloadable
- **GIVEN** a fuzz target crashes during any CI run
- **WHEN** the job concludes
- **THEN** the triggering input SHALL be available as a downloadable workflow artifact

#### Scenario: Resource exits are classified
- **GIVEN** an input that exceeds the configured RSS or per-input time limit
- **WHEN** the fuzzer exits on it
- **THEN** the uploaded artifact's name SHALL identify the class (`oom-*` or `timeout-*`), not present as a generic crash

### Requirement: PR Tier Is Deterministic Replay
On pull requests, the fuzz job SHALL NOT perform mutation-based fuzzing. It SHALL execute each fuzz target in libFuzzer file-list mode over the committed seeds and known reproducers, with ASan active, and SHALL fail on any crash. New-bug discovery SHALL be confined to the scheduled tier.

#### Scenario: PR replays the vetted set
- **GIVEN** a pull request triggers the fuzz job
- **WHEN** the PR-tier step runs
- **THEN** each target binary SHALL be invoked with the seed and reproducer files as arguments and SHALL perform no mutation

#### Scenario: Regression of a fixed bug fails the PR
- **GIVEN** a pull request reintroduces a crash covered by a committed reproducer
- **WHEN** the replay step runs
- **THEN** the job SHALL fail

#### Scenario: PR verdict is attributable
- **GIVEN** a pull request that does not change fuzz-reachable behavior
- **WHEN** the replay step runs
- **THEN** the step SHALL pass deterministically — an undiscovered pre-existing bug SHALL NOT be able to fail it

### Requirement: Scheduled Tier Is Funded Exploration
The scheduled (nightly cron) fuzz run SHALL fuzz each target for at least 600 seconds, starting from the persisted corpus. The job's `timeout-minutes` SHALL accommodate the full funded budget across all targets plus the build, and SHALL be raised before the per-target durations are increased.

#### Scenario: Nightly meets the funding floor
- **WHEN** the scheduled fuzz run executes
- **THEN** each of the five targets SHALL receive at least 600 seconds of fuzzing from the persisted corpus

#### Scenario: Timeout precedes funding
- **GIVEN** the change history of the fuzz job
- **WHEN** the per-target durations are raised to the funded budget
- **THEN** the job-level `timeout-minutes` SHALL already accommodate the total budget

#### Scenario: Nightly discovery feeds the replay gate
- **GIVEN** the nightly run finds a new crash
- **WHEN** the finding is triaged and fixed
- **THEN** the minimized reproducer SHALL be committed under `tests/fuzz/corpus/<target>/` and thereafter replayed on every pull request
