## ADDED Requirements

### Requirement: MSan CI job
CI SHALL include an MSan job using Clang with instrumented libc++. It SHALL run separately from the ASan/TSan matrix (incompatible).

#### Scenario: MSan job runs
- **WHEN** CI runs on push/PR
- **THEN** an MSan job SHALL execute and report results

#### Scenario: MSan passes or has documented suppressions
- **WHEN** MSan finds issues
- **THEN** they SHALL either be fixed or have documented suppressions with rationale

### Requirement: Coverage dashboard
CI SHALL upload coverage data to Codecov (or equivalent). README SHALL display a coverage badge.

#### Scenario: Badge visible
- **WHEN** README.md is viewed
- **THEN** a coverage percentage badge SHALL be displayed

#### Scenario: Coverage uploaded
- **WHEN** CI completes
- **THEN** coverage data SHALL be available on Codecov dashboard

### Requirement: gsl-lite check wired
`check_gsl_lite_usage.py` SHALL be executed in `sprint2-checks.yml`.

#### Scenario: Check runs in CI
- **WHEN** sprint2-checks workflow runs
- **THEN** `check_gsl_lite_usage.py` SHALL execute and fail the build on violations

### Requirement: Input injection fuzz target
A fuzz target at `tests/fuzz/fuzz_input_injection.cpp` SHALL exercise key and mouse event injection paths with random data.

#### Scenario: Fuzz target runs under ASan
- **WHEN** the fuzz CI job runs
- **THEN** `fuzz_input_injection` SHALL run for at least 60 seconds with ASan enabled

### Requirement: PIC C++ unit tests
C++ unit tests SHALL cover: IRQ raise, ISR/IRR transitions, cascade mode, auto-EOI. These complement the existing TLA+ PIC spec.

#### Scenario: PIC tests pass
- **WHEN** unit tests run
- **THEN** PIC tests SHALL pass covering all 4 scenarios
