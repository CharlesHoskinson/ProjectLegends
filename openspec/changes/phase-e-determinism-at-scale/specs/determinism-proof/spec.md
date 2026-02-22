## ADDED Requirements

### Requirement: Minimal COM test binaries
Test fixture COM binaries SHALL be assembled and checked into `tests/fixtures/`: `counter.com` (increment memory N times, HLT), `graphics.com` (switch to Mode 13h, draw pattern, HLT), `input.com` (wait for keystroke, echo, HLT).

#### Scenario: Binaries exist and are valid
- **WHEN** test fixtures are inspected
- **THEN** `counter.com`, `graphics.com`, and `input.com` SHALL exist as valid COM executables

### Requirement: Short-cycle correctness
Loading `counter.com` and running 1K cycles SHALL produce the expected memory value.

#### Scenario: Counter verified
- **WHEN** `counter.com` runs for 1K cycles
- **THEN** the target memory location SHALL contain the expected count

### Requirement: 1M-cycle determinism
Two independent instances running the same COM program for 1M cycles SHALL produce identical state hashes.

#### Scenario: Two instances match
- **WHEN** two instances run `counter.com` for 1M cycles
- **THEN** their final state hashes SHALL be identical

### Requirement: Save/load midpoint equivalence
Saving at 500K cycles, loading, and running 500K more SHALL produce the same hash as a straight 1M-cycle run.

#### Scenario: Midpoint save/load matches
- **WHEN** instance A runs 1M straight and instance B saves at 500K, loads, runs 500K more
- **THEN** final state hashes of A and B SHALL be identical

### Requirement: Graphics mode determinism
Mode 13h determinism SHALL be verified with framebuffer content comparison.

#### Scenario: Graphics mode round-trips
- **WHEN** `graphics.com` runs in Mode 13h on two instances
- **THEN** framebuffer contents SHALL be identical

### Requirement: Input replay determinism
Injecting keys at specific cycle counts SHALL produce identical hashes across runs.

#### Scenario: Input replay matches
- **WHEN** keys are injected at cycles 100K, 200K, 300K on two instances
- **THEN** final state hashes SHALL be identical

### Requirement: Nightly soak test
A nightly CI job SHALL run 1M-cycle determinism tests x10 with different COM programs.

#### Scenario: Soak test passes
- **WHEN** the nightly job runs
- **THEN** all 10 runs SHALL produce matching hashes
