## MODIFIED Requirements

### Requirement: Primary CI Signal
Normal source pushes and pull requests SHALL have one high-signal required validation set: Linux headless, Windows headless, Linux IPC, Windows IPC, ABI verification, REUSE license compliance, coverage artifact generation, Sprint 2 checks, and Module DAG architecture checks.

#### Scenario: Normal source push
- **GIVEN** a push modifies source, headers, tests, scripts, CMake, or workflow files
- **WHEN** GitHub Actions runs
- **THEN** primary headless Linux and Windows checks SHALL run
- **AND** the Linux IPC, Windows IPC, and REUSE license compliance checks SHALL run
- **AND** optional backend and research checks SHALL NOT duplicate the same headless failure as separate required failures
