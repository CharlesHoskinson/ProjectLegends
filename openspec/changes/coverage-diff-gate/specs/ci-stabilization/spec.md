## MODIFIED Requirements

### Requirement: Coverage Signal
Coverage SHALL run independently from optional backend lanes and SHALL publish artifacts when generated. The published `coverage.filtered.info` SHALL exclude the vendored engine tree from its denominator. The coverage policy SHALL be enforced — diff coverage on pull requests and committed per-module ratchet floors (see the `coverage-gating` capability) — rather than documented as report-only.

#### Scenario: Coverage job
- **GIVEN** the coverage workflow job builds and tests successfully
- **WHEN** coverage is captured
- **THEN** `coverage.filtered.info` SHALL be uploaded
- **AND** it SHALL contain no entries from the vendored engine tree
- **AND** the published policy text SHALL state the enforced diff-coverage and floor verdicts, not a report-only disclaimer
