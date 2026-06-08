## ADDED Requirements

### Requirement: ABI Negative Contract Manifest
The project SHALL maintain a machine-readable ABI parity contract manifest for public `legends_*` APIs covered by RuntimeHost/proxy work.

#### Scenario: Exported API coverage is checked
- **GIVEN** `include/legends/legends_embed.h` exports a `LEGENDS_API` symbol
- **WHEN** the ABI contract checker runs
- **THEN** every manifest entry SHALL reference an exported API
- **AND** unknown API names SHALL fail validation

### Requirement: Edge-Case Evidence
Each manifest entry SHALL declare evidence for required ABI edge cases.

#### Scenario: Required case has evidence
- **GIVEN** an API requires `null_handle`, `null_required_out`, `query_fill`, `undersized_buffer`, `default_initialized_output`, or `direct_proxy_return_parity`
- **WHEN** the ABI contract checker runs
- **THEN** the checker SHALL verify evidence files exist
- **AND** SHALL fail if a required case has no evidence token or test reference

#### Scenario: Case is not applicable
- **GIVEN** a case does not apply to an API
- **WHEN** the manifest marks the case `not_applicable`
- **THEN** the manifest SHALL include a human-readable reason

### Requirement: CI Enforcement
The ABI parity contract checker SHALL run in the fast quality gate.

#### Scenario: Manifest drifts
- **GIVEN** an implementation changes ABI coverage requirements
- **WHEN** CI runs
- **THEN** missing or stale ABI evidence SHALL fail the quality gate
