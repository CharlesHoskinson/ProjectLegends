## ADDED Requirements

### Requirement: Route And Support Are Distinct
The capability truth model SHALL distinguish IPC transport routing from public functional support.

#### Scenario: IPC route exists but behavior remains partial
- **GIVEN** a proxy request and dispatcher case exist for an API
- **WHEN** the underlying public behavior remains partial or unsupported
- **THEN** the capability manifest SHALL NOT classify the API as `proxy-supported`
- **AND** SHALL record the proxy route separately from public support status

### Requirement: Supported Claims Require Evidence
The validator SHALL reject unsupported `proxy-supported` claims.

#### Scenario: Direct capability is partial
- **GIVEN** an API has `direct_status` of `partial`
- **WHEN** the manifest sets `proxy_status` to `proxy-supported`
- **THEN** the validator SHALL require explicit notes and test evidence showing why proxy mode is functionally complete
- **AND** SHALL fail if that evidence is absent

### Requirement: Capability Summary
The validator SHALL emit a status summary for auditor review.

#### Scenario: Capability validator runs
- **GIVEN** the capability manifest contains all public APIs
- **WHEN** the validator completes
- **THEN** it SHALL report counts by proxy support status
- **AND** SHALL report counts by proxy route status
