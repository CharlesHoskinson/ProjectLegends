## ADDED Requirements

### Requirement: Capability Truth Enforcement
Every API marked `proxy-supported` SHALL have proxy code, dispatcher routing, and capability documentation in agreement.

#### Scenario: Supported proxy API validation
- **GIVEN** an API is marked `proxy-supported` in `capability_truth.json`
- **WHEN** the capability validator runs
- **THEN** the proxy implementation SHALL NOT directly return `LEGENDS_ERR_NOT_SUPPORTED`
- **AND** every request type used by the proxy SHALL have a dispatcher case
- **AND** the Markdown matrix SHALL match the JSON source of truth

### Requirement: Proxy Parity Report
The repository SHALL expose a concise report of remaining proxy-missing and proxy-partial APIs.

#### Scenario: Report generated
- **GIVEN** the capability manifest has been updated
- **WHEN** the proxy parity report is generated or refreshed
- **THEN** it SHALL list counts by proxy status
- **AND** SHALL list each remaining missing/partial API with a note explaining why it remains deferred

### Requirement: RuntimeHost Bypass Guard Preservation
RuntimeHost application bypass debt SHALL remain limited to lifecycle creation and destruction.

#### Scenario: Graphify validation after proxy work
- **GIVEN** Gemini has modified proxy and dispatcher code
- **WHEN** Graphify enrichment validation runs
- **THEN** application-layer direct `legends_*` bypass count SHALL remain exactly `2`
- **AND** the allowlist SHALL contain only `legends_create` and `legends_destroy`
