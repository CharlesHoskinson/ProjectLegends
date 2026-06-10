## ADDED Requirements

### Requirement: gsl-lite PRIVATE linkage
The `aibox_core` target SHALL link `gsl::gsl-lite-v1` as PRIVATE, not PUBLIC. Consumers of `aibox_core` SHALL NOT transitively receive gsl-lite headers.

#### Scenario: Linkage changed
- **WHEN** `engine/CMakeLists.txt` is inspected
- **THEN** `target_link_libraries(aibox_core PRIVATE gsl::gsl-lite-v1)` SHALL be present

#### Scenario: Downstream builds unaffected
- **WHEN** the legends library is built
- **THEN** compilation SHALL succeed without gsl-lite in the consumer's include path

### Requirement: No /wd4244 suppression
The engine build SHALL NOT suppress MSVC warning C4244 (narrowing conversion). All narrowing conversions SHALL use explicit `static_cast<>`.

#### Scenario: Warning suppression removed
- **WHEN** `engine/CMakeLists.txt` is inspected
- **THEN** `/wd4244` SHALL NOT appear

#### Scenario: Clean build with no narrowing warnings
- **WHEN** the engine is built on MSVC
- **THEN** zero C4244 warnings SHALL be emitted (all fixed with explicit casts)
