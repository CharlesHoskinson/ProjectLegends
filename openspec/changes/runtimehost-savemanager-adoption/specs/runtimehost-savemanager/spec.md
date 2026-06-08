## ADDED Requirements

### Requirement: SaveManager RuntimeHost Routing
`SaveManager` operations SHALL route state saving and loading operations through the `RuntimeHost` abstraction when called from the main application.

#### Scenario: Save state routed
- **GIVEN** Application invokes `SaveManager::saveToSlot`
- **WHEN** the runtime instance is available
- **THEN** it SHALL call `RuntimeHost::save_state`
- **AND** SHALL NOT directly call `legends_save_state`

#### Scenario: Load state routed
- **GIVEN** Application invokes `SaveManager::loadFromSlot`
- **WHEN** the runtime instance is available
- **THEN** it SHALL call `RuntimeHost::load_state`
- **AND** SHALL NOT directly call `legends_load_state`

### Requirement: Two-call query/fill preservation
The state saving implementation in `SaveManager::saveToSlot` SHALL preserve the two-call query/fill behavior of the emulation backend.

#### Scenario: Query and fill state
- **GIVEN** `SaveManager::saveToSlot` is called
- **WHEN** querying state size
- **THEN** it SHALL call `RuntimeHost::save_state` with a null buffer pointer to query the size
- **AND** then call `RuntimeHost::save_state` with the allocated buffer to fill the state

### Requirement: Format and CRC stability
State saving file format, unpacking layout, and CRC verification checks SHALL be preserved.

#### Scenario: CRC verification passes
- **GIVEN** a state file is loaded from slot
- **WHEN** `SaveManager` reads the file
- **THEN** it SHALL unpack the `SaveStateHeader`
- **AND** verify that the computed CRC-32 matches the CRC stored in the header

### Requirement: Autosave slot preservation
Crash autosave recovery SHALL continue to use slot `0` as valid storage.

#### Scenario: Autosave slot remains loadable
- **GIVEN** crash recovery invokes `SaveManager::recoverAutosave`
- **WHEN** the autosave file is stored in `SaveManager::kAutosaveSlot`
- **THEN** `SaveManager` SHALL treat slot `0` as a valid storage slot
- **AND** SHALL route the load through `RuntimeHost::load_state`

### Requirement: Bypass count reduction
The total count of direct FFI bypasses in the application layer SHALL decrease.

#### Scenario: Graphify count drops
- **GIVEN** SaveManager migration completes
- **WHEN** Graphify checks are run
- **THEN** the number of observed bypasses SHALL decrease from 38 to 35
