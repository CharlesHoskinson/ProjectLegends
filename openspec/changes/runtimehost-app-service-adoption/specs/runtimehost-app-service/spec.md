## ADDED Requirements

### Requirement: RuntimeHost Virtual Methods
`RuntimeHost` SHALL declare virtual methods for all remaining routable FFI operations:
`reset()`, `text_input(...)`, `get_cursor(...)`, `joystick_event(...)`, `set_log_callback(...)`, `set_midi_device(...)`, `set_midi_soundfont(...)`, `set_midi_romdir(...)`, `set_printer_output(...)`, `set_ttf_font(...)`, `ipx_enable(...)`, `ipx_connect(...)`, `ipx_disconnect()`, `glide_enable(...)`, `glide_set_resolution(...)`, and `set_machine_pc98(...)`.

#### Scenario: Subclasses override methods
- **GIVEN** `InProcessEngineRuntime` and `IpcEngineRuntime` are compiled
- **WHEN** the virtual methods are invoked
- **THEN** they SHALL delegate the call to their respective implementations

### Requirement: Application Routing
`Application` SHALL route all configuration, event, and action loop calls through the `runtime_` instance.

#### Scenario: Configuration calls routed
- **GIVEN** `Application` is initializing
- **WHEN** FFI configurations are set up
- **THEN** it SHALL call the virtual methods of `RuntimeHost`
- **AND** SHALL NOT directly call `legends_*` APIs (except `legends_create`)

#### Scenario: Events and Actions routed
- **GIVEN** `Application` handles actions or inputs
- **WHEN** input events, screenshots, or state captures occur
- **THEN** they SHALL call `RuntimeHost` methods
- **AND** SHALL NOT directly call `legends_*` APIs

### Requirement: AI Context Routing
`captureScreenContext` in `ai_screen_context.cpp` SHALL capture context using `RuntimeHost`.

#### Scenario: AI Screen Context routed
- **GIVEN** `captureScreenContext` is called
- **WHEN** retrieving screen text
- **THEN** it SHALL call `RuntimeHost::capture_text`
- **AND** SHALL NOT directly call `legends_capture_text`

### Requirement: Bypass Count Reduction
The allowlist and Graphify reports SHALL contain exactly 2 allowed bypasses: `legends_create` and `legends_destroy`.

#### Scenario: Direct bypasses verified
- **GIVEN** all routable bypasses have been migrated
- **WHEN** Graphify validates the codebase
- **THEN** `runtimehost_bypass_count` SHALL equal 2
- **AND** only `legends_create` and `legends_destroy` SHALL exist in the allowlist
