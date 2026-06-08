# Delta for RuntimeHost Adoption

## ADDED Requirements

### Requirement: Application Hot Path Uses RuntimeHost

The application hot path SHALL route supported engine operations through `RuntimeHost` instead of directly calling public `legends_*` APIs from app-layer code.

#### Scenario: Frame loop stepping

- GIVEN `Application::run` executes a normal unpaused frame
- WHEN the engine is stepped
- THEN the call is made through `RuntimeHost::step_ms`
- AND app-layer code does not directly call `legends_step_ms` for that path

#### Scenario: Input injection

- GIVEN `Application::processEvents` forwards keyboard or mouse input to the engine
- WHEN the translated input is supported by `RuntimeHost`
- THEN the call is made through a RuntimeHost input method
- AND extended key events remain routed through a distinct extended-key method

#### Scenario: Rendering capture

- GIVEN `Application::renderFrame` needs framebuffer or text-mode data
- WHEN dirty state, RGB pixels, or text cells are queried
- THEN the call is made through RuntimeHost
- AND the two-call query/fill capture contract is preserved

#### Scenario: Audio capture

- GIVEN `Application::pumpAudio` pulls PCM or MIDI samples
- WHEN samples are queried and captured
- THEN the call is made through RuntimeHost
- AND sample counts continue to represent `int16_t` elements

### Requirement: RuntimeHost Handle Ownership Is Explicit

RuntimeHost concrete wrappers SHALL distinguish owned handles from borrowed handles so application-owned engine handles are not destroyed by borrowed wrappers.

#### Scenario: Application borrowed wrapper teardown

- GIVEN `Application` owns `engine_`
- AND `runtime_` wraps `engine_` in borrowed mode
- WHEN `Application::shutdown` resets `runtime_`
- THEN the RuntimeHost destructor does not call `legends_destroy`
- AND `Application::shutdown` remains responsible for destroying `engine_`

### Requirement: Graphify RuntimeHost Adoption Evidence

Graphify SHALL provide auditable evidence that app-layer RuntimeHost bypass debt decreased.

#### Scenario: Migrated bypass entries are retired

- GIVEN a direct app-layer `legends_*` call has been replaced by RuntimeHost
- WHEN Graphify enrichment is regenerated
- THEN the RuntimeHost bypass count decreases
- AND the matching allowlist key is removed

#### Scenario: New bypasses are rejected

- GIVEN new app-layer code introduces a direct `legends_*` call
- WHEN `scripts/check_graphify_enrichment.py` runs in strict mode
- THEN the check fails unless the call is deliberately allowlisted with audit justification
