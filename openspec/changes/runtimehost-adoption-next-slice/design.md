# Design: RuntimeHost Adoption Next Slice

## Technical Approach

The application keeps `engine_` as transitional state for not-yet-migrated direct APIs, while adding a borrowed `RuntimeHost` wrapper named `runtime_`. The wrapper is constructed immediately after `legends_create` succeeds.

The wrapper classes accept an `own_handle` flag:

- `own_handle = true` preserves factory-created RuntimeHost ownership.
- `own_handle = false` lets `Application` keep ownership of `engine_` during the migration.

`Application::shutdown` resets `runtime_` before calling `legends_destroy(engine_)`. With borrowed ownership, this prevents double destruction while keeping teardown order explicit.

## RuntimeHost Interface Additions

This slice adds only the methods needed by the selected hot path:

- `get_total_cycles`
- `is_frame_dirty`
- `inject_key_ext`
- `capture_audio`
- `capture_midi_audio`

Both `InProcessEngineRuntime` and `IpcEngineRuntime` delegate through the public `legends_*` API surface. In IPC builds, those symbols resolve through the proxy library. In monolithic builds, they resolve through the direct implementation.

## Application Migration

The migrated application methods are:

- `Application::run`
- `Application::processEvents`
- `Application::renderFrame`
- `Application::pumpAudio`

The migration preserves existing semantics:

- 16 ms stepping remains unchanged.
- extended key input remains distinct from normal key input.
- mouse motion and button delivery preserve existing values.
- RGB and text capture keep two-call query/fill behavior.
- audio capture continues to treat counts as `int16_t` elements and converts to stereo frames with `actual / 2`.

## Graphify Evidence

The Graphify overlay is regenerated after migration. Retired direct bypass keys are removed from `docs/architecture/runtimehost-bypass-allowlist.json`.

Acceptance requires:

- RuntimeHost method count increases.
- app RuntimeHost call-site count increases.
- app direct RuntimeHost bypass count decreases.
- allowlisted bypass count matches the remaining direct bypass count.
- strict Graphify validation passes with no new unallowlisted app-layer direct `legends_*` calls.

## Risks

- `runtime_` is assumed to exist after a successful engine creation path. If future init paths allow `run()` without engine creation, `Application::run` should gain an explicit guard.
- The IPC class still delegates through the public C API surface, so IPC correctness depends on the proxy implementation for each migrated method.
- Remaining lifecycle and configuration bypasses are intentional migration debt and should not be treated as precedent for new direct calls.
