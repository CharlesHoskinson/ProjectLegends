## Why

Adopting the `RuntimeHost` abstraction in `SaveManager` continues the process of isolating the application frontend from the specific emulation backend FFI interface. By routing save/load operations through `RuntimeHost`, we ensure that save/load functionalities remain backend-agnostic (essential for process isolation).

## What app-layer bypass debt exists today

Currently, the application contains 38 direct FFI `legends_*` calls, including three in `SaveManager`:
- Query call to `legends_save_state`
- Fill call to `legends_save_state`
- Loading call to `legends_load_state`

## What Changes

This sprint will migrate these three state management calls behind the `RuntimeHost` abstraction. Specifically:
- `SaveManager` will be updated with new overloads accepting `RuntimeHost&`.
- The main application loop inside `Application::init` and `Application::registerActionHandlers` will pass `*runtime_` to `SaveManager` save/load methods.
- The direct FFI calls inside `SaveManager` will be replaced with `runtime.save_state` and `runtime.load_state`.

## What remains explicitly out of scope

- Migration of joystick event FFI calls (`legends_joystick_event`).
- Migration of mounting FFI calls (`legends_mount_drive`, `legends_unmount_drive`) in the setup/init phase.
- Migration of lifecycle configuration FFI calls (e.g. `legends_create`, `legends_set_log_callback`).

## How Codex will audit the result

Codex will verify:
1. **SaveManager Overloads**: Check that `saveToSlot`, `loadFromSlot`, and `recoverAutosave` have new overloads accepting a non-owning `RuntimeHost&` reference.
2. **Handle-backwards compatibility**: Verify that raw `legends_handle` overloads are preserved and delegate to `RuntimeHost` overloads.
3. **Application Call Sites**: Ensure that the application shell calls the new `RuntimeHost`-backed paths.
4. **Allowlist Cleanup**: Verify the allowlist count drops to 35.
5. **Graphify Validation**: Confirm the regenerated AST and enrichment overlay validate successfully.
