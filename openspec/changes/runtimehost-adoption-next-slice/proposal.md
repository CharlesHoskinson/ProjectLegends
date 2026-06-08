## Why

ProjectLegends is moving application-layer engine access behind `RuntimeHost` so the shell can route through either the in-process backend or the IPC/proxy backend without new direct `legends_*` call sites leaking into app code.

The current Graphify guard identifies app-layer direct `legends_*` calls as RuntimeHost bypass debt. Before this change, the application had 53 allowlisted direct bypasses. The hot path in `Application::run`, `Application::processEvents`, `Application::renderFrame`, and `Application::pumpAudio` is the highest-value migration slice because those paths define normal frame execution, input delivery, rendering, and audio pumping.

## What Changes

This change migrates the supported application hot path to `RuntimeHost`:

- engine stepping and total-cycle reporting
- keyboard and mouse input injection
- dirty-frame checks
- RGB and text capture used by rendering
- PCM and MIDI audio capture used by audio pumping

The change also updates Graphify evidence and removes retired bypass entries from `docs/architecture/runtimehost-bypass-allowlist.json`.

## Capabilities

### New Capabilities

- `runtimehost-adoption`: Application hot-path engine operations route through `RuntimeHost`, and Graphify verifies reduced bypass debt.

### Modified Capabilities

- `graphify-runtimehost-guard`: Existing app-layer direct `legends_*` bypasses remain tracked as migration debt, with 15 retired entries removed by this slice.

## Impact

- `include/legends/runtime_host.h` -- add narrow RuntimeHost methods and ownership-aware constructors
- `src/app/runtime_host.cpp` -- implement direct/proxy RuntimeHost delegations and borrowed ownership
- `src/app/application.h` -- add `runtime_` member
- `src/app/application.cpp` -- route selected hot-path calls through `runtime_`
- `docs/architecture/runtimehost-bypass-allowlist.json` -- remove retired hot-path bypass keys
- `graphify-out/projectlegends-enrichment.json` -- regenerated Graphify overlay
- `docs/architecture/graphify-enrichment-report.md` -- regenerated Graphify summary

## Out Of Scope

This change does not migrate every app-layer direct API call. The remaining allowlisted debt includes:

- engine creation and destruction lifecycle
- setup/configuration APIs for MIDI, printer, TTF, IPX, Glide, and PC-98
- action handler capture helpers
- joystick input
- AI screen context capture
- `SaveManager` save/load operations

Those families need separate RuntimeHost design work because they either require broader interface additions or touch application lifecycle boundaries.
