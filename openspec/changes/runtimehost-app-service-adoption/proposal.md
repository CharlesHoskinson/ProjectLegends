## Why

Migrating the remaining application-layer FFI direct bypasses behind `RuntimeHost` completes the decoupling of the application shell from the specific emulation backend API. This enables full process isolation (supporting `IpcEngineRuntime` in production) and ensures clean boundaries.

## What app-layer bypass debt exists today

Today, there are 35 direct FFI `legends_*` bypasses allowed, which cover application initialization (drives, sound, graphics, logging, machines), event handlers (joystick events, screenshots, input events), and AI screen context capture.

## What Changes

This sprint will migrate all 33 routable bypasses behind `RuntimeHost`. Specifically:
- **`RuntimeHost` Interface Extension**: Add 16 virtual methods delegating to FFI configurations and control calls.
- **Application Routing**: Update all FFI calls in `Application` init, action, and event pumps to route through `runtime_`.
- **AI Screen Context Capture**: Convert `ai_screen_context.cpp` to use `RuntimeHost` instead of `legends_handle`.
- **Bypass Allowlist**: Shrink the allowlist to exactly 2 entries: `legends_create` and `legends_destroy`.

## What remains explicitly out of scope

- Migration of `legends_create` and `legends_destroy` FFI lifecycle boundaries.
- Modifying engine lifecycle management or handle storage inside `Application`.

## How Codex will audit the result

Codex will audit:
1. **Delegation Completeness**: Verify all 16 new virtual functions are fully implemented in `InProcessEngineRuntime` and `IpcEngineRuntime`.
2. **AI Context Routing**: Confirm `ai_screen_context.cpp` does not contain any direct FFI calls.
3. **Application Routing Integrity**: Verify all routable call sites in `Application` use the `runtime_` pointer.
4. **Bypass Count**: Confirm Graphify reports exactly 2 bypasses.
