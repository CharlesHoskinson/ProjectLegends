## 1. RuntimeHost Interface Expansion

- [x] 1.1 Declare the 16 new virtual methods in `RuntimeHost` in `runtime_host.h`.
- [x] 1.2 Implement the overrides in `InProcessEngineRuntime` and `IpcEngineRuntime` in `runtime_host.cpp`.

## 2. Application Routing

- [x] 2.1 Route FFI config calls inside `Application::init` to `runtime_`.
- [x] 2.2 Route joystick events in `Application::processEvents` to `runtime_`.
- [x] 2.3 Route action handlers (Screenshot, SaveState thumbnail, Reset, TextInput, GetCursor) to `runtime_`.

## 3. AI Screen Context Migration

- [x] 3.1 Declare and implement the `RuntimeHost&` overload for `captureScreenContext` in `ai_screen_context.h/cpp`.
- [x] 3.2 Delegate the raw FFI overload to the `RuntimeHost` overload using `InProcessEngineRuntime`.

## 4. Allowlist & Graphify

- [x] 4.1 Update `docs/architecture/runtimehost-bypass-allowlist.json` to keep only `legends_create` and `legends_destroy`.
- [x] 4.2 Regenerate Graphify and verify bypass count is exactly 2.

## 5. Verification

- [x] 5.1 ABI tests pass.
- [x] 5.2 Unit tests pass.
- [x] 5.3 Strict Graphify validations pass.
