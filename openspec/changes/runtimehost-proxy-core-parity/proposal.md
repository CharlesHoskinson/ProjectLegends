## Why

`Application` now routes almost all engine work through `RuntimeHost`, but `IpcEngineRuntime` still delegates to C ABI proxy functions that return `LEGENDS_ERR_NOT_SUPPORTED` for core app features. Save/load, text capture, configuration reads, determinism verification, and last-error reporting are required for a credible out-of-process runtime.

## What Changes

Implement IPC request/response parity for the core proxy APIs:

- `legends_get_config`
- `legends_capture_text`
- `legends_save_state`
- `legends_load_state`
- `legends_verify_determinism`
- `legends_get_last_error`

This includes message structs, serialization, proxy client logic, engine dispatcher cases, focused tests, and capability truth updates.

## Scope

In scope:

- Request/response IPC over the existing control channel.
- Variable-size response payloads for text cells, save-state bytes, and error strings.
- Two-call C ABI semantics for query/fill APIs.
- Dispatcher tests and message serialization tests.

Out of scope:

- Shared-memory framebuffer/audio writer completion.
- Callback streaming over IPC.
- Video capture proxy support.
- Replacing `RuntimeHost` lifecycle ownership.

## Audit Strategy

Codex will audit the wire format, buffer-size behavior, dispatcher forwarding, truth matrix updates, and tests proving these APIs no longer return unsupported in proxy mode.
