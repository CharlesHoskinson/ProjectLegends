## 1. OpenSpec

- [ ] 1.1 Validate this change with `openspec.cmd validate runtimehost-proxy-device-command-parity --strict --json`.
- [ ] 1.2 Keep this task list current as implementation progresses.

## 2. IPC Message Layer

- [ ] 2.1 Add request/response structs for command-style device, input, network, and capability APIs.
- [ ] 2.2 Implement safe serialization/deserialization for string, bool, integer, and sample payload messages.
- [ ] 2.3 Add message round-trip and truncation tests.

## 3. Proxy And Dispatcher

- [ ] 3.1 Replace direct proxy `LEGENDS_ERR_NOT_SUPPORTED` returns for implemented APIs with IPC calls.
- [ ] 3.2 Add dispatcher cases for each new request type.
- [ ] 3.3 Preserve direct C ABI error semantics for null pointers, invalid strings, and output parameters.
- [ ] 3.4 Leave callback, video capture, and TTF APIs truthful unless implemented end to end.

## 4. Tests And Docs

- [ ] 4.1 Add dispatcher tests for representative command, string, query, and MIDI sample APIs.
- [ ] 4.2 Update capability truth JSON and Markdown matrix.
- [ ] 4.3 Update RuntimeHost design docs if proxy caveats change.

## 5. Verification

- [ ] 5.1 `python scripts/check_capability_matrix.py --repo .`
- [ ] 5.2 `cmake --preset dev`
- [ ] 5.3 `cmake --build --preset dev`
- [ ] 5.4 `build/dev/legends_unit_tests.exe`
