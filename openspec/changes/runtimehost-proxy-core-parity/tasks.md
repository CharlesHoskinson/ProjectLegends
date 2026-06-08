## 1. OpenSpec

- [ ] 1.1 Validate this change with `openspec.cmd validate runtimehost-proxy-core-parity --strict --json`.
- [ ] 1.2 Keep this task list current as implementation progresses.

## 2. IPC Message Layer

- [ ] 2.1 Add/complete message structs for config, text capture, save/load, determinism verification, and last-error APIs.
- [ ] 2.2 Implement serialization/deserialization with bounds checks for all new fixed and variable payload messages.
- [ ] 2.3 Add unit tests for message round-trips and too-small buffers.

## 3. Proxy And Dispatcher

- [ ] 3.1 Implement proxy client logic for all six core APIs without direct `LEGENDS_ERR_NOT_SUPPORTED` returns.
- [ ] 3.2 Add dispatcher cases that forward to direct `legends_*` implementations and serialize responses.
- [ ] 3.3 Preserve public C ABI null-pointer, null-handle, and buffer-too-small behavior.

## 4. Tests And Truth Matrix

- [ ] 4.1 Add focused dispatcher tests for the six APIs.
- [ ] 4.2 Update `docs/architecture/capability_truth.json`.
- [ ] 4.3 Update `docs/architecture/2026-06-08-public-capability-truth-matrix.md`.
- [ ] 4.4 Run `python scripts/check_capability_matrix.py --repo .`.

## 5. Verification

- [ ] 5.1 `cmake --preset dev`
- [ ] 5.2 `cmake --build --preset dev`
- [ ] 5.3 `build/dev/legends_abi_test.exe`
- [ ] 5.4 `build/dev/legends_unit_tests.exe`
