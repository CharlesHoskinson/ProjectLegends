## 1. OpenSpec

- [ ] 1.1 Validate this change with `openspec.cmd validate ipc-wire-adversarial-gates --strict --json`.
- [ ] 1.2 Keep this task list current as implementation progresses.

## 2. Malformed IPC Message Tests

- [ ] 2.1 Add tests for truncated dynamic payloads.
- [ ] 2.2 Add tests for oversized dynamic payloads.
- [ ] 2.3 Add tests for declared-size and actual-size mismatch.
- [ ] 2.4 Add tests for odd typed-array byte counts.
- [ ] 2.5 Add tests for malformed string-backed request lengths.

## 3. Dispatcher Adversarial Tests

- [ ] 3.1 Add dispatcher tests proving capture handlers query required size before allocation.
- [ ] 3.2 Add dispatcher tests for too-small caller counts.
- [ ] 3.3 Add dispatcher tests for malformed dynamic requests returning IPC errors.

## 4. Documentation

- [ ] 4.1 Add or update an IPC safety note under `docs/architecture`.
- [ ] 4.2 Record the dynamic message families covered by tests.

## 5. Verification

- [ ] 5.1 `cmake --preset dev`
- [ ] 5.2 `cmake --build --preset dev`
- [ ] 5.3 `build/dev/legends_unit_tests.exe --gtest_filter=IpcMessagesTest.*:EngineDispatcherTest.*`
- [ ] 5.4 `build/dev/legends_unit_tests.exe`
