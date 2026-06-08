## 1. OpenSpec

- [ ] 1.1 Validate this change with `openspec.cmd validate abi-parity-negative-gates --strict --json`.
- [ ] 1.2 Keep this task list current as implementation progresses.

## 2. ABI Contract Manifest

- [ ] 2.1 Create `docs/architecture/abi_parity_contracts.json`.
- [ ] 2.2 Add entries for all newly proxied RuntimeHost/proxy APIs.
- [ ] 2.3 Record explicit `not_applicable` reasons for APIs where a case does not apply.

## 3. Validator

- [ ] 3.1 Create `scripts/check_abi_parity_contracts.py`.
- [ ] 3.2 Validate exported API names against `include/legends/legends_embed.h`.
- [ ] 3.3 Validate evidence files and evidence tokens.
- [ ] 3.4 Add failure messages that point to the missing API/case.

## 4. Tests

- [ ] 4.1 Add or extend unit tests for null handles and null required output pointers.
- [ ] 4.2 Add or extend unit tests for query/fill and undersized buffer semantics.
- [ ] 4.3 Add or extend tests proving output structs start from documented defaults.

## 5. Verification

- [ ] 5.1 `python scripts/check_abi_parity_contracts.py --repo .`
- [ ] 5.2 `cmake --preset dev`
- [ ] 5.3 `cmake --build --preset dev`
- [ ] 5.4 `build/dev/legends_abi_test.exe`
- [ ] 5.5 `build/dev/legends_unit_tests.exe`
