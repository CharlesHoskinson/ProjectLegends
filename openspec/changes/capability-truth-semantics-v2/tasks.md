## 1. OpenSpec

- [ ] 1.1 Validate this change with `openspec.cmd validate capability-truth-semantics-v2 --strict --json`.
- [ ] 1.2 Keep this task list current as implementation progresses.

## 2. Manifest Semantics

- [ ] 2.1 Extend `docs/architecture/capability_truth.json` with route-vs-support semantics.
- [ ] 2.2 Update all 50 public API entries.
- [ ] 2.3 Keep `legends_joystick_event` partial unless functional direct behavior is implemented.

## 3. Validator

- [ ] 3.1 Update `scripts/check_capability_matrix.py` to validate new statuses and route fields.
- [ ] 3.2 Reject `proxy-supported` overclaims for partial/unsupported direct APIs without explicit evidence.
- [ ] 3.3 Emit a summary count by proxy status and route status.

## 4. Documentation

- [ ] 4.1 Sync `docs/architecture/2026-06-08-public-capability-truth-matrix.md`.
- [ ] 4.2 Add a routed-vs-supported summary section or companion report.

## 5. Verification

- [ ] 5.1 `python scripts/check_capability_matrix.py --repo .`
- [ ] 5.2 `cmake --preset dev`
- [ ] 5.3 `cmake --build --preset dev`
- [ ] 5.4 `build/dev/legends_unit_tests.exe`
