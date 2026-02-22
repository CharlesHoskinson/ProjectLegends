## Why

CI already covers fuzzing, TLA+, coverage, TSan, ASan, UBSan, and clang-tidy (correcting the audit). But MSan is missing, coverage has no dashboard/badge, `check_gsl_lite_usage.py` is unwired, and several test categories (input fuzzing, PIC unit tests, DOS execution) don't exist yet.

## What Changes

- Add MSan CI job (separate from matrix, incompatible with ASan/TSan)
- Add Codecov upload + README badge
- Wire `check_gsl_lite_usage.py` into sprint2-checks.yml
- Create input injection fuzz target
- Add PIC/PIT C++ unit tests (TLA+ specs exist, no C++ equivalents)
- Add differential determinism fuzzer and DOS program execution test (after Phase A)

## Capabilities

### New Capabilities
- `ci-coverage`: Fill remaining CI gaps and add missing test categories

### Modified Capabilities

(none)

## Impact

- `.github/workflows/ci.yml` -- MSan job, Codecov upload
- `.github/workflows/sprint2-checks.yml` -- gsl-lite check
- `tests/fuzz/fuzz_input_injection.cpp` -- new fuzz target
- `tests/` -- PIC unit tests, DOS execution test
- `README.md` -- coverage badge
