## 1. MSan CI Job

- [ ] 1.1 Add MSan job to `ci.yml` (separate from sanitizer matrix)
- [ ] 1.2 Configure Clang with `-fsanitize=memory -fPIE -pie -stdlib=libc++`
- [ ] 1.3 Run tests under MSan; fix or document suppressions

## 2. Coverage Dashboard

- [ ] 2.1 Add Codecov upload step to existing lcov coverage job in `ci.yml`
- [ ] 2.2 Add coverage badge to `README.md`

## 3. Wiring Existing Tools

- [ ] 3.1 Add `check_gsl_lite_usage.py` execution to `sprint2-checks.yml`
- [ ] 3.2 Verify it fails the build on gsl-lite usage violations

## 4. Input Fuzzing

- [ ] 4.1 Create `tests/fuzz/fuzz_input_injection.cpp` exercising key/mouse event injection
- [ ] 4.2 Add as third harness in existing fuzz CI job (60s smoke, ASan enabled)

## 5. PIC Unit Tests

- [ ] 5.1 Create `tests/test_pic.cpp` with test for IRQ raise (set IRR, check ISR after ack)
- [ ] 5.2 Add test for ISR/IRR transitions
- [ ] 5.3 Add test for cascade mode (slave through master IRQ2)
- [ ] 5.4 Add test for auto-EOI (ISR cleared automatically)

## 6. Verification

- [ ] 6.1 MSan job passes (or documented suppressions)
- [ ] 6.2 Coverage badge visible on README
- [ ] 6.3 Input fuzz runs 60s clean
- [ ] 6.4 All PIC tests pass
