## Status: ~80% COMPLETE

4 sanitizers in CI (ASan/UBSan/TSan/MSan), 3 fuzz targets (including input injection), 11 TLA+ model checks, lcov coverage, gsl-lite check wired. Remaining: MSan suppression cleanup, coverage README badge, PIC C++ unit tests. See AUDIT.md CI section for full pipeline inventory.

## Context

CI now covers: 4 sanitizers (ASan, UBSan, TSan, MSan), 3 fuzz targets (60s smoke), 11 TLA+ model checks, lcov coverage, clang-tidy, gsl-lite usage check. Remaining gaps: coverage README badge, PIC C++ unit tests matching TLA+ spec coverage.

## Goals / Non-Goals

**Goals:**
- MSan CI job (Clang + instrumented libc++)
- Codecov integration with README badge
- Wire `check_gsl_lite_usage.py` into sprint2-checks
- Input injection fuzz target
- PIC C++ unit tests matching TLA+ spec coverage

**Non-Goals:**
- Differential determinism fuzzer (blocked on Phase A)
- DOS program execution test (blocked on Phase A)
- Expanding clang-tidy scope (diminishing returns)

## Decisions

**MSan separate job:** MSan is incompatible with ASan and TSan. Add it as a standalone job in ci.yml, not in the sanitizer matrix. Use `clang` with `-fsanitize=memory -fPIE -pie` and instrumented libc++ (`-stdlib=libc++` built with MSan).

**Codecov over Coveralls:** Codecov has better GitHub integration, supports lcov format natively, and the free tier covers open-source. Upload the existing lcov artifact.

**PIC unit tests structure:** Create `tests/test_pic.cpp`. Test 4 scenarios: IRQ raise (set IRR, check ISR after ack), ISR/IRR transitions, cascade (slave through master IRQ2), auto-EOI (ISR cleared automatically). These mirror the TLA+ PIC spec properties.

**Input fuzz target:** `fuzz_input_injection.cpp` exercises `legends_key_event`, `legends_key_event_ext`, `legends_mouse_event` with random data. Run under ASan in the existing fuzz CI job (add as third harness alongside the two state-load fuzzers).

## Risks / Trade-offs

- [MSan with instrumented libc++ is complex to set up] → Use pre-built LLVM packages; document the exact setup
- [Codecov free tier limits] → Sufficient for this project's size
- [PIC tests may not catch all device-model bugs] → They complement TLA+ specs, not replace them
