# R1 ASan / UBSan / fuzz triage log

Updated 2026-07-15 during FINDING-001..005 remediation.

## FINDING-001 ASan clusters (run 29427786159 / earlier)

| Cluster | Example tests | ASan kind | Hypothesis / fix |
|---------|---------------|-----------|------------------|
| C1 | `EmulatorExceptionTest.*`, `IllegalCpuStateExceptionTest.*`, `FfiSafeCallTest.*` | `alloc-dealloc-mismatch (operator new vs free)` | **clang-18 + `-stdlib=libc++`** dual-runtime; free'd objects allocated via `new`. **Fix:** sanitizer CI uses clang-18 + libstdc++ from g++-13 (no libc++). |
| C2 | `GuestMemoryTest.*OutOfBounds*` | mismatch on throw paths | Same as C1; re-evaluate after libstdc++ switch |
| C3 | `DOSBoxContextTest.MoveConstruction/MoveAssignment` | Direct leak ~16MB | Possible real ownership bug; re-check after C1 noise cleared |

## FINDING-002 UBSan

- Invalid enum loads for `dosbox_*_name` — fixed via `int` parameters (green on prior run).

## FINDING-004 Fuzz

1. Missing gsl-lite include — fixed (`gsl::gsl-lite-v1` link).
2. clang+libc++ vs libFuzzer/libstdc++ link — fixed by **fuzz job → g++-13**.

## Method (local WSL after toolchain install)

```bash
cd /mnt/c/ProjectLegends
cmake -B build-asan -G Ninja \
  -DCMAKE_C_COMPILER=clang-18 -DCMAKE_CXX_COMPILER=clang++-18 \
  -DCMAKE_BUILD_TYPE=Debug \
  -DCMAKE_CXX_FLAGS="-fsanitize=address -fno-omit-frame-pointer" \
  -DCMAKE_C_FLAGS="-fsanitize=address -fno-omit-frame-pointer" \
  -DCMAKE_EXE_LINKER_FLAGS="-fsanitize=address -fno-omit-frame-pointer" \
  -DLEGENDS_BUILD_TESTS=ON -DLEGENDS_HEADLESS=ON
cmake --build build-asan
ASAN_OPTIONS=detect_leaks=1:halt_on_error=1 ctest --test-dir build-asan --output-on-failure
```
