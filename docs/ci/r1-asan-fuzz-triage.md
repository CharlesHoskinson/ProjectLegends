# R1 ASan / UBSan / fuzz triage log

Updated 2026-07-15 during FINDING-001..005 remediation.

## FINDING-001 ASan clusters (run 29427786159 / earlier)

| Cluster | Example tests | ASan kind | Hypothesis / fix |
|---------|---------------|-----------|------------------|
| C1 | `EmulatorExceptionTest.*`, `IllegalCpuStateExceptionTest.*`, `FfiSafeCallTest.*` | `alloc-dealloc-mismatch (operator new vs free)` | **clang-18 + `-stdlib=libc++`** dual-runtime; free'd objects allocated via `new`. **Fix:** sanitizer CI uses **g++-13** (native libstdc++, no libc++). |
| C2 | `GuestMemoryTest.*OutOfBounds*` | mismatch on throw paths | Same as C1; re-evaluate after g++-13 switch |
| C3 | `DOSBoxContextTest.MoveConstruction/MoveAssignment` | Direct leak ~16MB guest RAM | Move ctor/assign omitted `memory` (and other raw-pointer owners); source `initialized_=false` skipped `MEM_FreeForContext`. **Fix:** transfer `memory`/`dma`/`vga.hw` and null source. |

### C++23 configure trap (post-26a52ed)

clang-18 + default libstdc++ **fails** `engine/cmake/test_cxx23.cpp`:

- libstdc++ `<expected>` is gated on `__cplusplus > 202002L && __cpp_concepts >= 202002L`
- clang-18 reports `__cpp_concepts 201907L` → `no template named 'expected' in namespace 'std'`
- **Sanitizers:** g++-13 (concepts 202002L natively). TSan also needs `-Wno-error=tsan` (libstdc++ `atomic_thread_fence` under `-Werror`).
- **Fuzz (must stay Clang for libFuzzer):** **clang-19** + pure libstdc++ (`__cpp_concepts=202002`). clang-18 + `-D__cpp_concepts=202002L` broke libstdc++ headers (`requires` parse errors).

## FINDING-002 UBSan

- Invalid enum loads for `dosbox_*_name` — fixed via `int` parameters (**SUCCESS** under g++-13 on run 29429960139).

## FINDING-004 Fuzz

1. Missing gsl-lite include — fixed (`gsl::gsl-lite-v1` link).
2. clang+libc++ vs libFuzzer/libstdc++ — dual-link `-lstdc++` still left `std::__cxx11` unresolved from `libclang_rt.fuzzer`. **Fix:** pure libstdc++ under **clang-19**.
3. Link deps — `fuzz_input_injection` → `legends_pal`; `fuzz_config_parser` → `platform_dirs.cpp`.
4. Smoke fail `corpus/config` missing — `generate_fuzz_corpus` now writes config seeds under `corpus/config/`.

## Method (local WSL after toolchain install)

```bash
cd /mnt/c/ProjectLegends
cmake -B build-asan -G Ninja \
  -DCMAKE_C_COMPILER=gcc-13 -DCMAKE_CXX_COMPILER=g++-13 \
  -DCMAKE_BUILD_TYPE=Debug \
  -DCMAKE_CXX_FLAGS="-fsanitize=address -fno-omit-frame-pointer" \
  -DCMAKE_C_FLAGS="-fsanitize=address -fno-omit-frame-pointer" \
  -DCMAKE_EXE_LINKER_FLAGS="-fsanitize=address -fno-omit-frame-pointer" \
  -DLEGENDS_BUILD_TESTS=ON -DLEGENDS_HEADLESS=ON
cmake --build build-asan
ASAN_OPTIONS=detect_leaks=1:halt_on_error=1 ctest --test-dir build-asan --output-on-failure
```
