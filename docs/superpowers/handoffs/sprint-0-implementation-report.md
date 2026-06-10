# Sprint 0 Implementation Report

Project: Project Legends (`C:\projectLegends`)

Branch: `sprint-0/stop-the-bleeding`

Base: `ce6a847daf5ced4e72892511a96d28af9795fd0e`

Head: `3ff9754f3d4fbc41cf943d54c9f675bc65c250af`

Note: the committed branch diff is the 11-file Sprint 0 diff shown below. The worktree is not clean because `.claude/commands/`, `.claude/skills/`, and these handoff files are untracked.

## Verification Summary

Default dev configure:

```text
cmd.exe /c "call ""C:\Program Files (x86)\Microsoft Visual Studio\18\BuildTools\Common7\Tools\VsDevCmd.bat"" -arch=x64 -host_arch=x64 && ""C:\Program Files\CMake\bin\cmake.exe"" --fresh --preset dev -DCMAKE_C_COMPILER=cl -DCMAKE_CXX_COMPILER=cl -DCMAKE_MAKE_PROGRAM=""C:\Users\charl\AppData\Local\Microsoft\WinGet\Packages\Ninja-build.Ninja_Microsoft.Winget.Source_8wekyb3d8bbwe\ninja.exe"" -DCMAKE_CXX_FLAGS=""/EHsc /wd4875"""
Exit code: 0
Compiler: MSVC 19.51.36244.0
CMake preset: dev
Generator: Ninja 1.13.2
```

Full dev build:

```text
cmd.exe /c "call ""C:\Program Files (x86)\Microsoft Visual Studio\18\BuildTools\Common7\Tools\VsDevCmd.bat"" -arch=x64 -host_arch=x64 && ""C:\Program Files\CMake\bin\cmake.exe"" --build --preset dev"
Exit code: 0
[306/306] Linking CXX executable legends_unit_tests.exe
```

The build emitted existing warning classes from old engine/test sources and a command-line `/std` override warning. I did not establish a warning-free baseline for the repository. No source diagnostic attributable to the Sprint 0 changes was observed in the final build output.

Full ctest:

```text
cmd.exe /c "call ""C:\Program Files (x86)\Microsoft Visual Studio\18\BuildTools\Common7\Tools\VsDevCmd.bat"" -arch=x64 -host_arch=x64 && ""C:\Program Files\CMake\bin\ctest.exe"" --test-dir build/dev --output-on-failure"
Exit code: 0
100% tests passed, 0 tests failed out of 4512
Total Test time (real) = 213.99 sec
The following tests did not run: 48 skipped/not-run tests listed by ctest
```

Workflow validation:

```text
C:\Users\charl\AppData\Local\Microsoft\WinGet\Packages\rhysd.actionlint_Microsoft.Winget.Source_8wekyb3d8bbwe\actionlint.exe .github/workflows/ci.yml .github/workflows/pal-ci.yml
Exit code: 0
No diagnostics.
```

Fuzz verification:

```text
$asan = 'C:\Program Files\LLVM\lib\clang\22\lib\windows'; $env:Path = $asan + ';C:\Program Files\LLVM\bin;' + [Environment]::GetEnvironmentVariable('Path','Machine') + ';' + [Environment]::GetEnvironmentVariable('Path','User'); build\fuzz\tests\fuzz\fuzz_engine_memory_blob.exe build\fuzz\tests\fuzz\corpus\engine_memory_blob -max_len=1048576 -max_total_time=600 -print_final_stats=1
Exit code: 0
#2223899 DONE cov: 17 ft: 17 corp: 4/4044b lim: 1048576 exec/s: 3700 rss: 332Mb
Done 2223899 runs in 601 second(s)
stat::number_of_executed_units: 2223899
fuzz_engine_memory_blob: crc_valid_ram_inputs=2223898 rle_decode_reached=1061747 oversized_ram_rejections=52388
```

Diffstat:

```text
 .github/workflows/ci.yml                    |  57 ++++-
 .github/workflows/pal-ci.yml                |   2 +-
 CMakeLists.txt                              |   2 +
 LICENSE                                     |  73 ++++--
 engine/src/misc/dosbox_library.cpp          |  77 +++++-
 engine/tests/unit/test_dosbox_library.cpp   |  94 +++++++
 src/legends/legends_embed_api.cpp           |  75 +++---
 tests/fuzz/CMakeLists.txt                   |  48 +++-
 tests/fuzz/fuzz_engine_memory_blob.cpp      | 378 ++++++++++++++++++++++++++++
 tests/fuzz/generate_corpus.cpp              |  66 +++++
 tests/unit/test_legends_embed_lifecycle.cpp |  24 ++
 11 files changed, 815 insertions(+), 81 deletions(-)
```

## Item 0.1 - mem-01

Status: complete

Commit: `c4f5916a6c134ad5d8594761be5add5f2a5a2964`

Files changed:

- `engine/src/misc/dosbox_library.cpp`: lines 1178-1220, 1358-1368, 1493-1527
- `engine/tests/unit/test_dosbox_library.cpp`: lines 726-762, 1055-1096

Test added: `DOSBoxLibraryEngineStateTest.LoadRejectsOversizedSerializedMemorySizeBeforeRamDecode`

Pre-fix failing output captured:

```text
build\dev\engine\tests\aibox_unit_tests.exe --gtest_filter=DOSBoxLibraryEngineStateTest.LoadRejectsOversizedSerializedMemorySizeBeforeRamDecode --gtest_color=no
Exit code: 1
Expected equality of these values:
  err
    Which is: 0
  -8
Expected equality of these values:
  std::memcmp(hash_before, hash_after, sizeof(hash_before))
    Which is: 1
  0
[  FAILED  ] DOSBoxLibraryEngineStateTest.LoadRejectsOversizedSerializedMemorySizeBeforeRamDecode
```

Post-fix verification:

```text
build\dev\engine\tests\aibox_unit_tests.exe --gtest_filter=DOSBoxLibraryEngineStateTest.LoadRejectsOversizedSerializedMemorySizeBeforeRamDecode --gtest_color=no
Exit code: 0
[ RUN      ] DOSBoxLibraryEngineStateTest.LoadRejectsOversizedSerializedMemorySizeBeforeRamDecode
[       OK ] DOSBoxLibraryEngineStateTest.LoadRejectsOversizedSerializedMemorySizeBeforeRamDecode (1 ms)
[  PASSED  ] 1 test.
```

Implementation notes:

- Rejects serialized `EngineStateMemory::size` values larger than the live allocation before mutating state.
- Validates V5 directory table offsets and sizes against `header.total_size`.
- Validates RAM and VRAM decoded sizes against live capacities.
- Does not overwrite the live allocation descriptor from blob contents.

Deviations: none.

## Item 0.2 - mem-02

Status: complete

Commit: `b7cc4f8017e60ee73f7856fc19c8ae10bd813f10`

Files changed:

- `CMakeLists.txt`: lines 214, 803
- `src/legends/legends_embed_api.cpp`: lines 70-75, 835-963
- `tests/unit/test_legends_embed_lifecycle.cpp`: lines 13-15, 132-154

Test added: `DosboxxEmbedLifecycleTest.CreateLateFailureReleasesEngineHandle`

Pre-fix failing output captured:

```text
build\dev\legends_unit_tests.exe --gtest_filter=DosboxxEmbedLifecycleTest.CreateLateFailureReleasesEngineHandle --gtest_color=no
Exit code: 1
tests\unit\test_legends_embed_lifecycle.cpp(145): error: Expected equality of these values:
  err
    Which is: -3
  0
tests\unit\test_legends_embed_lifecycle.cpp(146): error: Expected: (recovered) != (nullptr), actual: NULL vs (nullptr)
[  FAILED  ] DosboxxEmbedLifecycleTest.CreateLateFailureReleasesEngineHandle
```

Post-fix verification:

```text
build\dev\legends_unit_tests.exe --gtest_filter=DosboxxEmbedLifecycleTest.CreateLateFailureReleasesEngineHandle --gtest_color=no
Exit code: 0
[ RUN      ] DosboxxEmbedLifecycleTest.CreateLateFailureReleasesEngineHandle
[       OK ] DosboxxEmbedLifecycleTest.CreateLateFailureReleasesEngineHandle (1 ms)
[  PASSED  ] 1 test.
```

Implementation notes:

- Adds test-only late failure injection under `LEGENDS_TESTING`.
- Routes post-allocation `legends_create` failures through one cleanup lambda.
- Destroys acquired engine handles, resets machine state, clears `g_active_instance`, and deletes the instance before returning an error.

Deviations: none.

## Item 0.3 - ci-01, test-ci-01, ci-04

Status: complete

Commit: `7aabd5285c983e17eebce543d67270dcf1a9d1d7`

Files changed:

- `.github/workflows/ci.yml`: lines 20-23, 328-373, 478-555
- `.github/workflows/pal-ci.yml`: lines 5, 13-14

Verification:

```text
C:\Users\charl\AppData\Local\Microsoft\WinGet\Packages\rhysd.actionlint_Microsoft.Winget.Source_8wekyb3d8bbwe\actionlint.exe .github/workflows/ci.yml .github/workflows/pal-ci.yml
Exit code: 0
No diagnostics.
```

Trigger trace from final YAML:

- Push to `master`: `ci.yml` push branch filter matches; sanitizer and fuzz job-level `if` expressions match `github.ref == 'refs/heads/master'`; ASan and UBSan are required, TSan/MSan remain `continue-on-error`; 30s fuzz smoke runs.
- PR to `master`: `ci.yml` pull_request branch filter matches; sanitizer and fuzz job-level `if` expressions match all PRs; ASan and UBSan are required; 30s fuzz smoke runs; 60s scheduled/manual fuzz steps do not run.
- PR to `develop`: `ci.yml` and `pal-ci.yml` pull_request branch filters include `develop`; sanitizer and fuzz job-level `if` expressions match all PRs in `ci.yml`; ASan and UBSan are required; 30s fuzz smoke runs.

TSan/MSan remain allow-failure with dated 2026-06-10 Sprint 7 exit-plan comments.

Deviations: none.

## Item 0.4 - lic-01

Status: complete

Commit: `40ca8fddeeb3c64b6ffda64f6b0e43ad8c382055`

Files changed:

- `LICENSE`: lines 1-50

Verification:

```text
git diff -- COPYING NOTICE
Exit code: 0
No output.
```

Implementation notes:

- Replaced the root bare MIT grant with a multi-component overview.
- Names current top-level component license facts, including `engine/`, `src/`, `include/`, `external/`, tests, benchmarks, scripts, CMake/build metadata, docs/specs, `COPYING`, and `NOTICE`.
- Explicitly does not resolve GPL-2.0-only versus GPL-2.0-or-later.
- No source SPDX headers changed.

Deviations: none.

## Item 0.5 - test-fuzz-05 partial

Status: complete

Commit: `3ff9754f3d4fbc41cf943d54c9f675bc65c250af`

Files changed:

- `tests/fuzz/fuzz_engine_memory_blob.cpp`: lines 1-378
- `tests/fuzz/generate_corpus.cpp`: lines 68-93, 241
- `tests/fuzz/CMakeLists.txt`: lines 24-55, 169-189, 255-269
- `.github/workflows/ci.yml`: lines 509-555

Fuzz target added: `fuzz_engine_memory_blob`

Verification:

```text
cmd.exe /c "call ""C:\Program Files (x86)\Microsoft Visual Studio\18\BuildTools\Common7\Tools\VsDevCmd.bat"" -arch=x64 -host_arch=x64 && set ""PATH=C:\Program Files\LLVM\bin;C:\Users\charl\AppData\Local\Microsoft\WinGet\Packages\Ninja-build.Ninja_Microsoft.Winget.Source_8wekyb3d8bbwe;C:\Program Files\CMake\bin;%PATH%"" && cmake --fresh -B build/fuzz -G Ninja -DCMAKE_BUILD_TYPE=Release -DCMAKE_C_COMPILER=""C:/Program Files/LLVM/bin/clang.exe"" -DCMAKE_CXX_COMPILER=""C:/Program Files/LLVM/bin/clang++.exe"" -DCMAKE_MAKE_PROGRAM=""C:/Users/charl/AppData/Local/Microsoft/WinGet/Packages/Ninja-build.Ninja_Microsoft.Winget.Source_8wekyb3d8bbwe/ninja.exe"" -DCMAKE_MSVC_RUNTIME_LIBRARY=MultiThreaded -DENABLE_FUZZING=ON -DENABLE_ASAN=ON -DLEGENDS_BUILD_TESTS=ON -DLEGENDS_HEADLESS=ON"
Exit code: 0
```

```text
cmd.exe /c "call ""C:\Program Files (x86)\Microsoft Visual Studio\18\BuildTools\Common7\Tools\VsDevCmd.bat"" -arch=x64 -host_arch=x64 && set ""PATH=C:\Program Files\LLVM\bin;C:\Users\charl\AppData\Local\Microsoft\WinGet\Packages\Ninja-build.Ninja_Microsoft.Winget.Source_8wekyb3d8bbwe;C:\Program Files\CMake\bin;%PATH%"" && cmake --build build/fuzz --target fuzz_engine_memory_blob generate_fuzz_corpus"
Exit code: 0
```

```text
build\fuzz\tests\fuzz\generate_fuzz_corpus.exe build\fuzz\tests\fuzz\corpus
Exit code: 0
Created engine_memory_blob/fresh_v5_engine_state.bin
Created engine_memory_blob/stepped_v5_engine_state.bin
Created engine_memory_blob/reset_v5_engine_state.bin
```

```text
$asan = 'C:\Program Files\LLVM\lib\clang\22\lib\windows'; $env:Path = $asan + ';C:\Program Files\LLVM\bin;' + [Environment]::GetEnvironmentVariable('Path','Machine') + ';' + [Environment]::GetEnvironmentVariable('Path','User'); build\fuzz\tests\fuzz\fuzz_engine_memory_blob.exe build\fuzz\tests\fuzz\corpus\engine_memory_blob -max_len=1048576 -max_total_time=600 -print_final_stats=1
Exit code: 0
Done 2223899 runs in 601 second(s)
fuzz_engine_memory_blob: crc_valid_ram_inputs=2223898 rle_decode_reached=1061747 oversized_ram_rejections=52388
```

Implementation notes:

- Adds a valid V5 engine-state corpus for RAM blob fuzzing.
- Custom mutator recomputes CRC32 after mutations so cases pass header validation.
- Mutator targets RAM directory metadata, memory section metadata, encoded RAM blob bytes, and oversized memory-size rejection cases.
- CI fuzz smoke and longer fuzz steps include `fuzz_engine_memory_blob`.

Deviations: none.

## Limitations and Audit Notes

- Exact session start timestamp was unavailable after context compaction; the machine JSON uses `null` for `started_at_utc`.
- The full dev build exits 0 but emits existing warning classes. I did not claim the repository is warning-free.
- The working tree is not clean because of untracked `.claude` directories and the untracked handoff files. The tracked Sprint 0 branch diff is clean and shown in the diffstat.
- Local ASan fuzz execution requires `C:\Program Files\LLVM\lib\clang\22\lib\windows` on PATH so `clang_rt.asan_dynamic-x86_64.dll` is found.
