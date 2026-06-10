# Tasks: presets-single-source

## 1. CMakePresets.json — hidden bases and modified presets

- [ ] 1.1 Add hidden `toolchain-gcc13` preset: `CMAKE_C_COMPILER=gcc-13`, `CMAKE_CXX_COMPILER=g++-13`, condition `${hostSystemName} == Linux`
- [ ] 1.2 Add hidden `toolchain-clang18` preset: `CMAKE_C_COMPILER=clang-18`, `CMAKE_CXX_COMPILER=clang++-18`, `-stdlib=libc++` in `CMAKE_CXX_FLAGS` and `CMAKE_EXE_LINKER_FLAGS`, condition `${hostSystemName} == Linux`
- [ ] 1.3 Add `CMAKE_EXPORT_COMPILE_COMMANDS=ON` to the hidden `default` and `default-ninja` bases (design D8)
- [ ] 1.4 Modify `asan`: remove `,undefined` from `CMAKE_CXX_FLAGS`, `CMAKE_C_FLAGS`, `CMAKE_EXE_LINKER_FLAGS`; remove `UBSAN_OPTIONS` from environment; inherit `toolchain-clang18` and drop the duplicated compiler/libc++ entries
- [ ] 1.5 Modify `tsan`: inherit `toolchain-clang18`, drop duplicated compiler/libc++ entries, leave `TSAN_OPTIONS` value untouched (R1 may have added `suppressions=`)
- [ ] 1.6 Modify `coverage` and `fuzz`: add Linux condition (directly or via inherit); flags unchanged
- [ ] 1.7 Verify `dev`, `dev-mingw`, `release`, `ipc` are byte-identical in effect after the base edits (only `CMAKE_EXPORT_COMPILE_COMMANDS` added)

## 2. CMakePresets.json — new configure presets

- [ ] 2.1 Add `release-tests`: inherits `default-ninja`, Release, `LEGENDS_BUILD_TESTS=ON`, no condition
- [ ] 2.2 Add `linux-gcc`: inherits `release-tests` + `toolchain-gcc13`
- [ ] 2.3 Add `linux-clang`: inherits `release-tests` + `toolchain-clang18`
- [ ] 2.4 Add `windows-msvc`: generator `Visual Studio 17 2022`, architecture `x64`, `LEGENDS_BUILD_TESTS=ON`, `LEGENDS_HEADLESS=ON`, condition `${hostSystemName} == Windows`
- [ ] 2.5 Add `ubsan`: inherits `default-ninja` + `toolchain-clang18`, Debug, `-fsanitize=undefined -fno-omit-frame-pointer` in CXX/C/linker flags (raw flags, not `ENABLE_UBSAN`), `LEGENDS_BUILD_TESTS=ON`, env `UBSAN_OPTIONS=halt_on_error=1:print_stacktrace=1`
- [ ] 2.6 Add `library-mode`: inherits `default-ninja` + `toolchain-gcc13`, Release, `LEGENDS_BUILD_TESTS=ON`, `LEGENDS_LIBRARY_MODE=ON`
- [ ] 2.7 Add `pal-headless`: inherits `default-ninja` + `toolchain-gcc13`, Debug, `LEGENDS_BUILD_TESTS=ON`, `PAL_BACKEND_HEADLESS=ON`, `PAL_BACKEND_SDL2=OFF`, `PAL_BACKEND_SDL3=OFF`
- [ ] 2.8 Add `pal-sdl2`: inherits `pal-headless`, `PAL_BACKEND_SDL2=ON`
- [ ] 2.9 Add `pal-sdl3`: inherits `pal-headless`, `PAL_BACKEND_SDL3=ON`, `PAL_DEFAULT_BACKEND=SDL3`
- [ ] 2.10 Add `package`: Ninja, Release, `PAL_BACKEND_SDL3=ON`, `LEGENDS_HEADLESS=OFF`, condition `${hostSystemName} != Windows`
- [ ] 2.11 Add `package-windows`: `Visual Studio 17 2022` + `x64`, `PAL_BACKEND_SDL3=ON`, `LEGENDS_HEADLESS=OFF`, condition `${hostSystemName} == Windows`
- [ ] 2.12 Confirm no preset named `msan` exists and none of the new presets reintroduces `-fsanitize=memory`

## 3. CMakePresets.json — build and test presets

- [ ] 3.1 Add build presets for: `release-tests`, `linux-gcc`, `linux-clang`, `windows-msvc` (configuration `Release`), `ubsan`, `library-mode`, `pal-headless`, `pal-sdl2`, `pal-sdl3`, `package`, `package-windows` (configuration `Release`)
- [ ] 3.2 Add test presets for: `release-tests`, `linux-gcc`, `linux-clang`, `windows-msvc` (configuration `Release`), `ubsan`, `pal-headless`, `pal-sdl2`, `pal-sdl3`
- [ ] 3.3 Set `execution.noTestsAction: error` on every test preset, existing (`dev`, `dev-mingw`, `asan`, `tsan`, `ipc`, `coverage`) and new; keep `output.outputOnFailure: true`
- [ ] 3.4 Validate JSON: `cmake --list-presets` on Windows shows `windows-msvc`, `package-windows`, `dev`, `dev-mingw`, `release`, `release-tests`, `ipc` and no Linux-pinned preset; on Linux shows the Linux set and no Windows preset

## 4. ci.yml migration (one commit; per-job flag-parity check against design D5/D7)

- [ ] 4.1 `linux` (gcc cell) → `cmake --preset linux-gcc` / `cmake --build --preset linux-gcc` / `ctest --preset linux-gcc`; drop matrix `cc`/`cxx`/`extra_cxx_flags` keys; map preset name from `matrix.compiler`; update visual-diff artifact glob to `build/linux-gcc/tests/**`
- [ ] 4.2 `linux` (clang cell) → `linux-clang` presets; artifact glob `build/linux-clang/tests/**`
- [ ] 4.3 `linux-ipc` → `cmake --preset ipc` / build / `ctest --preset ipc`; update `test -f build/...` checks to `build/ipc/...` (recorded divergence D5.1: gcc-13 pin dropped, runner default is gcc-13)
- [ ] 4.4 `linux-sdl3` → `cmake --preset linux-gcc|linux-clang -DPAL_BACKEND_SDL3=ON` + matching build preset; update SDL3 cache path to `build/<preset>/_deps/sdl3-*` and `test -f build/<preset>/project_legends`
- [ ] 4.5 `windows` → `windows-msvc` presets (build/test presets carry `-C Release`); artifact glob `build/windows-msvc/tests/**` (recorded divergence D5.7: explicit generator + x64)
- [ ] 4.6 `windows-sdl3` → `cmake --preset windows-msvc -DPAL_BACKEND_SDL3=ON`; update cache path and `build/windows-msvc/Release/project_legends.exe` check
- [ ] 4.7 `macos` → `release-tests` presets; artifact glob `build/release-tests/tests/**`
- [ ] 4.8 `macos-sdl3` → `cmake --preset release-tests -DPAL_BACKEND_SDL3=ON`; update cache path and executable check
- [ ] 4.9 `sanitizers` matrix → replace flag/c_flags/linker_flags/env matrix keys with a preset key: address→`asan`, undefined→`ubsan`, thread→`tsan` (keep its `allow_failure` state as R1 left it); memory cell is gone per R1 — if still present when this lands, do not create a preset for it; test step becomes `ctest --preset <name>` (env comes from the preset)
- [ ] 4.10 `static-analysis` → `cmake --preset linux-clang` (compile_commands now from the base); clang-tidy step points `-p build/linux-clang`
- [ ] 4.11 `fuzz` → `cmake --preset fuzz`; build via `cmake --build --preset fuzz --target fuzz-all generate_fuzz_corpus`; update all `./build/tests/fuzz/...` invocations and corpus paths to `build/fuzz/tests/fuzz/...`
- [ ] 4.12 `coverage` → `coverage` presets; lcov `--directory build/coverage`; artifact paths unchanged (repo root)
- [ ] 4.13 `packaging` → `cmake --preset package` (Unix) / `cmake --preset package-windows` (Windows) + build presets; `cd build/package`/`build/package-windows` for cpack; checksum script and artifact globs updated; SDL3 cache path updated
- [ ] 4.14 `release-validation` → `coverage` presets (recorded divergence D5.5); ctest keeps `--label-exclude soak`; lcov paths to `build/coverage`
- [ ] 4.15 Verify untouched: `abi-check`, `sdl-firewall`, `tlaplus`, `dependency-scan` bodies; all job names, `if:` conditions, triggers, timeouts

## 5. pal-ci.yml migration

- [ ] 5.1 Add `ninja-build` to apt installs (pal presets are Ninja, design D5.3)
- [ ] 5.2 `headless-tests` → `pal-headless` presets (recorded divergences D5.2/D5.3: Debug build type, Ninja)
- [ ] 5.3 `sdl2-tests` → `pal-sdl2` presets; keep `SDL_VIDEODRIVER`/`SDL_AUDIODRIVER` env on the test step
- [ ] 5.4 `sdl3-tests` → `pal-sdl3` presets; SDL3-from-source step untouched (R14 scope)
- [ ] 5.5 `contract-gates` → `pal-headless` configure/build; gtest-filter run, nm symbol checks updated to `build/pal-headless/` paths
- [ ] 5.6 `asan-lifecycle` → `asan` configure/build (recorded divergence D5.4: gcc→clang-18); apt install gains clang-18/libc++ packages; gtest `--gtest_filter=ContractGate_Lifecycle* --gtest_repeat=3` invocation unchanged except `build/asan/` path
- [ ] 5.7 `abi-c-compile` → `pal-headless` configure/build; `./build/pal-headless/legends_abi_test`; C11 compile step unchanged
- [ ] 5.8 `windows-build` → `windows-msvc` presets; `-C Release` via test preset
- [ ] 5.9 Verify untouched: `sdl-firewall`, all job names, path filters, triggers

## 6. module-dag.yml migration

- [ ] 6.1 `cmake-dag` → `cmake --preset release` (configure-only; Release, tests OFF, headless — matches current flags); DAG-output verification step reads the same configure log
- [ ] 6.2 `build-linux` → `linux-gcc` presets
- [ ] 6.3 `build-windows` → `windows-msvc` presets
- [ ] 6.4 Verify untouched: `include-rules`, `summary`, job names, path filters, `needs` graph

## 7. sprint2-checks.yml migration

- [ ] 7.1 `multi-instance-tests` → `cmake --preset library-mode`; build via `cmake --build --preset library-mode --target legends_unit_tests`; both gtest invocations point at `build/library-mode/legends_unit_tests` (recorded divergence D5.6: C compiler pinned too)
- [ ] 7.2 Verify untouched: `globals-registry` job, path filters, job names

## 8. Verification

- [ ] 8.1 `grep -rn 'cmake -B' .github/workflows/` returns nothing
- [ ] 8.2 `grep -rn '\-D' .github/workflows/` on configure steps returns only the three SDL3 `-DPAL_BACKEND_SDL3=ON` overlays
- [ ] 8.3 Per migrated job: diff effective cache variables (old flags vs `cmake --preset <name> -N -LA` equivalent) and confirm equality or a design-D5 entry
- [ ] 8.4 Push to a branch and confirm every migrated job goes green on `workflow_dispatch`, and the five required-check names report unchanged: `Linux (gcc)`, `Linux (clang)`, `Linux IPC (gcc)`, `Windows (MSVC)`, `C ABI Verification`
- [ ] 8.5 Local spot-check on Windows: `cmake --preset windows-msvc && cmake --build --preset windows-msvc && ctest --preset windows-msvc`; on Linux (or CI): same for `linux-gcc`, `ubsan`, `pal-headless`, `library-mode`
- [ ] 8.6 Confirm `ctest --preset` with a filter selecting zero tests exits nonzero (`noTestsAction: error` live)
