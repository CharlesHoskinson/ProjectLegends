# build-presets

## ADDED Requirements

### Requirement: Workflows configure only through presets
Every CMake configure, build, and ctest step in `.github/workflows/ci.yml`, `pal-ci.yml`, `module-dag.yml`, and `sprint2-checks.yml` SHALL invoke `cmake --preset <name>`, `cmake --build --preset <name>`, or `ctest --preset <name>`. Workflow YAML SHALL NOT carry `-D` cache-variable flag lists, with one exception: a job whose configuration is a named base preset plus the single variant flag `PAL_BACKEND_SDL3=ON` MAY pass that one flag as an overlay on `cmake --preset`.

#### Scenario: No hand-rolled configure remains
- **WHEN** `.github/workflows/` is searched for `cmake -B`
- **THEN** no match exists outside `cmake --preset` invocations

#### Scenario: SDL3 variant overlay is the only permitted flag
- **WHEN** a workflow configure step passes any `-D` flag
- **THEN** that step is one of the SDL3 variant jobs (`linux-sdl3`, `windows-sdl3`, `macos-sdl3`) and the flag is exactly `-DPAL_BACKEND_SDL3=ON`

### Requirement: Every surviving CI build cell has a preset
`CMakePresets.json` SHALL define configure presets covering every build configuration a workflow job uses after the MSan cell's retirement: `linux-gcc`, `linux-clang`, `release-tests`, `windows-msvc`, `asan`, `ubsan`, `tsan`, `ipc`, `coverage`, `fuzz`, `library-mode`, `pal-headless`, `pal-sdl2`, `pal-sdl3`, `package`, and `package-windows`, alongside the existing local presets `dev`, `dev-mingw`, and `release`. Each configure preset whose job builds SHALL have a build preset; each whose job runs ctest SHALL have a test preset.

#### Scenario: MSVC job is preset-driven
- **WHEN** the `windows` job in ci.yml, the `build-windows` job in module-dag.yml, or the `windows-build` job in pal-ci.yml configures
- **THEN** it uses the `windows-msvc` preset, whose generator is `Visual Studio 17 2022` with `x64` architecture and whose build and test presets set the `Release` configuration

#### Scenario: Library-mode job is preset-driven
- **WHEN** the `multi-instance-tests` job in sprint2-checks.yml configures
- **THEN** it uses the `library-mode` preset carrying `LEGENDS_LIBRARY_MODE=ON`

#### Scenario: PAL jobs are preset-driven
- **WHEN** the `headless-tests`, `contract-gates`, or `abi-c-compile` job in pal-ci.yml configures
- **THEN** it uses the `pal-headless` preset, which sets `PAL_BACKEND_HEADLESS=ON`, `PAL_BACKEND_SDL2=OFF`, and `PAL_BACKEND_SDL3=OFF` explicitly

### Requirement: Sanitizer presets match the split CI lanes
The `asan` preset SHALL sanitize address only; a separate `ubsan` preset SHALL sanitize undefined only; the `tsan` preset SHALL sanitize thread only. The sanitizer presets SHALL be the configurations the ci.yml `sanitizers` matrix legs build. No `msan` preset SHALL exist while the MSan re-entry condition (an MSan-instrumented libc++) is unmet.

#### Scenario: address and undefined are separate presets
- **WHEN** the `asan` preset's flag strings are inspected
- **THEN** they contain `-fsanitize=address` and do not contain `undefined`
- **AND** the `ubsan` preset's flag strings contain `-fsanitize=undefined` and do not contain `address`

#### Scenario: No msan preset
- **WHEN** `CMakePresets.json` is searched for `msan`
- **THEN** no preset of that name exists

#### Scenario: ubsan bypasses the fuzz-only option
- **WHEN** the `ubsan` preset is inspected
- **THEN** it passes raw `-fsanitize=undefined` compile/link flags and does not set `ENABLE_UBSAN` (which sanitizes only fuzz targets)

### Requirement: OS condition guards on toolchain-pinned presets
Every preset that pins a Linux toolchain (`asan`, `ubsan`, `tsan`, `coverage`, `fuzz`, `library-mode`, `pal-headless`, `pal-sdl2`, `pal-sdl3`, `linux-gcc`, `linux-clang`, `package`, and the hidden toolchain bases) SHALL carry a `condition` on `${hostSystemName}` excluding Windows; `windows-msvc` and `package-windows` SHALL carry the symmetric Windows condition. Presets with no toolchain pin (`dev`, `dev-mingw`, `release`, `release-tests`, `ipc`) SHALL remain unconditioned.

#### Scenario: Windows listing stays usable
- **WHEN** `cmake --list-presets` runs on a Windows host
- **THEN** the listing contains `windows-msvc`, `package-windows`, and the unconditioned presets, and contains no Linux-pinned preset

#### Scenario: Linux listing excludes Windows presets
- **WHEN** `cmake --list-presets` runs on a Linux host
- **THEN** the listing contains the Linux-pinned and unconditioned presets and does not contain `windows-msvc` or `package-windows`

### Requirement: Test presets fail on empty selection
Every test preset SHALL set `output.outputOnFailure: true` and `execution.noTestsAction: error`.

#### Scenario: Vacuous test run fails
- **WHEN** `ctest --preset <name>` selects zero tests
- **THEN** the invocation exits nonzero

### Requirement: Migration preserves job identity and lane behavior
The preset migration SHALL NOT rename any workflow job or display name (including the required-check names `Linux (gcc)`, `Linux (clang)`, `Linux IPC (gcc)`, `Windows (MSVC)`, `C ABI Verification`), SHALL NOT alter any trigger, tier, path filter, or `if:` condition, and SHALL keep each migrated job's effective cache configuration equal to its pre-migration configuration except for the divergences recorded in the change's design document (D5).

#### Scenario: Required-check names survive
- **WHEN** the migrated workflows run
- **THEN** the five required-check names report with unchanged strings

#### Scenario: Flag parity per migrated job
- **WHEN** a migrated job's preset configure is compared to the pre-migration flag list
- **THEN** the effective cache variables are identical, or the difference is one recorded in design D5

#### Scenario: Binary-dir references updated
- **WHEN** a job migrates to a preset whose `binaryDir` is `build/${presetName}`
- **THEN** every path in that job referencing the old `build/` directory (artifact globs, cache paths, fuzzer and test-binary invocations, lcov directories, cpack working directory, existence checks) references the preset's binary directory
