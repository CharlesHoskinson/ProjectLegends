# Change: presets-single-source

## Why

`CMakePresets.json` defines nine configure presets and no workflow invokes any of them — all four workflows hand-roll `cmake -B build` flag lists, and the copies have already drifted: the `asan` preset combines address+undefined (CMakePresets.json:65) while CI runs them as split lanes (.github/workflows/ci.yml:343-350), and no preset at all matches the Windows MSVC job, the library-mode job, or the PAL-headless jobs (audit-wiki/wiki/entities/Build & CI System (Project Legends).md). This implements CI-THESIS.md recommendation R5: presets become the single source of build truth that CI and R3's preflight both consume, and the preset name becomes the natural matrix axis for R8's consolidation (audit-wiki/wiki/sources/CI Design for C++-CMake Monorepos (2026-06).md, practice 1).

## What Changes

- Add the missing presets first (Recommendation Review rows M-2, A-1, G-6): a `windows-msvc` Visual Studio-generator preset (the hidden `default` is MinGW, `dev` is Ninja; nothing matches ci.yml's windows job, .github/workflows/ci.yml:197-207), `ubsan`, `library-mode`, and `pal-headless` (plus `pal-sdl2`/`pal-sdl3` variants), plus CI-parity presets for cells with no counterpart today: `release-tests`, `linux-gcc`, `linux-clang`, `package`/`package-windows`.
- **BREAKING**: reconcile the `asan` preset with CI's split sanitizer lanes — `asan` drops `,undefined` and becomes address-only; the new standalone `ubsan` preset carries undefined. Local `cmake --preset asan` behavior changes.
- No `msan` preset is added — that matrix cell is retired under `ci-stabilize-mandatory-lanes` (R1; Recommendation Review row G-7).
- Condition-guard Linux-pinned presets (`asan`, `ubsan`, `tsan`, `coverage`, `fuzz`, the new toolchain bases) on `${hostSystemName}` so Windows preset listings stay usable; guard `windows-msvc` symmetrically.
- Migrate every workflow configure/build/ctest step in `ci.yml`, `pal-ci.yml`, `module-dag.yml`, and `sprint2-checks.yml` to `cmake --preset` / `cmake --build --preset` / `ctest --preset`. Job names — including the five required-check names `master-ruleset-required-checks` (R2) binds — do not change.

## Capabilities

### New Capabilities

- `build-presets`: CMake presets as the single source of build configuration — preset coverage of every CI build cell, sanitizer preset parity with the split lanes, OS condition guards, MSVC-generator preset, test-preset strictness, and the rule that workflows configure only through presets.

### Modified Capabilities

(none — `openspec/specs/ci-stabilization` defines which lanes are primary vs optional and when they trigger; this change relocates flag definitions into presets without altering which lanes run, when they run, or what they test)

## Impact

- `CMakePresets.json` — new and modified entries in all three sections (configurePresets, buildPresets, testPresets).
- `.github/workflows/ci.yml`, `pal-ci.yml`, `module-dag.yml`, `sprint2-checks.yml` — configure/build/test step bodies only; triggers, job names, and `if:` tiers untouched.
- Downstream: `preflight-gate-entrypoint` (R3) consumes these presets for its build/test legs; `consolidate-workflows-policy` (R8) matrixes over preset names; sequenced after `ci-stabilize-mandatory-lanes` (R1) so the preset set covers surviving cells only.
