# Tasks

## 1. RuntimeHost Ownership

- [x] 1.1 Add explicit constructor ownership control to RuntimeHost concrete classes.
- [x] 1.2 Ensure borrowed RuntimeHost destruction does not destroy the application-owned engine handle.
- [x] 1.3 Reset `runtime_` before raw engine destruction in `Application::shutdown`.

## 2. RuntimeHost Hot-Path Surface

- [x] 2.1 Add `get_total_cycles`.
- [x] 2.2 Add `is_frame_dirty`.
- [x] 2.3 Add `inject_key_ext`.
- [x] 2.4 Add `capture_audio`.
- [x] 2.5 Add `capture_midi_audio`.
- [x] 2.6 Implement each method in both `InProcessEngineRuntime` and `IpcEngineRuntime`.

## 3. Application Migration

- [x] 3.1 Add `std::unique_ptr<RuntimeHost> runtime_` to `Application`.
- [x] 3.2 Create a borrowed runtime wrapper after successful `legends_create`.
- [x] 3.3 Route `Application::run` stepping and cycle reporting through `runtime_`.
- [x] 3.4 Route keyboard and mouse hot-path input through `runtime_`.
- [x] 3.5 Route frame dirty, RGB capture, and text capture through `runtime_`.
- [x] 3.6 Route PCM and MIDI audio capture through `runtime_`.

## 4. Graphify And Allowlist

- [x] 4.1 Remove retired hot-path bypass keys from `docs/architecture/runtimehost-bypass-allowlist.json`.
- [x] 4.2 Regenerate `graphify-out/projectlegends-enrichment.json`.
- [x] 4.3 Regenerate `docs/architecture/graphify-enrichment-report.md`.
- [x] 4.4 Verify RuntimeHost bypass count decreases from 53 to 38.

## 5. Verification

- [x] 5.1 Run `openspec validate runtimehost-adoption-next-slice --strict --json`.
- [x] 5.2 Run `cmake --preset dev`.
- [x] 5.3 Run `cmake --build --preset dev`.
- [x] 5.4 Run `build/dev/legends_unit_tests.exe`.
- [x] 5.5 Run `build/dev/legends_abi_test.exe`.
- [x] 5.6 Run `python scripts/check_capability_matrix.py --repo .`.
- [x] 5.7 Run `python scripts/check_conflict_markers.py --path .`.
- [x] 5.8 Run `python scripts/check_graphify_enrichment.py --repo . --overlay graphify-out/projectlegends-enrichment.json --strict --strict-tests fail --allow-missing-graphify`.
- [x] 5.9 Run `git diff --check`.
