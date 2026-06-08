# Codex Audit: RuntimeHost Proxy Parity

Date: 2026-06-08
Auditor: Codex
Gemini QA artifact: `docs/superpowers/reviews/2026-06-08-gemini-35-flash-openspec-runtimehost-proxy-parity-qa.md`

## Verdict

PASS after auditor corrections.

The proxy parity sprint builds locally, passes ABI validation, passes full unit and CTest execution, and leaves the application-layer RuntimeHost bypass count at exactly 2 lifecycle calls: `legends_create` and `legends_destroy`.

## Corrections Applied

1. Hardened proxy ABI validation in `src/legends_proxy/proxy_api.cpp`.
   - Added missing null-handle checks for newly proxied APIs.
   - Added required output pointer checks matching direct ABI behavior.
   - Restored the missing response error check in `legends_is_audio_active`.
   - Ensured `legends_get_config` starts from `LEGENDS_CONFIG_INIT`.
   - Ensured `legends_save_state` always reports required size and rejects undersized returned payloads before copying.

2. Hardened IPC dynamic payload parsing in `src/legends_ipc/messages.cpp`.
   - Rejected truncated, oversized, or malformed dynamic payloads for save/load state, text capture, MIDI capture, and string-backed requests.
   - Replaced overflow-prone size expressions with remaining-buffer checks.

3. Hardened dispatcher allocation behavior in `src/engine_host/engine_dispatcher.cpp`.
   - `CaptureTextReq` and `CaptureMidiAudioReq` now query required size first.
   - Malicious or stale caller buffer counts now return `LEGENDS_ERR_BUFFER_TOO_SMALL` instead of driving large allocations.

4. Corrected capability truth for `legends_joystick_event`.
   - Changed proxy status from `proxy-supported` to `proxy-partial`.
   - The IPC route exists, but the underlying direct API remains partial, so full public support would be an overclaim.

5. Added focused regression coverage in `tests/unit/test_ipc_messages.cpp`.
   - Truncated save-state payloads.
   - Mismatched load-state payload sizes.
   - Odd text-cell payloads.
   - Odd MIDI sample payloads.

## Verification

- `openspec.cmd validate runtimehost-proxy-core-parity --strict --json`
- `openspec.cmd validate runtimehost-proxy-device-command-parity --strict --json`
- `openspec.cmd validate runtimehost-proxy-parity-quality-gates --strict --json`
- `python scripts/check_capability_matrix.py --repo .`
- `python scripts/check_conflict_markers.py --path .`
- `python scripts/graphify_projectlegends.py update --repo . --source-only`
- `python scripts/graphify_projectlegends.py runtimehost-bypasses --repo .`
- `python scripts/check_graphify_enrichment.py --repo . --overlay graphify-out/projectlegends-enrichment.json --strict --strict-tests fail --allow-missing-graphify`
- `cmake --preset dev`
- `cmake --build --preset dev`
- `build/dev/legends_abi_test.exe`
- `build/dev/legends_unit_tests.exe --gtest_brief=1`
- `ctest --test-dir build/dev --output-on-failure`
- `git diff --check`

## Residual Notes

- The local tree is not committed at the time of this audit.
- Remote CI should be checked after this corrected tree is committed and pushed.
- The capability matrix validates all 50 public APIs for documentation and dispatcher consistency; this does not mean all APIs are fully implemented in both direct and proxy modes.
