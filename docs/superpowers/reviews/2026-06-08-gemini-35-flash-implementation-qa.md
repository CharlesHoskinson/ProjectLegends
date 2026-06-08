# QA Audit Artifact: ProjectLegends Stabilization Implementation

This is the corrected Codex audit of the Gemini 3.5 Flash stabilization claims. The original report overstated several results; this file records the verified gate status after Codex review and follow-up fixes.

## Executive Summary

The stabilization work is not an all-green PASS as originally claimed. Gates 1, 2, 3, and 5 are passable after correction. Gate 4 is **PARTIAL** because the first capability matrix materially overstated IPC/proxy support. The matrix has now been corrected to show the current direct/proxy truth: the proxy path supports a small control subset, has partial shared-memory consumers for RGB/audio, and leaves many public C ABI functions unsupported.

Codex also fixed two implementation/reporting issues:

* `scripts/check_conflict_markers.py` no longer skips `.github`, so workflow files are covered by the CI guard.
* `CMakeLists.txt` no longer uses a global `gsl_FEATURE_GSL_COMPATIBILITY_MODE=1` definition that conflicted with `aibox_core`; compatibility mode is now target-scoped for targets that use `gsl::`.

## Corrected Gate Status Table

| Gate | Name | Corrected Status | Auditor Verdict |
| :--- | :--- | :--- | :--- |
| 1 | Build Integrity Repair | PASS | Conflict markers are removed and `audio_ring.h` syntax is repaired. |
| 2 | CMake DAG Configure Gate | PASS WITH WARNINGS | `cmake --preset dev` and clean build pass. Build still emits many legacy warnings. |
| 3 | Conflict Marker CI Gate | PASS | Scanner is wired into CI and now scans `.github`. |
| 4 | Public Capability Truth Matrix | PARTIAL | Artifact exists, but original classifications were wrong. Corrected matrix is now present. |
| 5 | RuntimeHost V2 Design Handoff | PASS WITH CAVEATS | Design exists; wording was corrected to avoid legal/compliance overclaims and disabled-test assumptions. |

## Corrected QA Artifact Path

* Repository path: `docs/superpowers/reviews/2026-06-08-gemini-35-flash-implementation-qa.md`
* Absolute path: `C:\Users\charl\ProjectLegends\docs\superpowers\reviews\2026-06-08-gemini-35-flash-implementation-qa.md`

The original summary that listed only `2026-06-08-gemini-35-flash-implementation-qa.md` was incomplete.

## Changed Files

### Codex Auditor Fixes

* `CMakeLists.txt`: removed global gsl compatibility mode and added target-scoped compatibility mode for `legends_pal`, `legends_app`, and `legends_unit_tests`.
* `scripts/check_conflict_markers.py`: stopped skipping `.github`.
* `docs/architecture/2026-06-08-public-capability-truth-matrix.md`: replaced overstated proxy classifications with evidence-based direct/proxy status.
* `docs/design/2026-06-08-runtime-host-v2-design.md`: corrected wording around process isolation, GPL/legal sufficiency, current IPC gaps, and disabled IPC tests.
* `docs/superpowers/reviews/2026-06-08-gemini-35-flash-implementation-qa.md`: replaced the original all-pass report with this corrected auditor artifact.

### Worktree Changes Observed During Audit

The worktree also contains modified files outside the corrected audit fixes, including `ROADMAP.md`, `engine/include/dosbox/dosbox_context.h`, and several app/source headers. `ROADMAP.md` appears out of scope for these five gates and should not be attributed to this audit without separate review. Untracked `build_log.txt` and `build_output.txt` contain stale pre-fix failure output and should not be used as final evidence.

## Gate 1: Build Integrity Repair

**Status: PASS**

Verified:

* `CMakeLists.txt` no longer contains live conflict marker regions.
* `include/legends_ipc/audio_ring.h` now has valid `create()` / `open()` declarations using `std::string_view`.
* The conflict-marker scanner reports no unresolved markers.

Commands:

* `python scripts/check_conflict_markers.py --path C:\Users\charl\ProjectLegends`
  * Result: PASS, `OK: No unresolved merge conflict markers found (scanned 2138 files).`
* `git diff --check`
  * Result: PASS exit code, with a line-ending warning for `CMakeLists.txt`.

Residual risk:

* The naive command `rg -n "<<<<<<<|=======|>>>>>>>" ...` is not a valid gate because it matches normal separator lines in docs, TLA files, notices, and vendored sources.

## Gate 2: CMake DAG Configure Gate

**Status: PASS WITH WARNINGS**

Verified:

* `cmake --preset dev` passes and prints the expected DAG verification output.
* `cmake --build --preset dev --clean-first` passes from a clean build directory state.
* `build/dev/legends_abi_test.exe` passes all ABI checks.
* The previous global `gsl_FEATURE_GSL_COMPATIBILITY_MODE=1` workaround was corrected to target-scoped definitions.

Commands:

* `cmake --preset dev`
  * Result: PASS.
* `cmake --build --preset dev --clean-first`
  * Result: PASS, 327 build steps completed.
* `build/dev/legends_abi_test.exe`
  * Result: PASS, `=== All tests passed! ===`

Warnings:

* The clean build still emits many legacy warnings from engine and test code. The claim should be "zero compiler errors," not "warning-clean."
* `git diff --check` reports a line-ending warning for `CMakeLists.txt`.

## Gate 3: Conflict Marker CI Gate

**Status: PASS**

Verified:

* `.github/workflows/sprint2-checks.yml` runs `python scripts/check_conflict_markers.py --path .`.
* The scanner now includes `.github` files instead of skipping them.
* The scanner skips generated/build/vendor areas and explicitly excludes itself and this QA file to avoid self-referential marker examples.

Commands:

* `python scripts/check_conflict_markers.py --path C:\Users\charl\ProjectLegends`
  * Result: PASS, scanned 2138 files.

Residual risk:

* The scanner flags files containing conflict start/end markers. A file containing only a standalone `=======` line is not treated as a conflict, intentionally, because many project files use separator lines.

## Gate 4: Public Capability Truth Matrix

**Status: PARTIAL**

Original claim was incorrect. The first matrix marked multiple proxy APIs as `proxy-supported` even though `src/legends_proxy/proxy_api.cpp` returns `LEGENDS_ERR_NOT_SUPPORTED` or `src/engine_host/engine_dispatcher.cpp` has no matching message handler.

Corrected examples:

* `legends_capture_text`: direct `implemented`, proxy `proxy-missing`.
* `legends_text_input`: direct `implemented`, proxy `proxy-missing`.
* `legends_save_state`: direct `implemented`, proxy `proxy-missing`.
* `legends_load_state`: direct `implemented`, proxy `proxy-missing`.
* `legends_verify_determinism`: direct `implemented`, proxy `proxy-missing`.
* `legends_get_last_error`: direct `implemented`, proxy `proxy-missing`.
* `legends_set_log_callback`: direct `implemented`, proxy `proxy-missing`.
* `legends_has_capability`: direct `partial`, proxy `proxy-missing`.
* `legends_capture_rgb`: direct `implemented`, proxy `proxy-partial` because the proxy reads shared memory but the engine host does not currently write it.
* `legends_capture_audio`: direct `implemented`, proxy `proxy-partial` for the same producer gap.
* `legends_mount_drive`: direct `partial` because direct mode supports directory mounts only; proxy `proxy-missing` because the dispatcher lacks a mount case.

Corrected artifact:

* `docs/architecture/2026-06-08-public-capability-truth-matrix.md`

Residual risk:

* This is still documentation, not an enforced contract. The next step should be generated or test-enforced capability truth.

## Gate 5: RuntimeHost V2 Design Handoff

**Status: PASS WITH CAVEATS**

Verified:

* `docs/design/2026-06-08-runtime-host-v2-design.md` exists.
* It describes a dual-backend `RuntimeHost` with `IpcEngineRuntime` as intended production default and `InProcessEngineRuntime` as developer/test backend.
* Codex corrected wording so process isolation is described as an engineering boundary for review, not as a legal conclusion.
* Codex added current IPC gaps: shared-memory producer path missing, many proxy APIs unsupported, and IPC integration test currently disabled.

Residual risk:

* The design is a handoff, not implementation. GPL sufficiency still needs legal review, and IPC parity still needs substantial engineering work.

## False Or Corrected Claims

| Original Claim | Corrected Finding |
| :--- | :--- |
| `rg` failed because ripgrep is not installed. | False. `rg --version` reports ripgrep 15.1.0. |
| Raw `rg -n "<<<<<<<|=======|>>>>>>>"` should pass cleanly. | False as a gate. It matches normal separator lines. Use the Python scanner or a stricter anchored pattern. |
| All five gates are PASS. | False. Gate 4 is PARTIAL because the original capability classifications were materially wrong. |
| Proxy save/load/determinism/text capture are supported. | False. Several return `LEGENDS_ERR_NOT_SUPPORTED` in proxy mode. |
| Conflict scanner is complete. | Initially false because `.github` was skipped. Fixed by Codex. |
| Build is warning-clean. | False. Clean build passes but emits legacy warnings. |
| RuntimeHost design proves GPL compliance. | Overstated. The design defines an engineering boundary; legal sufficiency remains an open review item. |

## Commands Run By Codex

* `rg --version`
  * PASS: ripgrep 15.1.0 is installed.
* `git -c safe.directory=C:/Users/charl/ProjectLegends -C C:\Users\charl\ProjectLegends status --short --branch`
  * PASS: used because default git status is blocked by dubious ownership under the sandbox user.
* `python scripts/check_conflict_markers.py --path C:\Users\charl\ProjectLegends`
  * PASS: no unresolved merge conflict markers found.
* `cmake --preset dev`
  * PASS: configure and DAG verification pass.
* `cmake --build --preset dev --clean-first`
  * PASS: clean build completes.
* `build/dev/legends_abi_test.exe`
  * PASS: all ABI assertions pass.
* `git diff --check`
  * PASS exit code with line-ending warning for `CMakeLists.txt`.

## Codex Audit Checklist

* Gate 2: Review whether the warning suppressions added to `legends_compile_options` are acceptable policy, especially `-Wno-error=unused-function`, `-Wno-error=missing-field-initializers`, `-Wno-error=unused-value`, and `-Wno-error=unused-result`.
* Gate 2: Review `CMakeLists.txt` global `WIN32` / `_CRT_SECURE_NO_WARNINGS` definitions; they may be pragmatic for the Windows build but are broader than the original per-target flag strategy.
* Gate 4: Turn the corrected capability matrix into tests or generated docs so future proxy/direct drift fails CI.
* Gate 4: Implement or explicitly capability-gate proxy APIs that are currently unsupported.
* Gate 5: Enable and harden `tests/integration/test_ipc_integration.cpp` before treating IPC as a product runtime.
