# QA Capability Gate Audit: ProjectLegends Capability Truth Enforcement

This QA artifact documents the implementation of the capability truth enforcement sprint for ProjectLegends. It is structured for systematic audit by Codex (external auditor).

---

## Executive Summary

During this sprint, the capability status (Gate 4) was transitioned from **PARTIAL** to a machine-enforceable **PASS**. A complete machine-readable capability manifest covering all 50 exported public C APIs was created, and the validator now checks the header exports, JSON manifest, Markdown matrix, direct unsupported classifications, proxy stubs, and proxy dispatcher coverage. The validation step is wired directly into the Sprint 2 CI checks workflow, protecting the project from future capability documentation drift.

---

## Changed Files

The following files were created or modified during this sprint:

### Newly Created Files
1. **[capability_truth.json](file:///C:/Users/charl/ProjectLegends/docs/architecture/capability_truth.json)**: The machine-readable capability manifest.
2. **[check_capability_matrix.py](file:///C:/Users/charl/ProjectLegends/scripts/check_capability_matrix.py)**: The automated validator script.
3. **[2026-06-08-gemini-35-flash-capability-gate-qa.md](file:///C:/Users/charl/ProjectLegends/docs/superpowers/reviews/2026-06-08-gemini-35-flash-capability-gate-qa.md)**: This QA artifact.

### Modified Files
1. **[sprint2-checks.yml](file:///C:/Users/charl/ProjectLegends/.github/workflows/sprint2-checks.yml)**: Integrated the validation check into the GitHub Actions CI workflow.

---

## Gate Status Table

| Gate | Name | Status | Auditor Verdict |
| :--- | :--- | :--- | :--- |
| **1** | Capability Source Of Truth | PASS | [capability_truth.json](file:///C:/Users/charl/ProjectLegends/docs/architecture/capability_truth.json) contains all 50 C APIs matching the corrected Codex matrix. |
| **2** | Capability Matrix Validator | PASS | [check_capability_matrix.py](file:///C:/Users/charl/ProjectLegends/scripts/check_capability_matrix.py) validates header declarations, JSON/Markdown parity, direct unsupported classifications, proxy stubs, and proxy dispatcher cases. |
| **3** | CI Wiring | PASS | Validator step is wired into [.github/workflows/sprint2-checks.yml](file:///C:/Users/charl/ProjectLegends/.github/workflows/sprint2-checks.yml) as a mandatory block. |
| **4** | Human-Readable Matrix Sync | PASS | [2026-06-08-public-capability-truth-matrix.md](file:///C:/Users/charl/ProjectLegends/docs/architecture/2026-06-08-public-capability-truth-matrix.md) and [capability_truth.json](file:///C:/Users/charl/ProjectLegends/docs/architecture/capability_truth.json) are in 100% agreement. |
| **5** | Verification And QA Handoff | PASS | Verified locally with the listed gate commands. Full `ctest` coverage was not run as part of this handoff. |

---

## Capability Manifest Summary

The machine-readable manifest [capability_truth.json](file:///C:/Users/charl/ProjectLegends/docs/architecture/capability_truth.json) documents:
* **Total public C APIs**: 50
* **Direct Mode Statuses**:
  * `implemented`: 43 APIs
  * `partial`: 3 APIs (`legends_mount_drive`, `legends_joystick_event`, `legends_has_capability`)
  * `unsupported`: 2 APIs (`legends_start_video_capture`, `legends_set_ttf_font`)
  * `stub-success`: 2 APIs (`legends_stop_video_capture`, `legends_is_video_capturing`)
* **IPC/Proxy Mode Statuses**:
  * `proxy-supported`: 17 APIs (lifecycle, emulation control, key/mouse event, cursor, audio-active, state hash, mount/unmount)
  * `proxy-partial`: 3 APIs (`legends_capture_rgb`, `legends_capture_audio` due to missing host-side writes; `legends_key_event_ext` due to E0 aliases)
  * `proxy-missing`: 30 APIs (explicitly return `LEGENDS_ERR_NOT_SUPPORTED` directly from proxy code or lack dispatcher cases)

---

## Validator Behavior

The validation script [check_capability_matrix.py](file:///C:/Users/charl/ProjectLegends/scripts/check_capability_matrix.py):
1. Parses [legends_embed.h](file:///C:/Users/charl/ProjectLegends/include/legends/legends_embed.h) to extract all `LEGENDS_API` exports.
2. Checks for duplicates in the header.
3. Loads [capability_truth.json](file:///C:/Users/charl/ProjectLegends/docs/architecture/capability_truth.json) and detects:
   * **Missing keys**: declared in header but absent in manifest.
   * **Extra keys**: documented in manifest but absent in header.
4. Parses [2026-06-08-public-capability-truth-matrix.md](file:///C:/Users/charl/ProjectLegends/docs/architecture/2026-06-08-public-capability-truth-matrix.md) and asserts status parity with the JSON manifest.
5. Asserts that direct/proxy status values fall within allowed enums and that manifest entries have evidence files and notes.
6. Parses direct implementations and confirms APIs classified as `unsupported` return `LEGENDS_ERR_NOT_SUPPORTED` directly.
7. Parses the body of every function in [proxy_api.cpp](file:///C:/Users/charl/ProjectLegends/src/legends_proxy/proxy_api.cpp), extracts IPC request types, and confirms APIs classified as `proxy-supported` have matching `engine_dispatcher.cpp` cases.

---

## CI Wiring Evidence

The capability verification step is wired into [.github/workflows/sprint2-checks.yml](file:///C:/Users/charl/ProjectLegends/.github/workflows/sprint2-checks.yml) under the `globals-registry` quality gate job:

```yaml
      - name: Check unresolved merge conflict markers
        run: python scripts/check_conflict_markers.py --path .

      - name: Check capability matrix drift
        run: python scripts/check_capability_matrix.py --repo .
```

It is a mandatory step that blocks the build on failure.

---

## Commands Run

The following commands were run locally to verify correctness:
1. `python scripts/check_capability_matrix.py --repo .`
   * **Result**: PASS (printed `PASS: Capability matrix validated successfully. 50 public C APIs mapped; 50 Markdown rows synced; proxy dispatcher constraints checked.`)
2. `python scripts/check_conflict_markers.py --path .`
   * **Result**: PASS (printed `OK: No unresolved merge conflict markers found (scanned 2144 files).`)
3. `git diff --check`
   * **Result**: PASS (returned exit code 0)
4. `cmake --preset dev`
   * **Result**: PASS (configure and module DAG checks pass)
5. `cmake --build --preset dev --clean-first`
   * **Result**: PASS (clean compile completes)
6. `build/dev/legends_abi_test.exe`
   * **Result**: PASS (all 100% C ABI verification checks pass)

---

## Environment Notes

* Gemini's execution shell reported `rg --version` as unavailable. In the Codex auditor environment, `rg --version` succeeds (`ripgrep 15.1.0`), so the failure claim is environment-specific and not a repository blocker.
* The validator relies entirely on Python standard library tools, so CI does not require ripgrep.

---

## Residual Risks

1. **Runtime Semantics**: The validator is static. It confirms that `proxy-supported` APIs have proxy request wiring and dispatcher cases, but it does not execute the engine host or prove runtime parity.
2. **Shared Memory Producers**: `legends_capture_rgb` and `legends_capture_audio` remain `proxy-partial`; the validator records that status but does not prove future framebuffer/audio ring producer behavior.
3. **Line Ending Warnings**: `git diff --check` reports line ending conversions for `CMakeLists.txt` on Windows platforms, but this has no impact on configuration or compilation.

---

## Codex Audit Checklist

Auditors from Codex should verify:
- [ ] **Gate 1**: Confirm that the API status classifications in [capability_truth.json](file:///C:/Users/charl/ProjectLegends/docs/architecture/capability_truth.json) perfectly match the verified states.
- [ ] **Gate 2**: Audit the brace-matching body-parsing logic in [check_capability_matrix.py](file:///C:/Users/charl/ProjectLegends/scripts/check_capability_matrix.py) to confirm robust detection of return statements.
- [ ] **Gate 3**: Verify that the CI configuration step in [.github/workflows/sprint2-checks.yml](file:///C:/Users/charl/ProjectLegends/.github/workflows/sprint2-checks.yml#L55-L56) is correctly structured.
- [ ] **Gate 4**: Cross-reference [2026-06-08-public-capability-truth-matrix.md](file:///C:/Users/charl/ProjectLegends/docs/architecture/2026-06-08-public-capability-truth-matrix.md) and [capability_truth.json](file:///C:/Users/charl/ProjectLegends/docs/architecture/capability_truth.json) to confirm perfect status parity.
- [ ] **Gate 5**: Execute `python scripts/check_capability_matrix.py --repo .` locally and verify output logs.
