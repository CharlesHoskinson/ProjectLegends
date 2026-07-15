# Independent adversarial audit — R1 P1–P4 residual closeout

## 1. Header

| Field | Value |
|---|---|
| Audit date | 2026-07-15 |
| Repository | `CharlesHoskinson/ProjectLegends` |
| `AUDITED_SHA` | `73fa4ad48d6413daa1417fe89e473c17349a0eb6` |
| Audited subject | `docs(audit): Codex brief for P1-P4 residual closeout` |
| Implementation parent | `d989ebda1b45e6256ecce23167b12072f7537b31` (`fix(security): remove vendored FluidSynth (#43); expand SBOM; drop /wd4875`) |
| Exact-SHA CI | [run 29443572124](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29443572124) — **completed / failure** |
| Claimed-tip CI, context only | [run 29443440591](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29443440591) — **completed / failure** |
| Auditor model | OpenAI Codex (GPT-5 runtime) |
| Evidence cutoff | 2026-07-15 19:30 UTC |

`73fa4ad` is the fetched `origin/master` tip pinned at audit start. It changes only this audit brief relative to implementation commit `d989ebd`, but all gate conclusions below come from the exact `73fa4ad` run rather than being inferred from its parent.

## 2. Executive summary

**FAIL — NO-GO.** The exact-SHA CI run is complete, and the mandatory Windows lane is red. Static removal of `/wd4875` did not establish the claimed P3 outcome: gsl-lite v1.1.0 still emits C4875 under MSVC 19.51, `/WX` promotes it to C2220, the build fails, and Windows tests do not run.

P1 passes at the audited snapshot: the FluidSynth 1.1.6 tree and headers are absent, the baseline has no active ignores, the optional component is honestly identified as v2.5.2, and the exact Dependency Scan is green. P2 also passes the point-in-time inventory contract: all six pins and all nine present top-level library directories are represented. Its regression guard is not fail-closed, however. P4 passes: MSan is absent, its checklist is concrete, and #40 remains open.

New finding counts: **1 high, 2 medium, 1 low** (F019–F022). Regardless of the non-Windows successes, one red mandatory lane requires **NO-GO**.

## 3. Dimension scorecard

| Dimension | Score (1–5) | Basis |
|---|---:|---|
| Security | **5** | No tracked FluidSynth 1.1.6 source/header tree; no active CVE ignores; optional pin is v2.5.2; production OSV scan exits 0. |
| Correctness | **2** | ASan, UBSan, TSan, and Fuzz pass, but mandatory Windows fails to build and runs no tests. |
| Maintainability | **2** | gsl-lite v1.1.0 does not satisfy the no-suppression premise; SBOM coverage is hard-coded; deleted FluidSynth still has Automake references. |
| Documentation honesty | **1** | #44 asserted Windows proof before a failing run completed; CI-THESIS, OpenSpec tasks, the residual tracker, NOTICE, and the threat model disagree with live state. |
| CI/CD integrity | **3** | CI correctly exposes the Windows regression and the exact dependency job is strong, but the SBOM comparator ignores coverage properties and the seed step accepts scanner exit 0. |
| Process/governance | **2** | #40 is correctly open, but #42/#43/#44 were closed before claimed-tip CI completed; #44 remains closed after two Windows failures. |

**Total: 15/30.**

## 4. Method

- Fetched `origin/master`, resolved `73fa4ad48d6413daa1417fe89e473c17349a0eb6`, and inspected the last 12 commits.
- Used live `gh` run/job APIs and job logs as primary CI evidence. Closed-issue narrative was treated as an assertion to test, not proof.
- Read tracked content from the pinned tree and confirmed the local checkout had no tracked modifications before testing.
- Ran `python scripts/generate_vendored_sbom.py --check`, parsed all SBOM components/properties, compared the actual `engine/src/libs/*` directory set with `legends:source-path`, compared CMake pins with the generator map, and searched the complete tracked tree for FluidSynth, `/wd4875`, MSan, and `allow_failure` paths.
- Queried live issue state and timestamps for #40, #42, #43, and #44.
- Did not run optional E14 because configuring would write build output and the audit authorization permits only this report to be written. No product code, workflow, test, or issue was modified.

## 5. Mandatory gate matrix

All rows are from [exact-SHA run 29443572124](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29443572124), which completed with conclusion `failure`.

| Mandatory job | Conclusion | Exact evidence | Gate |
|---|---|---|---|
| `address Sanitizer` | success | [job 87448327534](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29443572124/job/87448327534) | PASS |
| `undefined Sanitizer` | success | [job 87448327411](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29443572124/job/87448327411) | PASS |
| `thread Sanitizer` | success | [job 87448327473](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29443572124/job/87448327473): C++23 validation passed; 4,512/4,512 tests passed; 0 `WARNING: ThreadSanitizer`; 0 `SUMMARY: ThreadSanitizer`; 0 active suppressions | PASS |
| `Fuzz Testing` | success | [job 87450299911](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29443572124/job/87450299911): build, five-target smoke, and five 60-second main steps succeeded | PASS |
| `Windows (MSVC)` | **failure** | [job 87448327421](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29443572124/job/87448327421): 200 C4875 log hits, 4 C2220 errors; build failed; test step skipped | **FAIL** |
| `Dependency Scan` | success | [job 87448327450](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29443572124/job/87448327450): tree/ignore assertion passed; production exit 0; seed exit 1 with 5 vulnerabilities | PASS |

**Mandatory runtime lanes: FAIL.** The hard rule applies because Windows is red.

## 6. P1–P4 matrix

| Priority | Required claim | Evidence | Result |
|---|---|---|---|
| P1 / #43 | Remove vendored FluidSynth 1.1.6, drop ignores, retain only optional modern external path | Neither `engine/src/libs/fluidsynth` nor `engine/include/fluidsynth.h` nor `engine/include/fluidsynth/` exists. No tracked path name contains FluidSynth. `osv-scanner.toml` has 0 active `[[IgnoredVulns]]` headers. SBOM has `fluidsynth@2.5.2`, explicitly labeled optional, and no 1.1.x component. Exact Dependency Scan succeeds. `midi.cpp` includes `midi_synth.h` only under `C_FLUIDSYNTH`; the header uses external `<fluidsynth.h>`. | **PASS**, with stale Automake references in F022 and premature issue closure in F021 |
| P2 / #42 | Inventory every FetchContent pin and every present top-level `engine/src/libs/*` tree | Local `--check` exits 0 with 15 components. All six `LEGENDS_DEP_*_TAG` values are mapped: gsl-lite 1.1.0, SDL 3.2.8, googletest 1.14.0, benchmark 1.8.3, mt32emu 2.7.0, FluidSynth 2.5.2. All nine present directories map one-for-one to SBOM source paths; zmbv is `linked-default=true`, the other eight are `false`. | **PASS at this snapshot**, but the CI regression guard is not fail-closed (F020) |
| P3 / #44 | Remove `/wd4875` and remain Windows-green under `/WX` with gsl-lite v1.1.0 | No active `/wd4875` or `legends_gsl_msvc_options` remains, and Tier A still receives `/WX`. Exact Windows nevertheless fails on gsl-lite C4875 promoted to C2220; tests are skipped. The claimed implementation run fails the same way. | **FAIL** (F019) |
| P4 / #40 | Keep MSan absent and gate re-entry by checklist | The only CI workflow sanitizer matrix is exactly `[address, undefined, thread]`; there is no active memory sanitizer or `allow_failure` in any workflow. `docs/ci/msan-reentry.md` has five concrete criteria. #40 is OPEN. | **PASS** |

### P2 directory reconciliation

| Present directory | SBOM identity | `linked-default` |
|---|---|---|
| `decoders` | `decoders@vendored-bundle` | false |
| `gui_tk` | `gui_tk@vendored` | false |
| `libchdr` | `libchdr@vendored` | false |
| `mt32` | `mt32-vendored@vendored` | false |
| `passthroughio` | `passthroughio@vendored` | false |
| `physfs` | `physfs@vendored` | false |
| `tinyfiledialogs` | `tinyfiledialogs@vendored` | false |
| `xBRZ` | `xbrz@vendored` | false |
| `zmbv` | `zmbv@dosbox-x-vendored` | true |

Unaccounted present directories: **0**. Phantom source paths: **0**.

## 7. Issue state matrix

| Issue | Live state at cutoff | Required state/evidence | Audit result |
|---|---|---|---|
| [#40](https://github.com/CharlesHoskinson/ProjectLegends/issues/40) | OPEN | Remain open while MSan is parked | PASS |
| [#42](https://github.com/CharlesHoskinson/ProjectLegends/issues/42) | CLOSED at 19:09:31 UTC | Close only after accepted complete inventory | Current snapshot is complete, but closure preceded the claimed-tip Dependency Scan completion at 19:09:40 and overstates the fail-closed guard (F020/F021) |
| [#43](https://github.com/CharlesHoskinson/ProjectLegends/issues/43) | CLOSED at 19:09:29 UTC | Tree gone + empty ignores + same-SHA Dependency Scan green | Technical state is now proven, but closure occurred at run creation, before the job started at 19:09:32 or succeeded at 19:09:40 (F021) |
| [#44](https://github.com/CharlesHoskinson/ProjectLegends/issues/44) | CLOSED at 19:09:33 UTC | Windows success URL on the no-`/wd4875` SHA | **FAIL**: claimed-tip Windows failed at 19:16:13; exact-tip Windows failed at 19:19:50. The issue remains closed (F019/F021). |

## 8. Findings

New IDs continue after the prior audit's F018.

### F019 — HIGH — P3 is false: gsl-lite v1.1.0 still fails Windows under `/WX`

| Field | Detail |
|---|---|
| Affected | `CMakeLists.txt:103-124`, `cmake/dependencies.cmake:19-22`, Windows mandatory lane, issue #44 |
| Evidence | The exact job fetches gsl-lite v1.1.0. Its log contains 200 C4875 hits and four C2220 errors, including `legends_core.vcxproj` and `legends_ipc.vcxproj`. The Build step fails and Test is skipped. Claimed-tip run 29443440591 independently fails the same Windows lane. |
| Impact | P3 fails and the synchronized mandatory runtime gate is red. There is no Windows test evidence for the audited SHA. |
| Required correction | Reopen #44; advance to a gsl-lite revision that actually compiles cleanly under MSVC 19.51 `/WX` (or fix upstream/project interaction without warning suppression), then cite an exact-SHA Windows job where both Build and Test succeed. |

### F020 — MEDIUM — SBOM coverage is correct now but its CI check is not fail-closed

| Field | Detail |
|---|---|
| Affected | `scripts/generate_vendored_sbom.py:106-177,254-287`; `.github/workflows/ci.yml:883-897,902-925`; issue #42 |
| Evidence | The generator hard-codes the known directory tuple and never enumerates `engine/src/libs/*`; therefore a new unmapped top-level directory is silently omitted. `--check` compares only `(name, version, purl)`, so deleting every `legends:source-path` and `legends:linked-default` property in memory leaves its keyset equal. CI checks only component count plus zmbv/mt32emu names. The seed step also explicitly accepts scanner exit 0 when JSON contains vulnerabilities, despite calling the proof fail-closed. |
| Positive evidence | Current reconciliation is 9/9 directories, 0 missing, 0 phantom; all six pins are mapped. Exact production scan exits 0, and the current seed does exit 1 with five vulnerabilities. |
| Impact | A future vendored tree or stale/mislabelled coverage property can land while Dependency Scan remains green. The generator cannot enforce the continuing completeness claimed by #42. |
| Required correction | Enumerate actual top-level directories and fail on both `actual - inventoried` and `inventoried - actual`; compare canonical components including source-path and linkage properties; require seed scanner exit to be non-zero as well as parsing at least one vulnerability. |

### F021 — MEDIUM — Issues were closed before proof, and closeout documents contradict live evidence

| Field | Detail |
|---|---|
| Affected | Issues #42/#43/#44; `CI-THESIS.md:30`; `openspec/changes/ci-stabilize-mandatory-lanes/tasks.md:42-48`; `docs/ci/r1-residual-closeout.md:7-23`; `NOTICE:31`; `docs/security/THREAT_MODEL.md:169`; `cmake/dependencies.cmake:19-21` |
| Evidence | Claimed-tip CI was created at 19:09:29 UTC. #43 closed at 19:09:29, #42 at 19:09:31, and #44 at 19:09:33. Dependency Scan did not finish until 19:09:40, and Windows failed at 19:16:13. #44's closure comment nevertheless says “Windows CI on this commit is the proof.” CI-THESIS/OpenSpec still describe the deleted 1.1.6 inventory, active ignores, #42 partial status, and `/wd4875` as an open residual. The residual tracker says to close #43/#44 only after green CI even though they were already closed. NOTICE and the threat model still say FluidSynth v2.3.5. |
| Impact | Reviewers cannot determine current state from the repository or issue tracker, and a failed mandatory gate is represented as proven green. |
| Required correction | Reopen #44 immediately; attach exact job URLs before closing any gate issue; update the tracker, CI-THESIS, OpenSpec evidence, NOTICE, threat model, and stale gsl comment only after the replacement exact-SHA run completes. |

### F022 — LOW — Automake still references the deleted FluidSynth tree

| Field | Detail |
|---|---|
| Affected | `engine/src/libs/Makefile.am:3`; `engine/src/Makefile.am:74` |
| Evidence | `SUBDIRS` still includes `fluidsynth`, and non-Emscripten `dosbox_x_LDADD` still adds `libs/fluidsynth/libfluidsynth.a`, although both the directory and archive were deleted. |
| Impact | The security objective is satisfied because no source is present, but the alternate build graph can fail and still advertises the removed vendored integration. |
| Required correction | Remove the deleted subdirectory/archive references or replace them with an external-package condition consistent with the supported optional path. |

## 9. E-suite results

| ID | Result | Primary evidence |
|---|---|---|
| E1 | PASS | Fetched and pinned `origin/master` at `73fa4ad48d6413daa1417fe89e473c17349a0eb6`; 12-commit log below. |
| E2 | **FAIL** | Latest exact-SHA CI [run 29443572124](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29443572124) is completed with conclusion `failure`. |
| E3 | **FAIL** | ASan/UBSan/TSan/Fuzz/Dependency success; Windows failure. Exact job URLs are in section 5. |
| E4 | PASS | Exact TSan: C++23 PASS, 4,512/4,512 tests, 0 warning lines, 0 summary lines; `tsan-suppressions.txt` has 0 active entries. |
| E5 | **FAIL** | Exact Windows: C4875 → C2220 under `/WX`; build fails; tests skipped. |
| E6 | PASS | Exact Dependency Scan confirms tree absent/no ignores; generator 15 components; production exit 0; seed exit 1 and vulnerability count 5. |
| E7 | PASS | Source tree, public header, header directory, and `version.h` all absent. |
| E8 | PASS | No active `[[IgnoredVulns]]`, CVE-2021-21417, or CVE-2025-56225 entry; references are comments only. |
| E9 | PASS static / FAIL outcome | 0 active `/wd4875` or `legends_gsl_msvc_options` matches; Windows result disproves the intended outcome. |
| E10 | PASS snapshot / WARN | Local generator check exits 0; 15 components; all pins mapped; no 1.1.x FluidSynth; F020 covers the comparator weakness. |
| E11 | PASS | Nine actual top-level library directories equal nine SBOM source paths; zmbv is present and default-linked. |
| E12 | **FAIL process/state** | #40 open; #42/#43/#44 closed prematurely; #44 remains closed despite two Windows failures. |
| E13 | **FAIL** | OpenSpec tasks, CI-THESIS, residual tracker, NOTICE, threat model, and dependency comments contain mutually stale claims. |
| E14 | NOT RUN | Optional; would create build output outside the sole authorized report write. Exact CI supplied runtime evidence instead. |
| E15 | PASS security / WARN build hygiene | v2.5.2 tag exists (`2d07b6ba240d5c40c51d42b8a9ccb0373ca9e1e9`); no 1.1.6 source can be revived from the pinned tree. F022 records stale Automake edges. |

### E1 commit log

```text
73fa4ad docs(audit): Codex brief for P1-P4 residual closeout
d989ebd fix(security): remove vendored FluidSynth (#43); expand SBOM; drop /wd4875
54d85be fix(ci): F017 FluidSynth deb purl + mt32 pin; exercise #43 baseline
bccc423 docs: plan Go clean-room foundation
621a099 fix(r1): mutex breadcrumb (F013); Windows gsl scope (F014); honest FluidSynth SBOM (F015)
6255f02 docs: qualify local game-playing model
42c30c4 docs(audit): Codex GPT-5.6 R1 master closeout audit brief
733bb96 fix(r1): clear TSan residuals #38/#39; SBOM generator; seed vuln proof
f0feebf docs(r1): residual closeout — tasks, SBOM, scoped C4875, master dep-scan
f39b3da Merge pull request #46 from CharlesHoskinson/ci/r1-stabilize-mandatory-lanes
c9bf553 docs: specify Go clean-room emulator program
98450e6 ci(fuzz): drop unverified llvm.sh fallback (FINDING-008 hygiene)
```

### Adversarial probes

| Probe | Result |
|---|---|
| Ignore theater | Current tree cannot hide 1.1.6 under `engine/`: no tracked source/header path remains, and exact Dependency Scan's tree/ignore assertion passes. |
| Header leftovers | Only external `<fluidsynth.h>` remains, behind `C_FLUIDSYNTH`; default Windows does not include an in-tree fallback. |
| SBOM theater | Optional FluidSynth is explicitly described as optional v2.5.2 and current tree linkage labels are honest. F020 shows the properties are not protected against future drift. |
| P3 regression | **Confirmed:** `/WX` is active, gsl-lite v1.1.0 emits C4875, C2220 fails the build, and tests are skipped. |
| MSan sneak | None. The sole active sanitizer matrix has address/undefined/thread only; no workflow has an active memory sanitizer or `allow_failure`. |
| Issue honesty | **Failed:** #42/#43/#44 closed before CI completion; #44 claimed proof before the same run failed. |

## 10. Verdict

```text
P1 FluidSynth remove+drop ignores: PASS
P2 SBOM libs inventory: PASS
P3 no /wd4875 + Windows green: FAIL
P4 MSan parked: PASS
Mandatory runtime lanes: FAIL
OVERALL: NO-GO
```

The static no-`/wd4875` half of P3 is true; the mandatory Windows-green half is false. That one red mandatory lane is independently sufficient for NO-GO. F020 and F021 also prevent representing this as a clean residual closeout.

## 11. Ordered fixes required for a GO attempt

1. Reopen #44 and fix the C4875/C2220 failure without muting it. Prove `Windows (MSVC)` Build and Test success under `/WX` on the replacement `origin/master` SHA.
2. Make SBOM tree/property coverage fail-closed and require the seed scanner process to return non-zero; re-evaluate #42 against that guard.
3. Correct the issue evidence and repository status documents only after the new synchronized run completes. At minimum, remove the false #44 proof and reconcile CI-THESIS, OpenSpec tasks, the residual tracker, NOTICE, the threat model, and the stale gsl comment.
4. Remove the deleted FluidSynth Automake subdirectory/archive references.
5. Re-run this audit against the newly resolved `origin/master`; require ASan, UBSan, TSan, Fuzz, Windows, and Dependency Scan all green on that single SHA.
