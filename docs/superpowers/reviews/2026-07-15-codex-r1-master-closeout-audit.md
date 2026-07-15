# Independent R1 master closeout re-audit

## 1. Header

| Field | Value |
|---|---|
| Date / evidence cutoff | 2026-07-15, 12:58 MDT (18:58 UTC) |
| Auditor model | OpenAI Codex (GPT-5; exact serving build not exposed) |
| Branch under audit | master |
| AUDITED_SHA | 621a099944f5c7d82ed1a00c607a57fbc959b4c7 |
| Audited CI | Run 29440398476, completed **success**: https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29440398476 |
| Prior NO-GO evidence | Run 29437942535, SHA 42c30c46b88fc30891f7e6a25b629cd0808a5154: https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29437942535 |
| PR #46 | **MERGED** at f39b3dab1c43a44f17c7d070e89b477bae9e1c91: https://github.com/CharlesHoskinson/ProjectLegends/pull/46 |

## 2. Executive summary

**Result: FAIL. Verdict: NO-GO.** The mandatory runtime gates are green on the synchronized master SHA, but the dependency baseline and documentation-honesty acceptance conditions are not satisfied.

- origin/master was fetched first and pinned to 621a099944f5c7d82ed1a00c607a57fbc959b4c7. The latest exact-SHA CI run is a completed master push with conclusion success.
- F013 is resolved at lane scope: CrashBreadcrumb now serializes add, read/readInto, clear, and totalCount with one mutex. Exact TSan configured for C++23, built, passed 4,512/4,512 tests, and emitted no ThreadSanitizer warning or summary with an empty active suppression list.
- F014 is resolved at lane scope: Windows built and passed 4,500/4,500 tests. There is no C2220, no breadcrumb C4324, and no C4875 attached to legends_app or the application entrypoints.
- ASan and UBSan each passed 4,512 tests; Fuzz used Clang 19.1.1, created corpus/config, completed all five 31-second smoke invocations and all five 61-second main invocations; Linux gcc/clang and C ABI are green.
- The Dependency Scan job is mechanically fail-closed: the scanner digest matched, generator check reported five components, five packages were parsed, and the known-vulnerable seed returned rc=1. Its production artifact nevertheless contains zero results and zero packages.
- F015 is only partially remediated. The SBOM now truthfully labels the vendored header as FluidSynth 1.1.6-noglib, but pkg:generic/fluidsynth@1.1.6 produces no OSV match, so the two #43 ignore rules are not exercised even though both OSV records list v1.1.6 as affected. The rewritten active-pin generator also omits LEGENDS_DEP_MT32EMU_TAG although CMake consumes it in a FetchContent declaration.
- Issue #39 was correctly reopened, while #40/#42/#43/#44 remain open. Checked OpenSpec tasks 3.1, 4.1, and 4.2 still overclaim evidence; CI-THESIS also describes completed residuals as pending.
- Current finding counts: **0 Critical, 0 High, 2 Medium, 0 Low, 0 Informational**.

## 3. Dimension scorecard

| Dimension | Score | Evidence sentence |
|---|---:|---|
| Security | **3/5** | The scanner binary is version-and-digest pinned and #43 is issue-linked, but the production result is empty for a known-affected FluidSynth version and an active mt32emu pin disappeared from inventory. |
| Correctness | **5/5** | ASan, UBSan, TSan, Fuzz, Windows, Linux gcc/clang, and C ABI are all green on one audited SHA; the former breadcrumb race is mutex-serialized and exact TSan is clean. |
| Maintainability | **3/5** | TSan suppressions are empty and the Windows warning policy is scoped, but the generator's claimed active-pin map omits a real FetchContent pin and the dead FluidSynth CMake pin remains declared. |
| Documentation honesty | **2/5** | #39 was honestly reopened, but checked tasks 3.1/4.1/4.2 are not supported, live-green tasks remain stale, and CI-THESIS does not reflect the exact-SHA result. |
| CI/CD integrity | **3/5** | Mandatory lanes and the seed control fail closed, but the production dependency job can return success with an empty results set for the component it claims to baseline. |
| Process/governance | **3/5** | The no-demotion rule remains intact and premature #39 closure was corrected, but dependency and closeout status were asserted before their exit evidence was complete. |

## 4. Scope and method

- Ran git fetch origin master before scoring; pinned and read static evidence from the origin/master git object with git show and git grep.
- Queried gh run list, the Actions run/jobs APIs, and raw job logs. Monitored run 29440398476 until GitHub recorded its terminal workflow and job conclusions.
- Downloaded artifact 8353165188 into memory and parsed dependency-scan/vendored-sbom.json and seed-vuln.json without writing either artifact to disk.
- Queried the official OSV API and records for CVE-2021-21417 and CVE-2025-56225. References: https://osv.dev/vulnerability/CVE-2021-21417 and https://osv.dev/vulnerability/CVE-2025-56225.
- Queried PR #46 and issues #38, #39, #40, #42, #43, #44, #45, #47, and #48, including the #39 close/reopen timeline.
- The local checkout was on docs/r1-parallel-fill, not master; no conclusion relies on local branch contents. All product/static conclusions use the pinned origin/master object.
- graphify-out/graph.json was absent. No graph was generated because the audit's write-only rule permits only this report.
- No product code, workflow, test, issue, or other documentation was modified. E15 was not built locally because configure/build output would violate the write-only restriction.

## 5. Mandatory gate matrix

| Gate | Actions conclusion | Audit status | Primary evidence |
|---|---|---|---|
| address Sanitizer | success | **PASS** | C++23 PASS; 4,512/4,512 tests; no alloc-dealloc-mismatch, AddressSanitizer, LeakSanitizer, or ERROR diagnostic: https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29440398476/job/87437543407 |
| undefined Sanitizer | success | **PASS** | C++23 PASS; 4,512/4,512 tests; no runtime error or UndefinedBehaviorSanitizer diagnostic: https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29440398476/job/87437543394 |
| thread Sanitizer | success | **PASS** | C++23 PASS; build success; 4,512/4,512 tests; no WARNING or SUMMARY from TSan: https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29440398476/job/87437543361 |
| Fuzz Testing | success | **PASS** | Clang 19.1.1; all five smoke and all five main targets completed: https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29440398476/job/87439305297 |
| Windows (MSVC) | success | **PASS** | Build success and 4,500/4,500 tests; no C2220: https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29440398476/job/87437543362 |
| MSan | absent | **PASS** | Matrix is address, undefined, thread only; issue #40 remains open. |
| Linux (gcc) | success | **PASS** | https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29440398476/job/87437543505 |
| Linux (clang) | success | **PASS** | https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29440398476/job/87437543512 |
| Linux IPC (gcc) | success | **PASS** | https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29440398476/job/87437543399 |
| C ABI Verification | success | **PASS** | https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29440398476/job/87437543339 |
| Dependency Scan | success | **FAIL** | Pin/check/seed mechanics pass, but the production artifact has results=[], the FluidSynth ignores are not exercised, and active mt32emu is omitted: https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29440398476/job/87437543480 |

Mandatory runtime lane result: **PASS**. Overall acceptance remains **FAIL** because Dependency Scan is a separate R1 residual requirement.

## 6. Residual matrix

| Residual | Live state | Audit status | Evidence |
|---|---|---|---|
| #38 — g_active_instance | CLOSED | **PASS / PROVEN** | src/legends/legends_embed_api.cpp:68 remains std::atomic with acquire/release operations; the suppression is absent and exact TSan is green. https://github.com/CharlesHoskinson/ProjectLegends/issues/38 |
| #39 — CrashBreadcrumb | OPEN (reopened) | **PASS / PROVEN technically** | One mutex guards every mutable member access in crash_breadcrumb.cpp:33-90; concurrent breadcrumb tests and all 4,512 TSan tests pass without an active suppression. The issue is conservatively still open. https://github.com/CharlesHoskinson/ProjectLegends/issues/39 |
| #40 — MSan re-entry | OPEN | **PASS (parked)** | MSan remains absent and docs/ci/msan-reentry.md retains concrete re-entry conditions. https://github.com/CharlesHoskinson/ProjectLegends/issues/40 |
| #42 — automated/full SBOM | OPEN | **FAIL (partial generator unsound)** | Full-tree automation may remain open, but the current pin generator drops LEGENDS_DEP_MT32EMU_TAG even though cmake/dependencies.cmake:118-128 consumes it. https://github.com/CharlesHoskinson/ProjectLegends/issues/42 |
| #43 — FluidSynth CVEs | OPEN | **FAIL (baseline not exercised)** | The version matches version.h, but the production result is empty and both ignore IDs are absent from output. The generic purl query returns no match although OSV lists v1.1.6 as affected. https://github.com/CharlesHoskinson/ProjectLegends/issues/43 |
| #44 — scoped /wd4875 | OPEN | **PASS at R1 scope** | The disable is confined to legends_gsl_msvc_options; legends_app and entrypoints consume it; exact Windows builds/tests. aibox_core still emits non-fatal C4875 warnings, so full removal remains correctly open. https://github.com/CharlesHoskinson/ProjectLegends/issues/44 |
| 4.3 — known-vulnerable seed | tracker checked | **PASS (mechanism)** | Exact log records seed rc=1; the step fails if rc=0, requires a non-empty artifact, and has no continue-on-error or verdict-path || true. |

Open #40/#42/#43/#44 are not failures merely because they remain open. #42/#43 fail here because the implemented production control is semantically incomplete, not because the explicitly deferred source upgrade or full vendored-tree automation is required.

## 7. OpenSpec honesty

Every task in openspec/changes/ci-stabilize-mandatory-lanes/tasks.md was reconciled with live evidence.

| Task | Checkbox | Audit |
|---|---|---|
| 1.1 local TSan build/ctest | [ ] | **PASS (honest incomplete)** — local TSan was not run and the note says CI is source of truth. |
| 1.2 race-family issues | [x] | **PASS** — #38, #39, and #45 exist; #39 is reopened. |
| 1.3 suppression file/hygiene | [x] | **PASS** — policy exists and there are no active race/deadlock/mutex/thread entries. |
| 1.4 intentional wrong-thread gate | [x] | **PASS** — exact TSan skips ThreadSafetyTest.ConcurrentDestroyAttempts and the intentional wrong-thread family. |
| 1.5 suppressions/symbolizer and zero reports | [ ] | **FAIL (stale underclaim)** — exact run now supplies the requested green, empty-suppression evidence but the task remains unchecked and cites only the prior red run. |
| 1.6 preset parity / red-without proof | [ ] | **PASS (honest incomplete)** — the without-file proof was not performed; it is not hidden. |
| 1.7 remove TSan allow-failure | [x] | **PASS** — no job-level mute; the earlier red run failed visibly. |
| 2.1 MSan re-entry issue | [x] | **PASS** — #40 remains open. |
| 2.2 remove memory matrix entry | [x] | **PASS** — MSan is absent and workflow links #40. |
| 3.1 reproduce each root and file one issue | [x] | **FAIL** — #47 tracks ASan, but repository issue searches for UBSan/undefined enum/dosbox name return no issue; FINDING-002 is not a GitHub issue. |
| 3.2 ASan/UBSan green | [x] | **PASS** — both exact-SHA jobs pass 4,512 tests. |
| 3.3 fuzz build/smoke green | [x] | **PASS** — exact Fuzz passes build, corpus, five smoke, and five main invocations. |
| 4.1 supported package source/artifact | [x] | **FAIL** — the artifact is present, but production results are empty and an actually consumed mt32emu pin is omitted. |
| 4.2 baseline findings | [x] | **FAIL** — the two FluidSynth ignores are issue-linked but never exercised by the production scan. |
| 4.3 unmute + seeded failure | [x] | **PASS** — exact master-push job runs and the seed fails closed. |
| 5.1 demotion rule | [x] | **PASS** — CONTRIBUTING.md:227-241 and the OpenSpec SHALL rule remain intact. |
| 5.2 synchronized mandatory green | [ ] | **FAIL (stale underclaim)** — run 29440398476 now proves the runtime stack green, but the task still records only the earlier NO-GO. |
| 5.3 update audit-wiki + CI-THESIS | [ ] | **PASS (honest incomplete)** — the checkbox admits the work is not done; CI-THESIS line 30 is consequently stale and fails the separate documentation acceptance check. |

The dangerous checked overclaims are 3.1, 4.1, and 4.2. Tasks 1.5 and 5.2 are conservative but no longer match live evidence. The residual tracker remains historical rather than falsely claiming closure, but CI-THESIS still lists #38/#39 and the seed proof as pending residuals.

## 8. Findings

### F017 — [MEDIUM] The production dependency scan is still semantically false-green

| Field | Value |
|---|---|
| Severity | Medium |
| Category | Security / Supply chain / CI integrity |
| Location | scripts/generate_vendored_sbom.py:32-53,69-88,111; docs/ci/vendored-sbom.cdx.json:58-62; cmake/dependencies.cmake:28-29,118-128; .github/workflows/ci.yml:843-865 |
| Evidence | Exact job https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29440398476/job/87437543480 parses five packages and says No issues found. Uploaded artifact 8353165188 has vendored-sbom.json with zero results/packages/vulnerabilities, while its seed artifact has one package and five vulnerabilities. A POST for pkg:generic/fluidsynth@1.1.6 to https://api.osv.dev/v1/query returns an empty object; querying the upstream v1.1.6 tag commit 62e375c71c815ca12f859b8722db5dff12f0c897 returns exactly CVE-2021-21417 and CVE-2025-56225, whose official records list v1.1.6 as affected. Separately, LEGENDS_DEP_MT32EMU_TAG is used by FetchContent but absent from ACTIVE_PIN_MAP and the generated SBOM. |
| Impact | The job can be green while neither demonstrating the intended #43 ignore baseline nor inventorying every known active FetchContent pin. Component-count and seed controls prove that the scanner runs, not that production identities reach a matching advisory source. |
| Recommendation | Represent FluidSynth with scanner input that can match its Git advisory range, preferably repository plus exact vendored commit/source provenance; add a production positive control that requires CVE-2021-21417 and CVE-2025-56225 to appear as ignored specifically by #43. Restore mt32emu to the active-pin inventory or mechanically fail when any consumed LEGENDS_DEP_*_TAG lacks a component. Remove the dead FluidSynth CMake pin to eliminate contradictory identity. |
| Residual risk | A version macro alone cannot establish downstream patch state. Even after matching by version, record the vendored source commit/hash so false positives and silently patched forks can be distinguished. |
| Status | Open under #42/#43; F015 is only partially resolved. |

### F018 — [MEDIUM] Closeout documentation still does not match the synchronized evidence

| Field | Value |
|---|---|
| Severity | Medium |
| Category | Documentation honesty / Process governance |
| Location | openspec/changes/ci-stabilize-mandatory-lanes/tasks.md:12-17,28-29,40-48,53-59; CI-THESIS.md:30; docs/ci/r1-residual-closeout.md:5-37 |
| Evidence | Tasks 3.1, 4.1, and 4.2 are checked despite a missing UBSan root-cause issue and F017. Tasks 1.5 and 5.2 remain unchecked after exact-SHA green proof. CI-THESIS still lists #38/#39 suppression burndown and the seed proof as residuals. Positive correction: #39 was reopened at 18:24:08 UTC and the residual tracker does not falsely call it closed. |
| Impact | Readers cannot tell whether R1 is technically green, administratively incomplete, or accepted with a dependency blind spot. A later closeout can again substitute checked narrative for synchronized evidence. |
| Recommendation | Keep 4.1/4.2 unchecked until F017 has a scanner-effective positive proof; file/link the promised UBSan issue or uncheck 3.1; record run 29440398476 for 1.5/5.2; update CI-THESIS and the residual tracker only after the dependency acceptance run is green. Close #39 only after recording the exact TSan evidence. |
| Residual risk | Hand-maintained status documents will drift again unless task transitions require an exact run/job URL whose SHA contains the claimed change. |
| Status | Open. |

### Prior finding remap (F001-F012)

| Prior finding | Status | Current SHA evidence |
|---|---|---|
| F001 — ASan mass failures/leaks | **Resolved** | Exact ASan passes 4,512 tests; DOSBoxContext move ownership transfer remains at dosbox_context.cpp:1114-1200. |
| F002 — UBSan invalid enums | **Resolved technically** | Exact UBSan passes 4,512 tests; documentation issue-tracking gap remains F018. |
| F003 — missed wrong-thread exclusion | **Resolved** | Exact TSan log shows ConcurrentDestroyAttempts and the intentional wrong-thread family skipped. |
| F004 — fuzz config dependency/corpus | **Resolved** | Exact Fuzz builds five targets, creates corpus/config, and completes all smoke/main runs. |
| F005 — Windows HandshakeAck red | **Resolved** | Exact Windows passes 4,500 tests. |
| F006 — scanner exits 128/no sources | **Resolved mechanically** | Exact job parses five packages and exercises the seed; semantic false-green is F017. |
| F007 — dependency coverage gap | **Open / partial** | FluidSynth matching is ineffective and an active mt32emu pin was removed from inventory. |
| F008 — mutable/unverified scanner | **Resolved** | v2.0.1 and SHA-256 are pinned; exact downloaded digest matches; no releases/latest. |
| F009 — TSan suppression hygiene | **Resolved** | No active entries and exact TSan is green. |
| F010 — checked tasks overstate completion | **Open** | F018 identifies checked overclaims and stale status. |
| F011 — global /wd4875 | **Resolved at R1 scope** | Disable is scoped; exact Windows is green. #44 correctly remains open for warning removal. |
| F012 — fail-closed controls | **Resolved** | Mandatory failures were visible historically; current jobs and seed inversion are not muted. |

### Prior closeout finding follow-up (F013-F016)

| Finding | Status | Current SHA evidence |
|---|---|---|
| F013 — breadcrumb race | **Resolved** | Mutex guards all shared state; exact TSan passes 4,512 tests without a race suppression. |
| F014 — Windows gsl/alignment build failure | **Resolved** | legends_app/entrypoints receive the scoped option, breadcrumb alignment was removed, and Windows passes build plus 4,500 tests. |
| F015 — phantom FluidSynth 2.3.5 | **Partial** | Runtime version is corrected to 1.1.6-noglib, but effective matching and active-pin completeness fail in F017. |
| F016 — premature closure/docs | **Partial** | #39 was reopened and several tasks were unchecked; remaining mismatches are F018. |

## 9. E-suite results

| ID | Status | Result |
|---|---|---|
| E1 | **PASS** | origin/master pinned to 621a099944f5c7d82ed1a00c607a57fbc959b4c7; last 15 commits listed below. |
| E2 | **PASS** | Latest exact-SHA CI is completed success, run 29440398476: https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29440398476 |
| E3 | **PASS** | ASan, UBSan, TSan, Fuzz, Windows, Dependency Scan, Linux gcc/clang, Linux IPC, and C ABI all have success conclusions. |
| E4 | **PASS** | TSan C++23 validation and build pass; ctest passes 4,512/4,512; no WARNING/SUMMARY; active suppression count is zero. |
| E5 | **PASS** | ASan passes 4,512/4,512; no dual-stdlib cascade, alloc-dealloc mismatch, ASan error, or leak diagnostic. |
| E6 | **PASS** | Clang 19.1.1, C++23 PASS, corpus/config present, five 31-second smoke and five 61-second main runs complete. |
| E7 | **FAIL** | Pin/digest, generator check, five-package parse, and seed rc=1 work; production artifact is empty for FluidSynth and mt32emu is omitted. |
| E8 | **PASS** | Anchored search finds zero active race, deadlock, mutex, or thread suppression entries. |
| E9 | **PASS** | g_active_instance is static std::atomic at legends_embed_api.cpp:68 with acquire/release operations. |
| E10 | **PASS** | The seqlock was removed. One mutex establishes happens-before across add/readInto/clear/totalCount, eliminating torn reads, ABA, wrap-order, and concurrent-clear races. |
| E11 | **PASS (narrow criterion)** | /wd4875 is absent from legends_compile_options and exists only on legends_gsl_msvc_options. Exact Windows is green; non-fatal aibox_core C4875 noise remains #44. |
| E12 | **PASS (mechanical only)** | Exact CI generator --check reports OK with five components; E7/F017 explain the semantic failure. |
| E13 | **PASS** | #38/#45/#47/#48 closed; #39 reopened; #40/#42/#43/#44 open. State is conservative and matches the current tracker. |
| E14 | **FAIL** | Checked tasks 3.1/4.1/4.2 are false; 1.5/5.2 and CI-THESIS are stale after the new run. |
| E15 | **BLOCKED** | WSL has CMake 4.2.3 and g++-13, but no trusted exact-SHA binary; a configure/build would violate the instruction to write only this report. Exact CI supplies decisive sanitizer/Windows evidence. |

### E1 commit log

    621a099 fix(r1): mutex breadcrumb (F013); Windows gsl scope (F014); honest FluidSynth SBOM (F015)
    6255f02 docs: qualify local game-playing model
    42c30c4 docs(audit): Codex GPT-5.6 R1 master closeout audit brief
    733bb96 fix(r1): clear TSan residuals #38/#39; SBOM generator; seed vuln proof
    f0feebf docs(r1): residual closeout — tasks, SBOM, scoped C4875, master dep-scan
    f39b3da Merge pull request #46 from CharlesHoskinson/ci/r1-stabilize-mandatory-lanes
    c9bf553 docs: specify Go clean-room emulator program
    98450e6 ci(fuzz): drop unverified llvm.sh fallback (FINDING-008 hygiene)
    2fdbab9 fix(fuzz): seed corpus/config for fuzz_config_parser smoke (FINDING-004)
    f5b2804 fix(fuzz): link legends_pal and platform_dirs for input/config targets (004)
    b842734 fix(ci,r1): TSan -Wno-error=tsan; fuzz clang-19; ASan move leak (001/003/004)
    5452aab fix(ci): sanitizers use g++-13; fuzz unlocks libstdc++ expected (001/004)
    d706ff1 fix(fuzz): build with clang-18 + libstdc++ (not g++ / not libc++) (FINDING-004)
    2382b6c docs(ci): ASan cluster table for FINDING-001 (libc++ dual-stdlib)
    26a52ed ci(r1): sanitizers use clang+libstdc++ (g++-13), not libc++ (#47)

### Adversarial probe results

| Probe | Result | Evidence |
|---|---|---|
| 1. Empty suppressions + green TSan | **PASS** | Active entries are zero and exact TSan succeeds after the mutex change. #38 is proven; #39 is technically proven but remains open. |
| 2. Seed-step false green | **PASS** | set +e only captures scanner status; set -e is restored; rc=0 forces exit 1; output must be non-empty; exact rc=1. |
| 3. SBOM theater | **FAIL** | Count checks prevent zero declared components, but the production vulnerability artifact still has zero results and an active mt32emu pin is absent. |
| 4. llvm.sh / latest binary | **PASS** | No curl-to-bash llvm.sh path and no releases/latest; fuzz installs clang-19 by apt and scanner uses a tagged URL plus digest. |
| 5. Task honesty | **FAIL** | Checked tasks 3.1, 4.1, and 4.2 are unsupported; 1.5/5.2 and CI-THESIS are stale. |
| 6. #43 version honesty | **FAIL (partial fix)** | SBOM version now matches version.h, but its generic purl returns no advisory match and #43 ignores are not exercised. |
| 7. Seqlock soundness | **PASS after redesign** | The seqlock no longer exists; one mutex serializes writers, readers, wrap, totalCount, and clear, and exact TSan is clean. |

## 10. Verdict

~~~text
R1 MASTER CLOSEOUT: NO-GO
Mandatory lanes: PASS
Residual TSan empty suppressions: PROVEN
Dependency scan + seed proof: FAIL
Overall: The synchronized master SHA is green across every mandatory runtime
lane and resolves F013/F014. R1 still fails because the production dependency
artifact does not exercise the FluidSynth baseline, omits an active mt32emu pin,
and closeout documentation does not match live evidence.
~~~

## 11. What would flip NO-GO → GO

1. Make FluidSynth scanner-effective: supply repository plus exact vendored commit/source provenance (or another OSV-supported identity), require CVE-2021-21417 and CVE-2025-56225 to be observed and ignored only through the issue-linked #43 rules, and fail if the production artifact has no FluidSynth result.
2. Restore LEGENDS_DEP_MT32EMU_TAG to the generated inventory or add a mechanical coverage assertion that every LEGENDS_DEP_*_TAG consumed by a FetchContent GIT_TAG has a component.
3. Reconcile OpenSpec: file/link the promised UBSan root-cause issue or uncheck 3.1; keep 4.1/4.2 unchecked until the production proof is real; record the exact TSan and synchronized green run for 1.5/5.2.
4. Update CI-THESIS and the residual tracker with the current states; close #39 only after attaching the exact TSan job evidence.
5. Push those corrections and require one completed master CI run where the same SHA has ASan, UBSan, TSan, Fuzz, Windows, Linux gcc/clang, C ABI, and the scanner-effective Dependency Scan all passing.
