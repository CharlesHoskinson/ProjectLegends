# Independent R1 master closeout audit

## 1. Header

| Field | Value |
|---|---|
| Date / evidence cutoff | 2026-07-15, 12:14 MDT (18:14 UTC) |
| Auditor model | OpenAI Codex (GPT-5; exact serving build not exposed) |
| Branch | `master` |
| `AUDITED_SHA` | `42c30c46b88fc30891f7e6a25b629cd0808a5154` |
| Audited CI | Run `29437942535`, completed **failure**: <https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29437942535> |
| Historical pre-residual CI | Run `29435150647`, SHA `98450e6928ae038b6235a9be8ef2eb65531624c2`, completed success: <https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29435150647> |
| PR #46 | **MERGED** at `f39b3dab1c43a44f17c7d070e89b477bae9e1c91`: <https://github.com/CharlesHoskinson/ProjectLegends/pull/46> |

## 2. Executive summary

**Result: FAIL. Verdict: NO-GO.** R1 is not closed on `master` at the synchronized audited SHA.

- The exact-SHA CI run completed, so this verdict is no longer merely `UNPROVEN`: required `thread Sanitizer` and `Windows (MSVC)` jobs are both **red**.
- TSan configured for C++23 and built successfully, then reported a real `CrashBreadcrumb` race between the writer at `crash_breadcrumb.cpp:57` and reader `memcpy` at line 100. Issue #39 was closed before this proof and is not resolved.
- Windows configured successfully but failed to build. `legends_app` receives gsl-lite C4875 warnings without the scoped `/wd4875` interface, and the new `alignas(64)` breadcrumb slot emits C4324; `/WX` promotes both to C2220. Its tests never ran.
- ASan, UBSan, Fuzz, Linux gcc/clang, C ABI, and Linux IPC are green on the audited SHA. ASan and UBSan each ran 4,512 tests with zero failures; Fuzz completed the five-target smoke and all five 60-second push targets.
- The `Dependency Scan` Actions job is mechanically fail-closed: the binary digest matched, generator `--check` reported six components, the production command exited zero, and the seed scan exited one as expected. The audit nevertheless fails the dependency acceptance because the so-called production SBOM reports FluidSynth `2.3.5` while the compiled in-tree copy declares `1.1.6-noglib`.
- The SBOM generator checks a CMake variable that is never used to fetch or select FluidSynth. Its green `--check` therefore proves agreement with a phantom pin, not agreement with the runtime vendored tree.
- Open issues #40, #42, #43, and #44 remain open as alleged. Closed issues #38 and #39 are not both proven: #38 is static-atomic but cannot meet the required green-TSan proof; #39 is directly disproved.
- Current finding counts: **0 Critical, 2 High, 2 Medium, 0 Low, 0 Informational**.

## 3. Dimension scorecard

| Dimension | Score | Evidence sentence |
|---|---:|---|
| Security | **2/5** | The scanner is version-and-digest pinned and ignores are issue-linked, but the production SBOM substitutes FluidSynth `2.3.5` for the runtime `1.1.6-noglib` tree, so the clean verdict is not an honest inventory verdict. |
| Correctness | **1/5** | Two mandatory gates are red on the audited SHA, and TSan directly confirms the allegedly fixed #39 race. |
| Maintainability | **2/5** | Suppressions are textually empty and `/wd4875` is scoped, but the scope omits a real gsl consumer and the generator enforces a disconnected pin. |
| Documentation honesty | **1/5** | #39, the residual tracker, suppression history, and several checked OpenSpec tasks claim completion that exact-SHA CI disproves. |
| CI/CD integrity | **2/5** | Failures are visible and the seed control is genuine, but TSan/Windows are red and a non-empty count assertion cannot prevent a semantically false SBOM. |
| Process/governance | **2/5** | The demotion rule remains intact, but #39 was closed before its exit criterion was demonstrated and checked acceptance tasks were not rolled back when master failed. |

## 4. Scope and method

- Ran `git fetch origin master` first and pinned `origin/master` to `42c30c46b88fc30891f7e6a25b629cd0808a5154`.
- Read static evidence from the pinned git object with `git show` / `git grep`, not from narrative claims. The local checkout was one documentation-only commit ahead; no product conclusion depends on that local commit.
- Queried CI with `gh run list`, `gh run view`, the Actions runs/jobs API, and raw per-job logs. The exact run was initially in progress; the audit waited until it completed at 18:14:20 UTC.
- Queried PR #46 and issues #38, #39, #40, #42, #43, #44, #45, #47, and #48 with `gh`, including closure comments.
- Compared the FluidSynth inventory with the committed runtime version header and the OSV records for CVE-2021-21417 and CVE-2025-56225: <https://osv.dev/vulnerability/CVE-2021-21417> and <https://osv.dev/vulnerability/CVE-2025-56225>.
- Did not modify product code, workflows, tests, issues, or other documentation. No local configure/build was performed because the user's write-only restriction permits only this report; E15 is therefore `BLOCKED` separately from the exact CI evidence.

## 5. Mandatory gate matrix

| Gate | Actions conclusion | Audit status | Primary evidence |
|---|---|---|---|
| `address Sanitizer` | success | **PASS** | 4,512/4,512 tests; no `alloc-dealloc-mismatch`, ASan error, or leak summary: <https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29437942535/job/87429208597> |
| `undefined Sanitizer` | success | **PASS** | 4,512/4,512 tests; no UBSan runtime error: <https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29437942535/job/87429208746> |
| `thread Sanitizer` | failure | **FAIL** | `CrashBreadcrumbTest.ConcurrentReadWriteSafe`; TSan write at line 57 races reader `memcpy` at line 100; ctest exit 8: <https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29437942535/job/87429208625> |
| `Fuzz Testing` | success | **PASS** | Clang 19.1.1; corpus/config exists; all five 30-second smoke invocations and five 60-second push invocations completed: <https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29437942535/job/87433224578> |
| `Windows (MSVC)` | failure | **FAIL** | Configure passed; build failed on C2220/C4875 in `legends_app` and C2220/C4324 at `crash_breadcrumb.h:64`; test step skipped: <https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29437942535/job/87429208725> |
| MSan absent | no job | **PASS** | Matrix is exactly `[address, undefined, thread]`; `.github/workflows/ci.yml:328-377`; re-entry remains #40. |
| `Linux (gcc)` | success | **PASS** | <https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29437942535/job/87429208653> |
| `Linux (clang)` | success | **PASS** | <https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29437942535/job/87429208728> |
| `C ABI Verification` | success | **PASS** | <https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29437942535/job/87429208667> |
| `Dependency Scan` | success | **FAIL** | Mechanics and seed proof pass, but `docs/ci/vendored-sbom.cdx.json:58-62` inventories FluidSynth `2.3.5` while `engine/include/fluidsynth/version.h:34-37` declares runtime `1.1.6-noglib`: <https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29437942535/job/87429208590> |

Mandatory lane result: **FAIL**. Either TSan or Windows alone forces NO-GO under the hard rules.

## 6. Residual matrix

| Residual | Live state | Audit status | Evidence |
|---|---|---|---|
| #38 — `g_active_instance` | CLOSED | **FAIL (unproven closeout)** | `src/legends/legends_embed_api.cpp:68` is `std::atomic`, and the active suppression is gone. The contract also requires TSan green without the line; exact-SHA TSan is red and stops on #39. <https://github.com/CharlesHoskinson/ProjectLegends/issues/38> |
| #39 — `CrashBreadcrumb` | CLOSED | **FAIL** | Exact-SHA TSan reports the same family in `add`/`readInto`. The close comment's requested confirmation failed. <https://github.com/CharlesHoskinson/ProjectLegends/issues/39> |
| #40 — MSan re-entry | OPEN | **PASS (parked)** | MSan is absent, issue remains open, and `docs/ci/msan-reentry.md:6-19` has concrete re-entry criteria. <https://github.com/CharlesHoskinson/ProjectLegends/issues/40> |
| #42 — automated/full SBOM | OPEN | **FAIL (partial implementation unsound)** | The pin generator and CI check exist, but they do not inventory the in-tree FluidSynth version and full vendored coverage remains open. <https://github.com/CharlesHoskinson/ProjectLegends/issues/42> |
| #43 — FluidSynth CVEs | OPEN | **FAIL (baseline inventory dishonest)** | Both ignores link #43, but the SBOM version does not represent the vulnerable runtime tree. The issue correctly remains open. <https://github.com/CharlesHoskinson/ProjectLegends/issues/43> |
| #44 — scoped `/wd4875` | OPEN | **FAIL (partial / Windows red)** | The disable is no longer global, but `legends_app` directly links gsl-lite without `legends_gsl_msvc_options`; exact Windows fails on C4875. <https://github.com/CharlesHoskinson/ProjectLegends/issues/44> |
| 4.3 — known-vuln seed | tracker says closed | **PASS (mechanism)** | Exact log: lodash fixture scan returned `rc=1`; the step would fail if `rc=0`; no `continue-on-error` or verdict `|| true`. |

Open #40/#42/#43/#44 are not R1 failures merely because they remain open. The failures above arise from the red mandatory gate and dishonest production inventory, not from requiring the explicitly non-required future work.

## 7. OpenSpec honesty

Every checked task in `openspec/changes/ci-stabilize-mandatory-lanes/tasks.md` was reconciled against live evidence.

| Task | Status | Audit |
|---|---|---|
| 1.1 local TSan build/ctest | **FAIL** | Lines 3-5 check the task while admitting the local run is Windows-blocked; the stated local verification was not done. |
| 1.2 tracked race-family issues | **PASS** | #38, #39, and #45 exist with exit language, although #39 was later closed incorrectly. |
| 1.3 suppression file/hygiene | **FAIL** | The file exists and has policy, but a live #39 race has neither an active suppression nor an open issue; the claimed fix-and-remove exit failed. |
| 1.4 intentional wrong-thread gate | **PASS** | Exact TSan log shows `ThreadSafetyTest.ConcurrentDestroyAttempts` skipped under TSan. |
| 1.5 suppressions/symbolizer and zero reports | **FAIL** | The cited run is pre-removal; exact current TSan emits a report. |
| 1.6 preset parity, green with/red without | **FAIL** | Line 17 admits the without-file proof was not performed; exact current run is red with the file. |
| 1.7 remove TSan allow-failure | **PASS** | No job `continue-on-error` / `allow_failure`; failures are visible. |
| 2.1 file MSan re-entry issue | **PASS** | #40 remains open. |
| 2.2 remove memory matrix entry | **PASS** | MSan is absent and workflow points to #40. |
| 3.1 reproduce and issue each root cause | **FAIL** | #47 exists for ASan; no UBSan enum root-cause issue was found despite the checkbox wording. The code fix itself is green. |
| 3.2 ASan/UBSan green | **PASS** | Both exact-SHA jobs pass all 4,512 tests. |
| 3.3 fuzz build/smoke green | **PASS** | Exact-SHA Fuzz job passes build, corpus, smoke, and all push targets. |
| 4.1 supported package source | **FAIL** | The JSON is parseable and non-empty but is not an honest production inventory for FluidSynth. |
| 4.2 baseline findings | **FAIL** | Ignores are issue-linked, but the generator does not identify the actual `1.1.6-noglib` runtime component. |
| 4.3 unmute + seeded failure | **PASS** | Exact master-push job runs and seed fail-closed control works. |
| 5.1 demotion rule | **PASS** | `CONTRIBUTING.md:227-241` and the OpenSpec SHALL rule remain intact. |
| 5.2 end-to-end mandatory green | **FAIL** | The checkbox cites `98450e6`; current synchronized master is TSan/Windows red. |
| 5.3 update docs after green | **FAIL** | `r1-residual-closeout.md:5-27`, `CI-THESIS.md:30`, and suppression history do not reflect the failed post-residual evidence. |

## 8. Findings

### F013 — [HIGH] The #39 seqlock is a real data race and the mandatory TSan lane is red

| Field | Value |
|---|---|
| Severity | High |
| Category | Correctness / CI integrity |
| Location | `src/app/crash_breadcrumb.cpp:38-67,78-120`; `src/app/crash_breadcrumb.h:60-64`; `tests/unit/test_crash_breadcrumb.cpp:236-266` |
| Evidence | Exact job <https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29437942535/job/87429208625> configured C++23 and built, then TSan reported a write at `add():57` racing `readInto()`'s `memcpy` at line 100; 1/4,512 tests failed, ctest exit 8. |
| Impact | A mandatory gate is red. The non-atomic payload access is undefined behavior under the C++ memory model; reading and later rejecting a torn snapshot does not retroactively remove the race. The implementation can also return stale data because `write_index_` is incremented before a slot is claimed, and an older reserved writer can overwrite a newer same-slot writer after wrap. `clear()` does not CAS-serialize with writers. |
| Recommendation | Reopen #39; remove the closed/proven claims; replace the payload protocol with one that creates legal C++ happens-before for every byte (for example, locked slots, atomic payload publication, or immutable snapshots), serialize `clear()`, and add tests that delay an older writer across a capacity wrap. Do not add `allow_failure`; rerun the full exact-SHA TSan job with no race suppression. |
| Residual risk | A one-writer/one-reader pass would still not prove multi-writer reservation order, wrap behavior, or concurrent clear; retain targeted stress tests in addition to the full TSan suite. |
| Status | Open; issue #39 is incorrectly closed. |

### F014 — [HIGH] Windows is red after the gsl-lite bump and breadcrumb change

| Field | Value |
|---|---|
| Severity | High |
| Category | Correctness / CI integrity / Maintainability |
| Location | `CMakeLists.txt:103-109,521-595`; `src/app/crash_breadcrumb.h:60-64`; `cmake/dependencies.cmake:19-22` |
| Evidence | Exact job <https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29437942535/job/87429208725> configured, then failed the build. `legends_app` compiles gsl-lite headers and directly links `gsl::gsl-lite-v1` at lines 589-595 but does not link `legends_gsl_msvc_options`, so C4875 becomes C2220 under `/WX`. The new aligned `Slot` also emits C4324 at `crash_breadcrumb.h:64`, promoted to C2220. The test step was skipped. |
| Impact | The mandatory Windows baseline cannot build, and current master provides no post-residual Windows test evidence for #48 or the new code. |
| Recommendation | Keep `/wd4875` scoped but attach the scope to every target that actually compiles gsl headers, including `legends_app`; address the C4324 layout warning explicitly rather than globally muting it; then run the full exact Windows build/test job. Keep #44 open and track the new C4324 regression if it is not handled in the same remediation. |
| Residual risk | Other transitive gsl consumers may be missing the interface; enumerate consumers from compile sources rather than maintaining a hand-curated four-target claim. |
| Status | Open; #44 partially tracks C4875, while C4324 is a new regression. |

### F015 — [MEDIUM] The production SBOM enforces a phantom FluidSynth pin

| Field | Value |
|---|---|
| Severity | Medium |
| Category | Security / Supply chain |
| Location | `docs/ci/vendored-sbom.cdx.json:18-20,58-62`; `scripts/generate_vendored_sbom.py:25-64,136-163`; `cmake/dependencies.cmake:28,96-109`; `engine/include/fluidsynth/version.h:34-37` |
| Evidence | The exact dependency job <https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29437942535/job/87429208590> reports six packages and a green scan. The SBOM says FluidSynth `2.3.5`; the runtime header says `1.1.6-noglib`. `git grep` finds `LEGENDS_DEP_FLUIDSYNTH_TAG` only in its declaration, the generated SBOM description, and generator map; the CMake FluidSynth block uses only `find_package` and never the tag. OSV lists v1.1.6 among affected versions for both tracked CVEs. |
| Impact | Component-count and generator checks prevent an empty scan but do not prevent version theater. The scan can miss vulnerabilities unique to the actual old vendored snapshot and gives reviewers a false production-clean signal. |
| Recommendation | Inventory the in-tree `1.1.6-noglib` component directly from the vendored version/source identity, separately inventory any real optional system/FetchContent dependency, and make `--check` compare those identities. Rerun with the issue-linked ignores and prove the intended findings are the ones suppressed. |
| Residual risk | A version macro alone may not identify downstream patches; record a source hash or commit provenance for the vendored snapshot and keep #42/#43 open until upgraded or removed. |
| Status | Open under #42/#43. |

### F016 — [MEDIUM] Closeout documents and issue closure overstate live evidence

| Field | Value |
|---|---|
| Severity | Medium |
| Category | Documentation honesty / Process governance |
| Location | `openspec/changes/ci-stabilize-mandatory-lanes/tasks.md:3-18,40-61`; `docs/ci/r1-residual-closeout.md:5-27`; `tsan-suppressions.txt:13-17`; `CI-THESIS.md:30`; issues #38/#39 |
| Evidence | #39 was closed at 17:43 UTC with a request to confirm TSan green; exact CI later failed that family. The residual tracker calls mandatory lanes and #39 closed, suppression history calls the removed entry/fix green using a pre-removal run, and tasks 1.1/1.5/1.6/5.2 remain checked despite contrary or missing proof. CI-THESIS still lists #38/#39 and the seed proof as residuals rather than current states. |
| Impact | Reviewers can mistake historical pre-residual green for synchronized master acceptance and close the release phase while hard gates are red. |
| Recommendation | Reopen #39, mark #38 unproven until a full green TSan run, uncheck false tasks, and update the residual tracker/CI-THESIS with the exact failed run and new findings. Re-check only after one synchronized SHA satisfies all exits. |
| Residual risk | Manually maintained status docs will drift again unless close comments and checkbox transitions require an exact run/job URL from a SHA containing the closing change. |
| Status | Open. |

### Prior finding remap (F001-F012)

| Prior finding | Status | Current SHA evidence |
|---|---|---|
| F001 — ASan mass failures/leaks | **Resolved** | Exact ASan passes 4,512 tests; move ownership transfer remains at `dosbox_context.cpp:1114-1200`. |
| F002 — UBSan invalid enums | **Resolved** | Exact UBSan passes 4,512 tests; name boundaries now accept `int`. |
| F003 — missed wrong-thread exclusion | **Resolved** | Exact TSan log shows `ThreadSafetyTest.ConcurrentDestroyAttempts` skipped as intended. |
| F004 — fuzz config dependency/corpus | **Resolved** | Exact Fuzz job builds all targets, creates `corpus/config`, and completes smoke/full targets. |
| F005 — Windows HandshakeAck red | **Superseded** | Historical `98450e6` Windows passed the original test; current Windows is red for the distinct F014 compile regressions. |
| F006 — scanner exits 128/no sources | **Resolved** | Exact job scans a six-component CycloneDX input and exercises the seed; semantic inventory defect is F015. |
| F007 — dependency coverage gap | **Partial** | Six CMake pins are present, but the runtime FluidSynth identity is wrong and full vendored coverage remains #42. |
| F008 — mutable/unverified latest scanner | **Resolved** | Workflow pins v2.0.1 and SHA-256; exact downloaded digest matches; no `releases/latest`. |
| F009 — TSan suppression hygiene | **Superseded** | Active race entries are empty, but removal exposed the still-live #39 race in F013; #38 is not fully proven. |
| F010 — checked tasks overstate completion | **Open** | OpenSpec honesty table above identifies current false checkboxes. |
| F011 — global `/wd4875` | **Resolved** | The disable moved off `legends_compile_options` to a scoped interface; incomplete consumer coverage is now F014. |
| F012 — fail-closed controls | **Resolved** | Exact TSan/Windows failures are visible; seed inversion is real; no verdict-path `allow_failure`, `continue-on-error`, or `|| true`. |

## 9. E-suite results

| ID | Status | Result |
|---|---|---|
| E1 | **PASS** | `origin/master` pinned to `42c30c46b88fc30891f7e6a25b629cd0808a5154`; last 15 commits listed below. |
| E2 | **FAIL** | Latest exact-SHA CI is completed **failure**, run 29437942535: <https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29437942535>. |
| E3 | **FAIL** | ASan/UBSan/Fuzz/Dependency/Linux gcc/Linux clang/C ABI success; TSan and Windows failure. Full job URLs are in the gate matrix. |
| E4 | **FAIL** | C++23 configure and build passed; ctest failed 1/4,512 with `WARNING` and `SUMMARY: ThreadSanitizer` at `CrashBreadcrumb` lines 57/100. Suppression file has no active race lines. |
| E5 | **PASS** | Exact ASan log: 100% tests passed, zero failures; no mass dual-stdlib mismatch or remaining leak report. |
| E6 | **PASS** | Clang 19.1.1, C++23 PASS, all targets link, `corpus/config` exists, five smoke and five 60-second targets complete without missing-directory errors. |
| E7 | **FAIL** | Pin/digest, generator check, six-component scan, config, and seed `rc=1` all work; production inventory truth fails because runtime FluidSynth is misversioned. |
| E8 | **PASS** | An anchored search for active `race:`, `deadlock:`, `mutex:`, or `thread:` entries returns no matches; only history comments contain `race:`. |
| E9 | **PASS** | `g_active_instance` is `static std::atomic<legends_instance*>` at `legends_embed_api.cpp:68` with acquire/release operations. |
| E10 | **FAIL** | Writer CAS exists, but non-atomic payload `memcpy` remains a real race; exact TSan proves it. Early reservation, wrap ordering, and `clear()` add further correctness defects. |
| E11 | **PASS (narrow static criterion)** | `/wd4875` is not global and exists only on `legends_gsl_msvc_options`. F014 separately records that a real gsl consumer is missing that interface. |
| E12 | **PASS (mechanical only)** | Exact CI `python3 scripts/generate_vendored_sbom.py --check` reports `OK ... (6 components)`; F015 explains why this does not establish semantic honesty. |
| E13 | **FAIL** | States match the alleged table (#38/#39/#45/#47/#48 closed; #40/#42/#43/#44 open), but #39's close claim is contradicted and #38 lacks the required green-TSan proof. |
| E14 | **FAIL** | Multiple `[x]` items are false or cite pre-residual evidence; see the 18-row honesty table. |
| E15 | **BLOCKED** | WSL has CMake 4.2.3 and g++-13, but no trusted exact-SHA sanitizer binary; configuring/building would violate the instruction to write only this report. Exact CI provides the decisive reproduction. |

### E1 commit log

```text
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
f5837e8 fix(r1): fuzz use g++-13; Windows named-pipe overlapped I/O (004/005)
1bf170b fix(fuzz): link libstdc++ with libc++ for libFuzzer ABI (FINDING-004)
```

### Adversarial probe results

| Probe | Result | Evidence |
|---|---|---|
| 1. Empty suppressions + green TSan | **FAIL** | File is empty of active entries, but exact TSan is red on #39. #38/#39 closeout is not proven. |
| 2. Seed-step false green | **PASS** | Step uses `set +e` only to capture scanner status, restores `set -e`, fails when `rc==0`, requires a non-empty output, and has no step-level continue-on-error. Exact seed `rc=1`. |
| 3. SBOM theater | **FAIL** | Count and pin checks prevent zero packages but accept a disconnected FluidSynth pin; the controls do not prove production identity. |
| 4. `llvm.sh` / latest binary | **PASS** | No active `curl | bash`, `llvm.sh`, or `releases/latest`; fuzz installs clang-19 by apt, scanner uses a tagged URL plus digest. |
| 5. Task honesty | **FAIL** | Tasks 1.1, 1.3, 1.5, 1.6, 3.1, 4.1, 4.2, 5.2, and 5.3 fail current evidence. |
| 6. #43 version honesty | **FAIL** | SBOM `2.3.5` does not match runtime `1.1.6-noglib`; the CMake tag is unused. |
| 7. Seqlock soundness | **FAIL** | Exact TSan proves torn concurrent payload access; pre-claim publication, delayed writers across wrap, and unsynchronized clear are not adequate for TSan or the C++ model. |

## 10. Verdict

```text
R1 MASTER CLOSEOUT: NO-GO
Mandatory lanes: FAIL
Residual TSan empty suppressions: FAIL
Dependency scan + seed proof: FAIL
Overall: The exact audited SHA is TSan/Windows red. The seed control passes,
but the production SBOM misidentifies the runtime FluidSynth component.
R1 is not closed on master.
```

## 11. What would flip NO-GO → GO

1. Reopen #39 and replace the `CrashBreadcrumb` payload protocol with a C++/TSan-race-free design; cover read/write, delayed multi-writer wrap, and concurrent clear; obtain a full green `thread Sanitizer` job with no race suppression.
2. Fix both exact Windows build failures: give every gsl-compiling target (including `legends_app`) the scoped C4875 policy and resolve C4324 without a global mute; obtain green build and tests.
3. Make the production SBOM identify `engine/src/libs/fluidsynth` as `1.1.6-noglib` (plus source provenance), keep #43 ignores issue-linked, and prove the scanner is evaluating the actual component while the seed still fails closed.
4. Reconcile #38/#39 states, `tsan-suppressions.txt`, the residual tracker, CI-THESIS, and every checked OpenSpec task with the new evidence.
5. Push the remediation and require one **completed** CI run where ASan, UBSan, TSan, Fuzz, Windows, Linux gcc/clang, C ABI, and the honest Dependency Scan all pass on the same new master SHA.
