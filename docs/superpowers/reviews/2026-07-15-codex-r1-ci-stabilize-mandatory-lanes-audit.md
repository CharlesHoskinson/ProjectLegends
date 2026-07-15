# 0. Independent audit — CI R1 stabilize mandatory lanes

| Field | Value |
|---|---|
| Date | 2026-07-15 |
| Auditor | Codex, independent senior security/correctness reviewer |
| Branch | `ci/r1-stabilize-mandatory-lanes` |
| Audited HEAD | `ba8cc8afe4302449c0a243c5959d54def43b1c7d` |
| Base | `master` at `22e0f291c5a5b7794b3d8266f8100f6db6747427` |
| Pull request | [PR #46](https://github.com/CharlesHoskinson/ProjectLegends/pull/46) |
| Scope | Adversarial review of the R1 diff, acceptance contract, live CI evidence, suppressions/baselines, dependency-scanner behavior, and governance controls. |

## 1. Executive summary

**Verdict: FAIL. Merge decision: NO-GO. R1 exit is not met.**

- The latest PR run fails all three mandatory sanitizer jobs: ASan has 193 failed tests, UBSan has two, and TSan reports a race in an intentional wrong-thread test that the new exclusion missed. Windows also fails one IPC test.
- The fuzz job still fails at build time because `fuzz_config_parser` cannot find `gsl-lite/gsl-lite.hpp`; the libc++ change fixed only the preceding configure failure.
- The dependency job is skipped on PRs, and the exact checked-in invocation with the workflow's mutable latest osv-scanner (v2.4.0) scans zero packages and exits 128.
- The strongest controls are real: TSan's absolute suppression path and symbolizer are present at runtime, `fail-fast: false` preserves sibling evidence, MSan has a tracked re-entry issue, and R1 gate mutes were removed.
- Several checked OpenSpec tasks nevertheless claim completion while their own verification text says pending or live CI disproves them.
- Finding counts: **0 Critical, 6 High, 4 Medium, 1 Low, 1 Informational.**

## 2. Dimension scorecard

| Dimension | Score (1–5) | Evidence |
|---|---:|---|
| Security | 2 | Known fluidsynth CVEs are issue-linked, but the scanner consumes no current package source and an unpinned downloaded executable is run without digest verification. |
| Correctness | 1 | The current ASan, UBSan, TSan, fuzz, and Windows jobs all fail on the audited SHA. |
| Maintainability | 2 | Issue links and central options help, but the suppression inventory is stale/ambiguous and the fuzz and warning fixes are incomplete or broad. |
| Documentation honesty | 2 | `CI-THESIS.md` and triage docs admit that green proof is pending, while six checked tasks overstate verified completion. |
| CI/CD integrity | 1 | Four R1 mandatory lanes and Windows are red; dependency scanning is not exercised on the PR and the current scheduled/dispatch invocation exits before producing a verdict. |
| Process/governance | 3 | The demotion rule is normative in OpenSpec and `CONTRIBUTING.md` with tracked exits, but completion bookkeeping was advanced ahead of evidence and enforcement still depends on review. |

## 3. Scope and method

The audit used the R1 design and tasks as the acceptance contract, reviewed `master...HEAD`, ran E1–E13, attempted E14, queried issues and PR checks with `gh`, and inspected current Actions job logs. It also executed the workflow's osv-scanner command under WSL using the SHA-256-verified current upstream Linux asset. No production, workflow, test, or audit-wiki file was modified.

Evidence sources:

- Current PR workflow run: [29423831242](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29423831242), audited head `ba8cc8a`.
- Superseded diagnostic runs: [29423049754](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29423049754), [29422640270](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29422640270).
- Dependency-scan history: [27304208837](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/27304208837) found the two fluidsynth CVEs; [27307862962](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/27307862962) passed after baselining under the scanner version resolved at that time.
- Local/static tools: Git, ripgrep, Python JSON parser, PowerShell, WSL Ubuntu 26.04, `gh` 2.96.0, and osv-scanner v2.4.0.
- Graph context was not used: `graphify-out/graph.json` is absent. The unrelated enrichment JSON was left untouched.
- E14 was attempted but is **BLOCKED** because the installed WSL distribution has neither `ctest` nor `cmake`.

## 4. Work under review

### Commits

| SHA | Subject |
|---|---|
| `b511005` | `ci(r1): stabilize mandatory sanitizer and dependency-scan lanes` |
| `e721855` | `ci(r1): fix TSan suppressions path and llvm-symbolizer on PATH` |
| `ba8cc8a` | `ci: fix Windows MSVC gsl-lite C4875 and Linux fuzz libc++` |

The directive listed two commits and 12 files, but the branch advanced during the audit. The actual audited diff contains 13 files, 415 insertions, and 51 deletions:

```text
M  .github/workflows/ci.yml
M  CI-THESIS.md
M  CMakeLists.txt
M  CMakePresets.json
M  CONTRIBUTING.md
A  docs/ci/2026-07-15-ci-audit-win-linux.md
A  docs/ci/r1-asan-fuzz-triage.md
A  docs/ci/r1-tsan-triage.md
M  openspec/changes/ci-stabilize-mandatory-lanes/tasks.md
A  osv-scanner.toml
M  tests/unit/test_contract_gates.cpp
M  tests/unit/test_thread_safety.cpp
A  tsan-suppressions.txt
```

### Intended R1 goals

The design requires: deterministic ASan/UBSan/fuzz green; an enforced TSan lane that suppresses only tracked known races; MSan retirement with a re-entry condition; an honest unmuted dependency scan; and a binding issue-plus-exit rule for every lane demotion (`design.md:9-14`). D1–D7 specify the implementation and evidence needed to reach those goals.

## 5. OpenSpec and design compliance matrix

### Decisions D1–D7

| Contract item | Status | Evidence |
|---|---|---|
| D1 — suppress known TSan families, exclude deliberate races, then enforce | **FAIL** | TSan is enforced, but [job 87380946377](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29423831242/job/87380946377) fails on `ThreadSafetyTest.ConcurrentDestroyAttempts`; `test_thread_safety.cpp:466-495` lacks the exclusion macro. |
| D2 — symbolizer is a hard dependency | **PASS** | Current log resolves `/usr/local/bin/llvm-symbolizer`; workflow installation is at `ci.yml:377-384`. |
| D3 — local/CI TSan agreement | **PARTIAL** | `CMakePresets.json` contains the source-root suppression path and parses, but local `ctest --preset tsan` is blocked on this host and no green/red-without-file comparison is recorded. |
| D4 — retire MSan with tracked re-entry | **PASS** | Matrix expands only address/undefined/thread; issue [#40](https://github.com/CharlesHoskinson/ProjectLegends/issues/40) states instrumented-runtime/dependency and nightly re-entry criteria. |
| D5 — fix dependency invocation before unmuting | **FAIL** | Mutes are gone, but v2.4.0 scans zero packages and exits 128 with the exact `ci.yml:812-815` command; no current green rehearsal exists. |
| D6 — ASan/UBSan/fuzz root cause or tracked quarantine to green | **FAIL** | Current ASan, UBSan, and fuzz jobs all fail; no per-root-cause issues or quarantines cover these failures. |
| D7 — demotion rule is a specification violation | **PASS** | The OpenSpec requirement uses SHALL/reject language at `spec.md:71-77`; contributor-facing MUST language and covered demotion types are at `CONTRIBUTING.md:227-241`. |

### Tasks 1.1–5.3

| Task | Checkbox | Audit status | Evidence |
|---|---:|---|---|
| 1.1 local TSan run and complete family triage | checked | **FAIL** | `tasks.md:4` says Windows could not run TSan; current CI found an omitted test family/path. |
| 1.2 one issue per race family with fix/remove exit | checked | **PARTIAL** | #38/#39/#45 exist, but #39 allows permanent “document-and-keep,” contrary to the task's fix-and-remove requirement. |
| 1.3 issue-linked narrow suppression file | checked | **PARTIAL** | File exists; `g_active_instance` is already atomic, and the second CrashBreadcrumb pattern is not itself immediately preceded by an issue URL. |
| 1.4 exclude every intentional wrong-thread test only in TSan | checked | **FAIL** | `ConcurrentDestroyAttempts` is not guarded and is the sole current TSan failure. |
| 1.5 wire suppression and symbolizer; verify zero reports | checked | **PARTIAL** | Runtime path/symbolizer are correct, but the thread job reports a race and there is no evidence that either checked-in suppression matched. |
| 1.6 preset parity; prove green with file/red without | checked | **PARTIAL** | Preset wiring/JSON are valid; the required local comparison is pending and E14 is blocked. |
| 1.7 remove allow-failure and seed/revert a race | checked | **PARTIAL** | Mute removed and a real race fails closed, but the prescribed seed/revert verification is absent. |
| 2.1 file MSan re-entry issue | checked | **PASS** | #40 has concrete runtime, dependency-surface, placement, and green-run criteria. |
| 2.2 remove memory matrix entry | checked | **PASS** | E5 and the current matrix show only address/undefined/thread; the workflow references #40. |
| 3.1 reproduce ASan/UBSan and issue each root cause | unchecked | **FAIL** | Current failures are reproducible in CI but remain untriaged and untracked. |
| 3.2 fix/quarantine ASan/UBSan to green | unchecked | **FAIL** | Both jobs are red; no new issue-linked `DISABLED_` quarantine is present. |
| 3.3 reproduce/fix fuzz smoke failures | unchecked | **FAIL** | Fuzz still fails during `fuzz-all` build before smoke execution. |
| 4.1 supported recursive scan with JSON artifact | checked | **FAIL** | CLI syntax is accepted, but the installed latest scanner finds no sources and exits 128 before the artifact assertion. |
| 4.2 triage honest first-run results | checked | **PARTIAL** | #43 tracks two detected CVEs; #42 concedes that manifest/SBOM coverage is absent. |
| 4.3 unmute alongside green/seeded rehearsal | checked | **FAIL** | Mutes/name were changed, but the required current green dispatch and seeded-vulnerable proof are absent. |
| 5.1 contributor-facing demotion rule | checked | **PASS** | `CONTRIBUTING.md:227-241` and `spec.md:71-77` provide normative requirements and rejection behavior. |
| 5.2 end-to-end green verification | unchecked | **FAIL** | Address, undefined, thread, and fuzz are red; dependency-scan is skipped on PRs and locally exits 128. |
| 5.3 update wiki/thesis after green | unchecked | **BLOCKED** | `CI-THESIS.md:30` honestly records “still required”; the read-only wiki must not be stamped until 5.2 passes. |

## 6. Findings

### FINDING-001 — [HIGH] AddressSanitizer remains massively red and untriaged

| Field | Value |
|---|---|
| Severity | High |
| Category | Correctness / CI integrity |
| Location | `address Sanitizer` job; `engine/src/misc/dosbox_context.cpp:39,1170`; exception paths including `engine/include/aibox/exceptions.h:29-32` |
| Evidence | E10; [job 87380946422](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29423831242/job/87380946422): “96% tests passed, 193 tests failed out of 4511,” exit 8. Logs contain 191 `alloc-dealloc-mismatch` reports plus 16,842,752-byte leaks in each of `DOSBoxContextTest.MoveConstruction` and `.MoveAssignment`. |
| Impact | R1's mandatory ASan gate cannot pass and memory-management defects or ABI/allocation mismatches remain unresolved across a large test surface. |
| Recommendation | Open one issue per root cause, isolate whether the 191 failures share an allocator/runtime boundary, fix the two context ownership leaks, and rerun the exact address leg. Use issue-linked quarantine only where D6 permits it; do not disable allocator mismatch detection globally. |
| Residual risk | Even after common-root fixes, rerun all 4,511 tests because the current failure cascade can hide later independent ASan defects. |
| Status | Open |

### FINDING-002 — [HIGH] UndefinedBehaviorSanitizer exposes two invalid-enum tests

| Field | Value |
|---|---|
| Severity | High |
| Category | Correctness / CI integrity |
| Location | `engine/src/misc/error_model.cpp:109`; `engine/src/misc/logging.cpp:62` |
| Evidence | E10; [job 87380946408](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29423831242/job/87380946408): value `99999` is invalid for `dosbox_error_code`, value `99` is invalid for `dosbox_log_level`; 2/4511 tests fail, exit 8. |
| Impact | The mandatory UBSan lane is red, and tests intended to validate unknown values invoke undefined behavior before the fallback logic can be trusted. |
| Recommendation | Change the boundary to accept/validate an integer representation before converting to the enum, or redesign the tests/API so unknown external values are represented legally; create a root-cause issue and retain assertions. |
| Residual risk | Other unchecked integer-to-enum boundaries may exist; search and add boundary-focused UBSan coverage after these two are corrected. |
| Status | Open |

### FINDING-003 — [HIGH] TSan exclusion misses `ConcurrentDestroyAttempts`

| Field | Value |
|---|---|
| Severity | High |
| Category | Correctness / CI integrity |
| Location | `tests/unit/test_thread_safety.cpp:466-495`; `src/legends/legends_embed_api.cpp:979` |
| Evidence | E6 and [job 87380946377](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29423831242/job/87380946377): the test has no `LEGENDS_SKIP_INTENTIONAL_WRONG_THREAD()` call; TSan reports concurrent writes through `legends_destroy`, then 1/4511 fails with exit 8. |
| Impact | Task 1.4 is false, the enforced TSan lane is red, and the exclusion inventory does not cover the deliberate wrong-thread family it claims to cover. |
| Recommendation | Prefer making the wrong-thread reject path synchronization-safe. If #45's temporary exclusion is used, add this exact test to the narrowly scoped guard/label, prove all non-TSan lanes still execute it, and never add a suppression for `legends_destroy`. |
| Residual risk | Skipping the test under TSan removes race coverage for its body; issue #45 must remain open until the reject path itself becomes TSan-clean. |
| Status | Open |

### FINDING-004 — [HIGH] Fuzz fix is partial; `fuzz_config_parser` lacks the gsl-lite dependency

| Field | Value |
|---|---|
| Severity | High |
| Category | Correctness / CI integrity |
| Location | `tests/fuzz/CMakeLists.txt:224-247`; `include/legends/gsl.hpp:31` |
| Evidence | E10; [job 87382692244](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29423831242/job/87382692244): configure succeeds with libc++, then compilation of `src/app/config_parser.cpp` fails because `gsl-lite/gsl-lite.hpp` is not found. |
| Impact | The mandatory fuzz job never builds all targets, so none of the intended smoke executions establishes crash resistance. |
| Recommendation | Give `fuzz_config_parser` an explicit target dependency that supplies gsl-lite's include/config contract (rather than relying on `legends_core`'s PRIVATE dependency), then build `fuzz-all`, generate the corpus, and run every smoke command. |
| Residual risk | A green build is not a green fuzz lane; corpus generation and each 30-second target still need runtime evidence. |
| Status | Open |

### FINDING-005 — [HIGH] Windows remains red after the C4875 build mitigation

| Field | Value |
|---|---|
| Severity | High |
| Category | Correctness / CI integrity |
| Location | `tests/unit/test_ipc_control_channel.cpp:36-70`; `Windows (MSVC)` job |
| Evidence | E10; [job 87380946056](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29423831242/job/87380946056): build completes, then `IpcControlChannelTest.BidirectionalSendRecv` fails at line 67 because the client receives no `HandshakeAck`; 1/4500 tests fails, exit 1. No matching open issue was found. |
| Impact | The required Windows baseline remains red after the C4875 build mitigation, so PR #46 is not mergeable even independently of the R1 sanitizer/fuzz failures. |
| Recommendation | Reproduce the named-pipe request/response timing on Windows, file a root-cause issue, and fix the synchronization/protocol lifetime. If it is demonstrably flaky, use the project's tracked quarantine policy rather than retrying or deleting the assertion. |
| Residual risk | A one-run failure does not distinguish deterministic protocol breakage from timing sensitivity; repeated Windows runs and a stress test are required. |
| Status | Needs CI re-run |

### FINDING-006 — [HIGH] Current dependency-scan invocation deterministically exits 128 with zero package sources

| Field | Value |
|---|---|
| Severity | High |
| Category | CI integrity / Security |
| Location | `.github/workflows/ci.yml:805-828` (`Dependency Scan`) |
| Evidence | Supplemental reproduction using the workflow-resolved v2.4.0 binary and exact first command: ten vendored directories each report “found 0 packages,” followed by “No package sources found” and `OSV_RC=128`. `set -euo pipefail` stops before `test -s`. The current PR job is skipped by `ci.yml:795`. |
| Impact | Scheduled/dispatch runs using today's `latest` cannot reach a vulnerability verdict or green baseline; task 4.1/4.3 and D5 are not satisfied. |
| Recommendation | Generate a deterministic SBOM and scan it with the pinned CLI, or otherwise provide a supported package source; rehearse a baseline and a seeded known-vulnerable entry using the exact committed workflow before claiming unmute completion. Do not paper over exit 128 with `|| true`. |
| Residual risk | Detector behavior can drift again unless the scanner and input format are versioned together and covered by a seeded failure test. |
| Status | Open |

### FINDING-007 — [MEDIUM] Dependency coverage excludes FetchContent and most C++ dependency metadata

| Field | Value |
|---|---|
| Severity | Medium |
| Category | Security / Supply chain |
| Location | `.github/workflows/ci.yml:812-825`; `cmake/dependencies.cmake`; issue #42 |
| Evidence | [Issue #42](https://github.com/CharlesHoskinson/ProjectLegends/issues/42) states that the trees have no parseable package sources and calls for an SBOM covering gsl-lite, SDL, GoogleTest, benchmark, curl, fluidsynth, mt32emu, and the engine. The v2.4.0 reproduction confirms zero packages. |
| Impact | Even if exit handling were made green, a no-source result could be mistaken for “no vulnerabilities,” leaving meaningful dependency versions outside the verdict. |
| Recommendation | Produce checked/reproducible CycloneDX or SPDX from pinned CMake/vendored inputs, scan that artifact, assert a nonzero expected inventory, and seed a vulnerable component in a test fixture. |
| Residual risk | Source-to-package mapping for patched vendored snapshots remains imperfect and needs documented manual review. |
| Status | Open |

### FINDING-008 — [MEDIUM] CI executes a mutable, unverified `latest` scanner binary

| Field | Value |
|---|---|
| Severity | Medium |
| Category | Supply chain / Security |
| Location | `.github/workflows/ci.yml:799-803` |
| Evidence | The job downloads `releases/latest/download/osv-scanner_linux_amd64`, applies `chmod +x`, and executes it without a tag, checksum, or signature check. On 2026-07-15 latest is v2.4.0 with upstream asset digest `15314940c10d26af9c6649f150b8a47c1262e8fc7e17b1d1029b0e479e8ed8a0`. |
| Impact | Upstream release drift already changed behavior; compromise or replacement of the mutable asset would execute code in the Actions runner and make results non-reproducible. |
| Recommendation | Pin the release version and expected SHA-256 (or use a digest-pinned trusted action/package), use `curl --fail --location --show-error`, verify before chmod/execute, and update by reviewed PR. |
| Residual risk | A pinned upstream binary still inherits upstream build/provenance risk; record its source/release provenance and minimize token permissions. |
| Status | Open |

### FINDING-009 — [MEDIUM] TSan suppression inventory does not meet its own hygiene/exit contract

| Field | Value |
|---|---|
| Severity | Medium |
| Category | Correctness / Process |
| Location | `tsan-suppressions.txt:5,13-21`; `src/legends/legends_embed_api.cpp:68`; issues #38/#39 |
| Evidence | E7: `race:g_active_instance` remains despite the symbol being `std::atomic`; two CrashBreadcrumb patterns cover the same family, but the second is not immediately preceded by an issue URL. #39 permits permanent “document-and-keep” rather than task 1.2's fix-and-remove exit. Current logs prove configuration, not that either entry matched. |
| Impact | Stale or duplicate patterns increase the chance of masking a future race and make suppression burndown unverifiable. |
| Recommendation | Remove/refine #38 from actual observed stacks, reduce aliases to the narrowest proven matcher, directly annotate every entry, amend #39 to a measurable fix/removal criterion, and capture TSan suppression-count evidence. |
| Residual risk | Symbol-based suppressions can broaden after refactors; review their match counts on every toolchain update. |
| Status | Open |

### FINDING-010 — [MEDIUM] Checked tasks overstate completion before required verification

| Field | Value |
|---|---|
| Severity | Medium |
| Category | Docs honesty / Process |
| Location | `openspec/changes/ci-stabilize-mandatory-lanes/tasks.md:3-15,32-36` |
| Evidence | E13/contract review: 1.1 is checked although no local TSan run occurred; 1.5, 1.6, 1.7, and 4.3 are checked while their own notes say verification is pending; 1.4 is checked but current TSan disproves completeness. |
| Impact | Reviewers can treat implementation wiring as accepted behavior, obscuring the exact work still required for R1 exit. |
| Recommendation | Uncheck any task whose stated verification has not passed, attach run/job URLs beside completed verification, and separate “wiring landed” subtasks from behavioral acceptance if partial progress must be recorded. |
| Residual risk | Checkboxes remain manually maintained; release/merge review must reconcile them with live required evidence. |
| Status | Open |

### FINDING-011 — [LOW] `/wd4875` is applied globally rather than at the gsl-lite boundary

| Field | Value |
|---|---|
| Severity | Low |
| Category | Maintainability |
| Location | `CMakeLists.txt:97-103` |
| Evidence | The suppression is added to the shared `legends_compile_options` interface and therefore reaches first-party targets, although the documented warning originates in pinned gsl-lite. Issue [#44](https://github.com/CharlesHoskinson/ProjectLegends/issues/44) provides a removal criterion. |
| Impact | A future C4875 in project code could be hidden until the global switch is removed. |
| Recommendation | Scope the warning disable to the imported/third-party include boundary if CMake/MSVC permits; otherwise retain #44, add a focused comment/test, and remove the switch with the pin upgrade. |
| Residual risk | Toolchain warning changes can still require a temporary exception; keep exceptions code-specific and time-bounded. |
| Status | Mitigated |

### FINDING-012 — [INFORMATIONAL] Several fail-closed controls are correctly active

| Field | Value |
|---|---|
| Severity | Informational |
| Category | CI integrity |
| Location | `.github/workflows/ci.yml:29-30,340,377-412,788-835` |
| Evidence | E5/E13/current logs: workflow token permissions are `contents: read`; sanitizer `fail-fast: false`; no sanitizer `allow_failure`/`continue-on-error`; TSan has an absolute suppression path and symbolizer; dependency scanner invocations are not muted. Remaining `|| true` at lines 438 and 970 serves a warning-only header probe and diagnostic artifact listing, not an R1 gate verdict. |
| Impact | Failures are visible and sibling sanitizer jobs complete, enabling the concrete evidence in this audit. |
| Recommendation | Preserve these controls while fixing root causes; do not restore mutes to manufacture green. |
| Residual risk | Enforcement is not merge-binding until the separately scoped R2 ruleset is active. |
| Status | Mitigated |

## 7. CI evidence

Current run: [29423831242](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29423831242), head `ba8cc8a`, overall **FAILURE**.

| Job | Conclusion at audit capture | URL | Notes |
|---|---|---|---|
| Linux (gcc) | SUCCESS | [job 87380946140](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29423831242/job/87380946140) | Required baseline green. |
| Linux (clang) | SUCCESS | [job 87380946175](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29423831242/job/87380946175) | Required baseline green. |
| Linux IPC (gcc) | SUCCESS | [job 87380946231](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29423831242/job/87380946231) | Required baseline green. |
| Windows (MSVC) | FAILURE | [job 87380946056](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29423831242/job/87380946056) | Build completed; `IpcControlChannelTest.BidirectionalSendRecv` failed, 1/4500, exit 1. |
| address Sanitizer | FAILURE | [job 87380946422](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29423831242/job/87380946422) | 193/4511 failed; 191 allocator mismatch reports plus two leaks. |
| undefined Sanitizer | FAILURE | [job 87380946408](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29423831242/job/87380946408) | Two invalid-enum tests, exit 8. |
| thread Sanitizer | FAILURE | [job 87380946377](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29423831242/job/87380946377) | One unsuppressed race in `ConcurrentDestroyAttempts`, exit 8. |
| Fuzz Testing | FAILURE | [job 87382692244](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29423831242/job/87382692244) | Configure fixed; `fuzz-all` build fails missing gsl-lite header. |
| Dependency Scan | SKIPPED | [job 87380946893](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29423831242/job/87380946893) | Expected on PR trigger, so it supplies no current acceptance evidence. Exact v2.4.0 local invocation exits 128. |

Historical dependency green is not current proof: run 27307862962 resolved a different `latest` binary at execution time. The current mutable endpoint resolves v2.4.0 and behaves differently.

## 8. Suppression and baseline inventory

### TSan suppressions

| Entry | Tracking issue | Current evidence | Exit-criterion quality | Audit result |
|---|---|---|---|---|
| `race:g_active_instance` | [#38](https://github.com/CharlesHoskinson/ProjectLegends/issues/38) | Named symbol is now atomic; no current match count | Removal in same PR after fix/clean enforced run is measurable | **Stale until an observed stack proves otherwise** |
| `race:CrashBreadcrumb::add` | [#39](https://github.com/CharlesHoskinson/ProjectLegends/issues/39) | Source has relaxed index plus non-atomic slot writes/read; no current match count | Allows fix or permanent documentation | **Real family, weak exit** |
| `race:legends::CrashBreadcrumb::add` | [#39](https://github.com/CharlesHoskinson/ProjectLegends/issues/39) | Namespace alias for same family; not directly issue-preceded | Same weak exit; duplicate necessity unproven | **Hygiene failure / refine** |
| TSan-only wrong-thread skips | [#45](https://github.com/CharlesHoskinson/ProjectLegends/issues/45) | 15 tests skip, but `ConcurrentDestroyAttempts` does not | Remove skip when reject path is clean or move to dedicated label | **Incomplete inventory** |

### osv-scanner baseline

| Ignore | Tracking issue | Rationale | Exit-criterion quality | Audit result |
|---|---|---|---|---|
| `CVE-2021-21417` | [#43](https://github.com/CharlesHoskinson/ProjectLegends/issues/43) | Vendored fluidsynth UAF in SoundFont loading | Upgrade/patch/remove vendored copy and delete ignore in same PR | **Good, but scanner currently cannot rediscover it** |
| `CVE-2025-56225` | [#43](https://github.com/CharlesHoskinson/ProjectLegends/issues/43) | Vendored fluidsynth vulnerability | Same concrete removal criterion | **Good, but scanner currently cannot rediscover it** |

Issue [#42](https://github.com/CharlesHoskinson/ProjectLegends/issues/42) correctly tracks the missing SBOM and seeded-failure proof. It is a coverage gap, not an ignore entry.

## 9. Security and supply-chain notes

- **Scanner trust:** `curl -sL` follows a mutable latest URL, does not fail explicitly on HTTP errors, and verifies neither digest nor signature before execution. The workflow's read-only token limits repository mutation, but does not make arbitrary runner code acceptable or results reproducible.
- **Scanner input:** a recursive source-tree walk is not a dependency inventory. The current tool finds zero packages, while CMake FetchContent and vendored snapshots remain real supply-chain inputs.
- **Known CVEs:** both fluidsynth ignores are narrowly identified, issue-linked, and have same-PR deletion criteria. They should remain visible in reports/SBOM even while accepted.
- **Suppression abuse:** TSan does fail on a new unsuppressed race, which is desirable. The stale and duplicate entries still need match-count evidence to show they cannot hide unrelated future reports.
- **Mute search:** no R1 sanitizer or dependency-scanner verdict is swallowed by `allow_failure`, `continue-on-error`, or `|| true`. The two `|| true` remnants are outside these verdict paths and are documented in FINDING-012.
- **Privileges/secrets:** top-level `permissions: contents: read` is appropriate. No new secret is printed; the absolute workspace path in `TSAN_OPTIONS` is non-secret.

## 10. Documentation honesty review

| Document | Assessment | Evidence |
|---|---|---|
| `CONTRIBUTING.md` | Mostly honest | Describes enforced rather than green TSan, names MSan retirement/#40, and states a normative demotion rule. It should not be read as evidence that current lanes pass. |
| `CI-THESIS.md` | Honest | Line 30 explicitly says green address/undefined/thread/fuzz and dependency evidence are still required. |
| `docs/ci/r1-tsan-triage.md` | Transparent but incomplete | Admits local TSan could not run; its design-derived family list missed the current `ConcurrentDestroyAttempts` path. |
| `docs/ci/r1-asan-fuzz-triage.md` | Honest placeholder, now stale | Lines 26-31 say first evidence is pending; current logs now provide concrete ASan/UBSan/fuzz roots that must replace placeholders. |
| `docs/ci/2026-07-15-ci-audit-win-linux.md` | Cautious, but fuzz diagnosis was partial | Checklist remains unchecked; libc++ fixed configure, not the later gsl-lite build failure. |
| `tasks.md` | Not reliable as acceptance status | Six checked items lack their required proof or are disproved; see FINDING-010 and the task matrix. |
| audit-wiki | Correctly left unchanged | Task 5.3 is gated on sustained green and the directive makes this evidence tree read-only. |

## 11. Recommendations

### Fix now

1. **R1/thread owner:** fix or narrowly exclude `ThreadSafetyTest.ConcurrentDestroyAttempts` under #45; prove the non-TSan suite still runs it.
2. **Sanitizer owners:** open root-cause issues for the ASan allocator mismatch, DOSBox context leaks, and the two UBSan enum boundaries; fix without globally weakening sanitizers.
3. **Fuzz/CMake owner:** make `fuzz_config_parser` explicitly consume the gsl-lite target/include contract; run the full build, corpus generator, and smoke set.
4. **Windows/IPC owner:** reproduce and issue-track `IpcControlChannelTest.BidirectionalSendRecv`; fix or apply only the policy-compliant tracked quarantine supported by repeat evidence.
5. **Security/CI owner:** pin and verify osv-scanner, generate/consume an SBOM, assert a nonempty inventory, and prove both clean and seeded-vulnerable outcomes.

### Fix before merge

1. Run one current `workflow_dispatch` with address, undefined, thread, fuzz, and Windows green and no memory job.
2. Run dependency-scan on the pinned tool/input and record a green dispatch/nightly plus a failing seeded rehearsal.
3. Refine/remove stale TSan entries, capture suppression match counts, and make #39's exit criterion require a measurable code fix/removal decision.
4. Reconcile every task checkbox with job URLs and actual verification; update triage documents with the current roots.
5. Re-run `gh pr checks 46` after the remediation SHA and require zero pending/failed mandatory R1 jobs.

### Fix after R1

1. Burn down #38/#39/#45 rather than expanding suppressions.
2. Patch/upgrade fluidsynth and remove both #43 ignores in the same PR.
3. Upgrade gsl-lite, remove `/wd4875`, and prove Windows green under #44.

### Defer to R2+

Activate branch protection/rulesets only after R1 is actually green, then bind the exact stable required-check names to merging. Corpus persistence and broader preset/coverage work remain in their already sequenced later rounds.

## 12. Residual risk and merge decision

**NO-GO for merging PR #46 at audited SHA `ba8cc8a`.** Four lanes that define R1 completion are red, Windows is also red, dependency scanning has neither current execution nor a functioning current input path, and task status overstates verification. Merging would establish enforced red lanes, not deterministic green gates.

After the High findings are fixed, residual risk remains in accepted TSan families, two baselined fluidsynth CVEs, incomplete dependency-to-package mapping, and the temporary MSVC warning suppression. Those risks are acceptable only with their issues open, precise exit criteria intact, a green current dispatch, and a failing seeded regression demonstration for TSan/dependency scanning. R2 merge binding must wait for that evidence.

## 13. Appendix

### Mandatory command transcript summary

| ID | Exit/status | Relevant excerpt |
|---|---|---|
| E1 | 0 | HEAD `ba8cc8afe4302449c0a243c5959d54def43b1c7d`; branch tracks origin; only pre-existing untracked audit prompt present. |
| E2 | 0 | Three commits: `ba8cc8a`, `e721855`, `b511005`. |
| E3 | 0 | 13 files; 415 insertions, 51 deletions. |
| E4 | 0 | Sanitizer mutes removed; matrix address/undefined/thread; `fail-fast: false`; absolute TSan path/symbolizer; fuzz libc++; unmuted recursive OSV scan. |
| E5 | 0 | No active `allow_failure`/`continue-on-error`; `|| true` remains only at lines 438 and 970; OSV/TSan locations enumerated. |
| E6 | 0 | TSan macro definitions/calls found; `LEGENDS_TSAN_BUILD` definition at `CMakeLists.txt:822`; no macro at `test_thread_safety.cpp:466`. |
| E7 | 0 | Three TSan patterns, issues #38/#39. |
| E8 | 0 | Two `[[IgnoredVulns]]` entries for #43. |
| E9 | 0 | `presets ok`. |
| E10 | 1 | Current checks fail address, undefined, thread, fuzz, and Windows; dependency scan is skipped. |
| E11 | 0 | PR #46 open at `ba8cc8a`; 13-file diff; current check rollup captured. |
| E12 | 0 | #38/#39/#40/#45/#43 are open; supplemental #42/#44 queries are also open. |
| E13 | 0 | Dependency and thread lanes are not named optional or muted; CI thesis explicitly withholds R1 exit. |
| E14 | **BLOCKED** | `wsl -d Ubuntu-26.04 -- bash -lc 'ctest --preset tsan'` cannot run: `ctest: command not found`; `cmake` is also absent. |

### Additional reproducible evidence

```text
osv-scanner version: v2.4.0 (latest on 2026-07-15)
upstream asset SHA-256: 15314940c10d26af9c6649f150b8a47c1262e8fc7e17b1d1029b0e479e8ed8a0
local verified SHA-256: 15314940c10d26af9c6649f150b8a47c1262e8fc7e17b1d1029b0e479e8ed8a0
command: osv-scanner -r engine/ --config osv-scanner.toml --format json --output /tmp/r1-osv-engine.json
result: 10 Extract calls, each 0 packages; "No package sources found"; OSV_RC=128
```

```text
Current TSan runtime evidence:
/usr/local/bin/llvm-symbolizer
TSAN_OPTIONS=halt_on_error=1:second_deadlock_stack=1:suppressions=/home/runner/work/ProjectLegends/ProjectLegends/tsan-suppressions.txt
SUMMARY: ThreadSanitizer: data race ... in memmove
99% tests passed, 1 tests failed out of 4511
```

### Key file citations

- `.github/workflows/ci.yml:29-30,333-412,438,788-835,970`
- `CMakeLists.txt:97-103,817-822`
- `CMakePresets.json` test preset `tsan`
- `tests/unit/test_thread_safety.cpp:24-30,466-495`
- `tests/fuzz/CMakeLists.txt:224-247`
- `tsan-suppressions.txt:1-21`
- `osv-scanner.toml:1-12`
- `CONTRIBUTING.md:218-243`
- `CI-THESIS.md:28-30`
- `openspec/changes/ci-stabilize-mandatory-lanes/design.md:24-43`
- `openspec/changes/ci-stabilize-mandatory-lanes/tasks.md:3-43`
- `openspec/changes/ci-stabilize-mandatory-lanes/specs/ci-stabilization/spec.md:19-77`

### Tracking issues

- [#38 — TSan engine global-state family](https://github.com/CharlesHoskinson/ProjectLegends/issues/38)
- [#39 — CrashBreadcrumb race](https://github.com/CharlesHoskinson/ProjectLegends/issues/39)
- [#40 — MSan re-entry](https://github.com/CharlesHoskinson/ProjectLegends/issues/40)
- [#42 — dependency SBOM gap](https://github.com/CharlesHoskinson/ProjectLegends/issues/42)
- [#43 — fluidsynth CVEs](https://github.com/CharlesHoskinson/ProjectLegends/issues/43)
- [#44 — remove `/wd4875`](https://github.com/CharlesHoskinson/ProjectLegends/issues/44)
- [#45 — TSan wrong-thread exclusions](https://github.com/CharlesHoskinson/ProjectLegends/issues/45)
