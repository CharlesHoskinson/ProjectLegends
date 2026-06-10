---
type: source
aliases: ["Build CI Report"]
tags: [source, type/source, topic/audit]
created: 2026-06-09
updated: 2026-06-09
status: draft
title: Build & CI Audit (2026-06)
authors: [Claude audit fleet]
url:
publisher:
published: 2026
accessed: 2026-06-09
source_type: report
covers:
  - "[[Build & CI System (Project Legends)]]"
  - "[[Quality Gate Demotion (2026-06-08)]]"
  - "[[Licensing Inconsistency]]"
  - "[[IPC Runtime (Project Legends)]]"
  - "[[Engine Bridge (DOSBox-X)]]"
  - "[[Project Legends Test Suite]]"
  - "[[Documentation Drift]]"
  - "[[Project Legends Documentation Corpus]]"
  - "[[Prior-Audit Remediation Status]]"
---

# Build & CI Audit (2026-06)

## Summary

A 2026-06-09 build-system and CI audit of Project Legends (HEAD ef11f20) grading the infrastructure C: breadth A, enforcement D. The machinery is unusually complete — 4-sanitizer matrix, libFuzzer, 17 TLA+ steps, coverage gate, module-DAG checks, CPack packaging — but commit 6900e7a (2026-06-08) demoted nearly all of it to nightly/manual-only, the GPL-isolation guarantee has zero automated enforcement, and the tag-gated release pipeline has never run because the repository has no git tags.

## Key takeaways

- CI-01 (HIGH): commit 6900e7a (2026-06-08) gated sanitizers (ci.yml:333), static analysis (:431), fuzz (:474), TLA+ (:554), and dependency scan (:740) to schedule/dispatch only; per-PR/merge enforcement is now just Linux gcc/clang headless Release, Linux IPC Debug, Windows MSVC headless, abi-check, and report-only coverage — silently re-opening prior-audit fixes H7, H8, and M12.
- The fuzz job's "PR: Quick fuzz (30s per target)" step (ci.yml:503-513) is dead code: the job-level `if` at line 474 excludes pull_request events entirely.
- CI-02 (HIGH): GPL-2.0 process isolation has zero automated enforcement — cmake/VerifyGPLIsolation.cmake is never included by any CMakeLists, legends_verify_all_dags() (cmake/ModuleDAG.cmake:191-213) checks only legends_core/legends_pal/aibox_core while skipping legends_ipc, legends_proxy, and legends_engine_host, and REQ-ISO-016 is enforced by nothing but comments (CMakeLists.txt:361-362, :422-423).
- CI-03 (HIGH): the release pipeline has never executed once — `git tag -l` returns nothing, so the packaging job (ci.yml:767-771), CPack NSIS/DMG/TGZ generators (cmake/packaging.cmake:17-23), checksum script, and the 80% coverage gate in release-validation (ci.yml:844-888) are all unexercised; every build ships the "1.0.0+<hash>" fallback version (cmake/version.cmake:46).
- CI-04 (MEDIUM): PRs into develop bypass primary CI — ci.yml:22-23 and pal-ci.yml:13-14 restrict pull_request to main/master while RELEASING.md:5-10 routes feature PRs into develop, so breakage is discovered only after merge.
- CI-05 (MEDIUM): dependency scanning is a no-op — osv-scanner is fed cmake/dependencies.cmake as a "lockfile" and the failure swallowed by `|| true` (ci.yml:744-754) — yet roadmap.md:1470 lists REQ-SEC-028 as fully implemented and roadmap.md:3279 marks it Done.
- CI-06 (MEDIUM): no workflow uses ccache/sccache; the 1M-line vendored engine is rebuilt cold up to ~12 times per push across four overlapping workflows, against a 15-minute timeout on the main linux job (ci.yml:39).
- BUILD-01 (MEDIUM): all FetchContent pins are mutable git tags with no URL_HASH (cmake/dependencies.cmake:19-26), the GoogleTest pin is duplicated in engine/CMakeLists.txt:327-330, and pal-ci.yml:98 outright violates the pin by cloning SDL3 from upstream main on every src/pal/** push.
- BUILD-02 (MEDIUM): committed build logs (build_log.txt, build_output.txt, commit 1dd76b4) document the dev preset failing — "use of undeclared identifier 'gsl'" at src/app/cli_parser.cpp:102/:133 and src/app/ai_config.cpp:24 plus a link failure of legends_unit_tests.exe — on a Windows clang/Ninja toolchain no CI job covers.
- BUILD-03 (MEDIUM): CMakeLists.txt:165-167 FORCE-sets AIBOX_BUILD_TESTS ON regardless of LEGENDS_BUILD_TESTS, so even tests-off configs (module-dag.yml:107, packaging at ci.yml:803-814) fetch GoogleTest and compile the ~33k-line engine test suite, and embedders cannot turn engine tests off.
- BUILD-04 (LOW): -D_FORTIFY_SOURCE=2 is injected configuration-blind (CMakeLists.txt:89-91) including -O0 Debug builds, where glibc's #warning can escalate to a hard error under Tier A -Werror (:121).
- BUILD-05 (LOW): test targets get -Wno-error (CMakeLists.txt:811-813, :1006-1008) despite the "tests should be strict too" comment, the abi-check header-guard step (ci.yml:414-422) only echoes warnings and can never fail, and clang-tidy findings are unbounded with no baseline.
- TSan and MSan remain allow_failure: true (ci.yml:351-365) over known engine data races (g_active_instance, CrashBreadcrumb::add()); TSan signal has been muted since 2026-03-02 with no exit plan.
- Coverage gaps: Windows IPC mode (legends_engine_host/legends_proxy) is never built or tested on Windows; the nightly soak claim (ci.yml:11) is vapor — no workflow sets LEGENDS_SOAK_ENABLED and cmake/SoakTestLabels.cmake does not exist, so test-soak matches zero tests.
- Prior findings: L6 resolved, L7 resolved, L5 partially resolved — Windows SDL2 still cannot link (hardcoded mingw32/SDL2main at CMakeLists.txt:1189, no external/SDL2/ directory in the tree).

## Covers

- [[Build & CI System (Project Legends)]] — the audit's primary subject: broad machinery (sanitizers, fuzz, TLA+, DAG checks, packaging) with demoted enforcement, no compiler caching, develop-PR bypass, and tag-based mutable pins; grade C.
- [[Quality Gate Demotion (2026-06-08)]] — commit 6900e7a moved sanitizers, static analysis, fuzz, TLA+, and dependency scan to nightly/dispatch only, leaving a dead PR-fuzz step and a false ci.yml header.
- [[Licensing Inconsistency]] — the GPL-2.0 isolation promise rests on comments: VerifyGPLIsolation.cmake is orphaned, the module DAG skips all license-critical targets, and REQ-ISO-016 is verified by nothing.
- [[IPC Runtime (Project Legends)]] — CI builds IPC only as Linux gcc Debug headless; legends_engine_host/legends_proxy are never built or tested on Windows.
- [[Engine Bridge (DOSBox-X)]] — the vendored engine is rebuilt cold in every job, its fork version escapes dependency scanning, its test suite is force-built in all configs, and its known data races mute TSan.
- [[Project Legends Test Suite]] — test targets carry -Wno-error, the soak target matches zero tests, the multi-instance job duplicates the unit suite, and PR fuzzing is unreachable.
- [[Documentation Drift]] — ci.yml's own header, RELEASING.md, DEPENDENCIES.md ("hermetic"), and roadmap.md (REQ-SEC-028 "Done") all describe enforcement that no longer or never happens.
- [[Project Legends Documentation Corpus]] — RELEASING.md documents a never-performed release workflow; CIFix.md already diagnoses the four-workflow duplication this audit confirms.
- [[Prior-Audit Remediation Status]] — L6 and L7 resolved, L5 partially resolved (Windows SDL2 path still broken); H7/H8/M12 effectively re-opened by the gate demotion.
