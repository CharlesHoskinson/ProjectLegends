---
type: source
aliases: ["Test Coverage Report"]
tags: [source, type/source, topic/audit]
created: 2026-06-09
updated: 2026-06-09
status: draft
title: Test Coverage Audit (2026-06)
authors: [Claude audit fleet]
url:
publisher:
published: 2026
accessed: 2026-06-09
source_type: report
covers:
  - "[[Project Legends Test Suite]]"
  - "[[Build & CI System (Project Legends)]]"
  - "[[Quality Gate Demotion (2026-06-08)]]"
  - "[[Determinism Oracle Weakness]]"
  - "[[IPC Trust Boundary Gaps]]"
  - "[[IPC Runtime (Project Legends)]]"
  - "[[Legends C API Layer]]"
  - "[[Engine Bridge (DOSBox-X)]]"
  - "[[Save-State Load Path Overflow]]"
  - "[[Prior-Audit Remediation Status]]"
  - "[[Documentation Drift]]"
---

# Test Coverage Audit (2026-06)

## Summary

Tests, fuzzing, and benchmarks audit of Project Legends (2026-06-09, baseline AUDIT.md 2026-02-24), covering 176 files under tests/, 82 under engine/tests/, benchmarks/, and the CI workflows. Health grade C: the suite is large and much of it real (~2,788 TEST macros under tests/ plus ~1,878 under engine/tests/), but it is wide and under-enforced, with weak oracles at exactly the points the product claims matter most — determinism, save/load, and the IPC trust boundary.

## Key takeaways

- HIGH (test-ci-01): commit 6900e7a "Stabilize CI and RuntimeHost adoption" (2026-06-08, one day before the audit) demoted all four sanitizers, fuzzing, TLA+ model checking, static analysis, and the macOS/SDL3 jobs to nightly/manual-only (ci.yml:333, 474, 554, 431, 136-301); the merge gate is now just Linux+Windows headless build-and-test, so a memory-safety regression, UB, fuzz crash, or TLA+ invariant violation can merge and sit up to 24h undetected.
- HIGH (test-oracle-02): every determinism and save/load roundtrip test asserts on the Fast-mode state hash, which excludes guest RAM, CPU GPRs/EIP/segment registers, and VRAM — dosbox_library.cpp:684 hard-codes HashMode::Fast, CpuState::hash_into covers only cycle counters/flags (dosbox_context.cpp:103-118), and nothing in production or tests ever uses Full mode; two runs diverging in RAM or registers would still "prove" determinism.
- HIGH (test-stub-03): 8 of 33 registered integration test files — including test_replay_determinism.cpp and test_save_state_compat.cpp, the headline product promises — are two-line GTEST_SKIP "Not yet implemented" stubs that register as green in every CI run (CMakeLists.txt:941-979).
- HIGH (test-ipc-04): the IPC/process-isolation path has no enabled end-to-end test — the only true cross-process test is DISABLED_FullE2E (test_ipc_integration.cpp:42); the dispatcher has direct tests for 8 of 43 MsgType cases; the proxy is tested only for not-connected errors; the linux-ipc CI job re-runs in-process tests because legends_unit_tests links legends_core, not legends_proxy (CMakeLists.txt:779-781); runtime_host.cpp (655 lines, 32 methods) has no direct unit test.
- HIGH (test-fuzz-05): the save-state fuzzers die at the CRC32 wall — legends_embed_api.cpp:2072-2073 rejects before any section parsing and the custom mutator never recomputes the checksum, so the deep deserialization paths flagged as H9 are effectively unfuzzed; no IPC fuzz target exists at all; budget is 30-60s per target, nightly-only, with no persisted corpus.
- MEDIUM (test-weak-07): assertion-free "no crash" tests persist (test_negative.cpp:74-139, test_legends_embed.cpp:709-726) even though the strict get_instance fix (legends_embed_api.cpp:79-82) makes exact LEGENDS_ERR_NULL_HANDLE assertions possible — a regression of H5 would not be caught.
- MEDIUM (test-api-08): legends_set_ttf_font has zero test references; 15 device APIs (PC-98, Glide, printer, IPX, MIDI) are tested only for null-handle rejection (test_phase3_bridge.cpp:16-124); mount/video-capture/event-callback paths skip in headless builds and every CI job sets -DLEGENDS_HEADLESS=ON — roughly a third of the public ABI has no behavioral verification anywhere.
- MEDIUM (test-headless-09): SDL backend tests run only via path-filtered/nightly pal-ci.yml, and commit 911692f "Relax SDL backend startup event tests" deleted the post-init event-count assertion outright (test_pal_sdl2_backend.cpp:141-144, test_pal_sdl3_backend.cpp:144-147) instead of filtering event types — the suppress-rather-than-fix pattern in miniature.
- MEDIUM (test-soak-10 / test-bench-11): the soak suite can never run (no workflow sets LEGENDS_SOAK_ENABLED/LEGENDS_SOAK_SHORT; cmake/SoakTestLabels.cmake does not exist), and the three benchmark files are never built or run anywhere — no performance regression tracking despite bench_ipc_overhead.cpp existing precisely to measure the IPC hop.
- MEDIUM (test-cov-13): coverage is report-only on the per-push job (ci.yml:716, added in 6900e7a); the only enforced threshold is 80% on src/app/ at release-tag time (ci.yml:879-888), leaving src/legends/, src/legends_ipc/, src/legends_proxy/, src/engine_host/, and src/pal/ outside every enforced gate.
- LOW (test-dead-12): 3 integration tests are uncompilable orphans calling a nonexistent legends_init; 6 engine test files are unregistered in engine/tests/CMakeLists.txt — including test_serialization_completeness.cpp, which pins the H1 keyboard-buffer gap but is never built; the counter/graphics/input.com fixtures are referenced only by a README.
- LOW (test-readme-14): the README "tests: 1500+ passing" badge (README.md:8) is a hardcoded static shields.io badge; "passing" silently includes 65+ GTEST_SKIP sites, the 8 stubs, the never-run soak suite, and the DISABLED_ E2E. The ci.yml header comment and AUDIT.md §3's CI table are likewise inaccurate post-6900e7a.
- Prior-audit verification: L8 (sentinel destroy masking H5) is RESOLVED with a proper negative-case test (test_legends_embed_lifecycle.cpp:206-215) and the underlying H5 fallback removed; H7 is PARTIALLY RESOLVED (Full mode now hashes guest RAM at state_hash.cpp:300-305 but nothing calls it); all four prior test-gap rows (real COM/EXE execution, >200K-cycle determinism, graphics-mode determinism, multi-process determinism) remain open.
- Genuinely good: boot-to-prompt is a real end-to-end test (test_boot_to_prompt.cpp); save-state security tests assert exact error codes for corrupted offsets/geometry/truncation; shared-fixture hygiene and per-test timeouts are in place; headless skips state their reasons precisely.

## Covers

- [[Project Legends Test Suite]] — the audited artifact: ~4,600 TEST macros across tests/ and engine/tests/, grade C, wide but under-enforced with stub and dead files inflating counts.
- [[Build & CI System (Project Legends)]] — headless-only merge gate, report-only coverage, never-built benchmarks, path-filtered SDL jobs, and a soak suite no workflow can enable.
- [[Quality Gate Demotion (2026-06-08)]] — commit 6900e7a demoted sanitizers, fuzzing, TLA+, and static analysis to nightly/manual-only, stripping the merge gate one day before this audit.
- [[Determinism Oracle Weakness]] — all determinism and roundtrip tests assert on a Fast-mode hash that ignores guest RAM, CPU registers, and VRAM, so they cannot observe the state that matters.
- [[IPC Trust Boundary Gaps]] — dispatcher tested for 8 of 43 message cases, no malformed-payload tests, no parity suite, and no fuzz target on the layer consuming cross-process bytes.
- [[IPC Runtime (Project Legends)]] — the proxy→pipe→engine_host→dispatcher→legends_core chain is never exercised under assertion; the only E2E test is DISABLED_ and RuntimeHost has no unit test.
- [[Legends C API Layer]] — per-API coverage map: 1 API untested, 15 device APIs null-handle-only, capability-gated APIs never asserted in CI; core create/step/save/load paths well covered.
- [[Engine Bridge (DOSBox-X)]] — engine-side hash modes (Fast vs Full), 6 unregistered engine test files, and headless DMA hashing reduced to presence bytes.
- [[Save-State Load Path Overflow]] — the CRC-first load path means the fuzzers never reach the H9 reinterpret_cast deserialization code; the existing security tests assert exact error codes.
- [[Prior-Audit Remediation Status]] — L8 resolved, H5 fixed, H7 partially resolved with the gap moved into the tests, and the prior test-gaps table mostly still open.
- [[Documentation Drift]] — static README badges, an overstated roundtrip-verification claim (README.md:138), and a ci.yml header plus AUDIT.md CI table that no longer describe the merge gate.
