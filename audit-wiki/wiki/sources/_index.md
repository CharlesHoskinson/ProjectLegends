# Sources index

Each entry: `[[Page]] — one-line summary`.

- [[Backlog Verification Audit (2026-06)]] — 2026-06-09 verification of the 2026-02 audit: 22 of 30 findings resolved at HEAD ef11f20, 8 open (none critical), plus five new documentation-of-record defects including a clobbered roadmap and a false TLS changelog claim.
- [[API & Architecture Audit (2026-06)]] — grade C; core 50-function C ABI solid and prior fixes verified, but the IPC runtime split cannot boot, diverges semantically, skips version handshakes, and outruns DAG/licensing enforcement (api-05 refuted).
- [[Memory Safety Audit (2026-06)]] — prior backlog (H5, H6, H9, M7, M8, M9, M11, C2) verified fixed, but a new CRITICAL save-state heap overflow and a HIGH engine-handle leak yield grade C.
- [[Security Audit (2026-06)]] — grade C: save-state deserialization well-hardened with H6/H9 resolved, but the IPC/SHM GPL trust boundary lacks response validation, peer authentication, fuzzing, and verified isolation (SEC-01 refuted).
- [[Concurrency & Determinism Audit (2026-06)]] — the C2 PIC fix is vacuous (stub linked, no device time), the determinism hash is blind to GPRs/RAM, the IPC proxy desyncs on timeout, and conformance docs are stale; real thread-discipline progress confirmed (M7 resolved, 4/5 invariants fixed).
- [[Build & CI Audit (2026-06)]] — grade C: extensive machinery (sanitizers, fuzz, TLA+, packaging) demoted to nightly-only by commit 6900e7a, GPL isolation unenforced, release pipeline never run, dev preset broken in committed logs.
- [[Test Coverage Audit (2026-06)]] — grade C: broad (~4,600 TEST macros) but under-enforced after the merge-gate demotion, with hash oracles blind to RAM/registers/VRAM, an untested IPC trust boundary, 8 stub integration tests, and CRC-walled fuzzers.
- [[Docs & Licensing Audit (2026-06)]] — grade D: bare MIT root LICENSE over a GPL codebase, GPL-2.0-only vs -or-later contradicted by all SPDX tags, never-committed Wasm artifacts, ~3.5-month-stale REQUIREMENTS statuses, and an unwired GPL-isolation CI gate.
- [[Sprint 0 Implementation Audit (2026-06-10)]] — auditor verdict on GPT 5.5 Codex's Sprint 0 branch: PASS on all 5 items, no code defects; mem-01 overflow + lic-01 LICENSE + mem-02 brick + CI gates + CRC-aware fuzzer all genuinely fixed and independently re-verified.
- [[Sprint 1 Implementation Audit (2026-06-10)]] — auditor verdict on Sprint 1 (Truthful Record): PASS 8/8, no defects; all three corrections honored (roadmap de-dup, CHANGELOG reword, REQ-EX PARTIAL); docs reconciled, 3 CI guard scripts added, 2 owner decisions queued.
- [[CI Run History (2026-06)]] — observational stats over all 397 retained Actions runs (2026-01-16..2026-06-10): 77.6% failure overall, CI workflow 6 successes ever (all post-gate-demotion), PAL CI zero, ~3h05m serial compute per full cycle.
