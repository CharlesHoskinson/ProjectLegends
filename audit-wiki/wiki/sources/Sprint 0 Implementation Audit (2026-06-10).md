---
type: source
aliases: ["Sprint 0 Audit", "Stop the Bleeding audit"]
tags: [source, type/source, topic/audit, topic/remediation]
created: 2026-06-10
updated: 2026-06-10
status: draft
title: Sprint 0 Implementation Audit (2026-06-10)
authors: [Claude auditor]
url:
publisher:
published: 2026
accessed: 2026-06-10
source_type: report
covers:
  - "[[Save-State Load Path Overflow]]"
  - "[[Licensing Inconsistency]]"
  - "[[Quality Gate Demotion (2026-06-08)]]"
  - "[[Legends C API Layer]]"
  - "[[Engine Bridge (DOSBox-X)]]"
  - "[[Project Legends Test Suite]]"
---

# Sprint 0 Implementation Audit (2026-06-10)

## Summary

Adversarial audit of GPT 5.5 Codex's Sprint 0 implementation on branch
`sprint-0/stop-the-bleeding` (5 commits off master `ce6a847`). Verdict: PASS on
all five items with no code defects. Both criticals (mem-01 save-state heap
overflow, lic-01 MIT-over-GPL LICENSE) and the high-severity items (mem-02
create-brick, CI gate re-arm, CRC-aware fuzzer) are genuinely fixed and
independently verified.

## Key takeaways

- mem-01 fixed at root cause: the lines overwriting `ctx->memory.size` from blob
  contents are removed; RAM/VRAM decode into live-sized local buffers; an early
  pass rejects oversized `mem.size`. The fix adds no new OOB read (inserted reads
  follow existing offset validation). Confirmed genuine, not cosmetic.
- mem-01 regression test is exploit-shaped (oversized size + re-encoded RLE blob
  + recomputed CRC, asserts INVALID_STATE and unchanged state hash); fails pre-fix
  under ASan. Independently re-run: engine-state group 25/25 pass.
- mem-02 fixed: the `catch` path that leaked a live engine handle now routes
  through a centralizing `fail_create` lambda; a `LEGENDS_TESTING`-gated injection
  test proves a subsequent create succeeds. Lifecycle group 15/15 pass independently.
- CI gates re-armed: ASan/UBSan + fuzz smoke now run on PR and push-to-master;
  the dead PR-fuzz step is fixed; `develop` added to PR filters; TSan/MSan keep
  allow_failure with dated Sprint-7 exit-plan comments. actionlint exit 0 (independent).
- LICENSE rewritten as a true multi-component overview that explicitly reserves
  the GPL-2.0-only-vs-or-later decision; COPYING/NOTICE untouched; MIT/GPL SPDX
  spot-checks hold.
- New `fuzz_engine_memory_blob` has a real CRC-recomputing custom mutator; an
  independent 60s run did 228,237 execs with zero crashes and 5,360 clean
  oversized-RAM rejections.
- All six handoff attestations verified true against the git diff; scope
  discipline was exact (11 in-scope files; audit-wiki/plan/COPYING/NOTICE untouched).
- Minor process findings (not defects): handoff files left untracked; null start
  timestamp; caveated "0 new warnings" with auditor-repro flag overrides hinting
  at pre-existing Windows dev-preset friction; duplicated V5 directory parse.

## Covers

- [[Save-State Load Path Overflow]] — mem-01 resolved and verified; the contested overflow-vs-bounded conflict is settled in favor of the overflow (now fixed)
- [[Licensing Inconsistency]] — lic-01 root LICENSE resolved without making the reserved -only/-or-later decision
- [[Quality Gate Demotion (2026-06-08)]] — gates re-armed on PR and push-to-master
- [[Legends C API Layer]] — mem-02 create-error-path leak closed
- [[Engine Bridge (DOSBox-X)]] — mem-01 lives here; root-cause descriptor overwrite removed
- [[Project Legends Test Suite]] — two real regression tests + CRC-aware fuzz target added
