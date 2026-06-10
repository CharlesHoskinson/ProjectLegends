---
type: concept
aliases: ["mem-01", "Save-state heap overflow"]
tags: [concept, type/concept, topic/audit, topic/memory-safety]
created: 2026-06-09
updated: 2026-06-09
status: resolved
parent: [[overview]]
related:
  - "[[Prior-Audit Remediation Status]]"
  - "[[Engine Bridge (DOSBox-X)]]"
  - "[[Legends C API Layer]]"
sources:
  - "[[Memory Safety Audit (2026-06)]]"
  - "[[Security Audit (2026-06)]]"
  - "[[Test Coverage Audit (2026-06)]]"
  - "[[Sprint 0 Implementation Audit (2026-06-10)]]"
claims_status: superseded
---

# Save-State Load Path Overflow

## Definition

The save-state load path is the project's primary untrusted-input surface in the default in-process build. The 2026-06 audit found it broadly well-hardened — except for one confirmed critical heap buffer overflow (finding mem-01) in the engine deserializer, where an attacker-controlled size field becomes the RLE decompression capacity.

## Claims

- The engine deserializer overwrites its live memory-allocation descriptor directly from untrusted save data, the root cause of the critical overflow.^[from [[Memory Safety Audit (2026-06)]] — "overwrites the live allocation descriptor verbatim from untrusted input"]
- A small crafted RLE blob expands far past the real allocation: a heap buffer overflow.^[from [[Memory Safety Audit (2026-06)]] — "tiny crafted blob writes hundreds of MB past a ~704 KB allocation"]
- The legends-layer loader validates the header before any deserialization.^[from [[Security Audit (2026-06)]] — "validate magic, version, declared size vs underflow"]
- The hardened load path applies state atomically so partial loads cannot corrupt state.^[from [[Security Audit (2026-06)]] — "with a four-phase atomic load"]
- This surface is exposed in the default (non-IPC) build.^[from [[Security Audit (2026-06)]] — "Save-state load is reachable in the default in-process build"]
- The existing load-state fuzzers cannot reach the deserialization logic because the mutator never recomputes the checksum.^[from [[Test Coverage Audit (2026-06)]] — "virtually every mutated input dies at the CRC check"]
- The save-state security tests that do exist assert exact error codes for corrupted inputs.^[from [[Test Coverage Audit (2026-06)]] — "corrupted offsets, geometry, truncation — with exact error-code assertions"]

> [!conflict] Is the engine RLE decode bounded?
> - Bounded with clamps and per-entry checks — [[Security Audit (2026-06)]] (2026-06-09)
> - Critical overflow: decode capacity taken from attacker-controlled `memory.size` — [[Memory Safety Audit (2026-06)]] (2026-06-09)
> Status: contested — adversarial verification confirmed the overflow (isReal=true, high confidence); the validation the security auditor saw guards other fields but not the allocation descriptor. Sprint plan treats mem-01 as OPEN and CRITICAL.

> [!check] RESOLVED 2026-06-10 (Sprint 0)
> Fixed on branch `sprint-0/stop-the-bleeding` and audited PASS. The descriptor-overwrite root cause was removed, RAM/VRAM decode into live-allocation-sized buffers, and an early pass rejects oversized `mem.size`. The contradiction is settled in favor of the overflow read (the memory-safety auditor was right); it is now closed. An exploit-shaped regression test plus a CRC-aware fuzzer (228k execs, 0 crashes) verify the fix. Provenance: [[Sprint 0 Implementation Audit (2026-06-10)]].

## Related

- [[Prior-Audit Remediation Status]] — H6/H9 in this same path were genuinely fixed; mem-01 arrived with the V5 expansion
- [[Engine Bridge (DOSBox-X)]] — the defect lives in the engine-side loader
- [[Sprint Plan Derivation (2026-06)]] — Sprint 0 item 1
