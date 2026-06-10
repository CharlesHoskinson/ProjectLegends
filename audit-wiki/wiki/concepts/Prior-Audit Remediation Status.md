---
type: concept
aliases: ["AUDIT.md verification", "22 of 30 resolved"]
tags: [concept, type/concept, topic/audit, topic/backlog]
created: 2026-06-09
updated: 2026-06-09
status: draft
parent: [[overview]]
related:
  - "[[Vacuous Interrupt Delivery (C2)]]"
  - "[[Quality Gate Demotion (2026-06-08)]]"
  - "[[Documentation Drift]]"
sources:
  - "[[Backlog Verification Audit (2026-06)]]"
  - "[[Memory Safety Audit (2026-06)]]"
  - "[[API & Architecture Audit (2026-06)]]"
  - "[[Test Coverage Audit (2026-06)]]"
  - "[[Concurrency & Determinism Audit (2026-06)]]"
  - "[[Build & CI Audit (2026-06)]]"
claims_status: supported
---

# Prior-Audit Remediation Status

## Definition

The 2026-02-24 AUDIT.md logged 30 findings (2 critical, 9 high, 11 medium, 8 low). The 2026-06 fleet re-verified every one at HEAD `ef11f20`: 22 are genuinely resolved, 8 remain open (none critical by the backlog-miner's tally, though the C2 "resolution" is contested at link level). The remediation work was real; the record-keeping was not.

## Claims

- 22 of 30 prior findings are verifiably resolved at HEAD.^[from [[Backlog Verification Audit (2026-06)]] — "22 of 30 AUDIT.md findings are verifiably resolved at HEAD"]
- Final disposition: 22 resolved, 8 open.^[from [[Backlog Verification Audit (2026-06)]] — "Tally: 22 resolved, 8 open"]
- The open remainder is mostly hygiene and accepted design, not critical defects.^[from [[Backlog Verification Audit (2026-06)]] — "none critical, mostly accepted-design or hygiene debt"]
- The memory-safety scope verified eight prior findings as genuinely, not cosmetically, fixed.^[from [[Memory Safety Audit (2026-06)]] — "H5, H6, H9, M7, M8, M9, M11 and C2 are all resolved"]
- H5's destroy-fallback hole is fixed in the in-process path.^[from [[API & Architecture Audit (2026-06)]] — "the destroy-fallback hole (H5) is fixed"]
- C1's 27-pair header duplication collapsed to forwarding shims.^[from [[API & Architecture Audit (2026-06)]] — "has been collapsed to 4-line forwarding headers"]
- The L8 sentinel-destroy test anti-pattern is fixed with a real rejection-and-survival test.^[from [[Test Coverage Audit (2026-06)]] — "L8 (sentinel destroy masking H5) is fixed"]
- Four of five non-conformant TLA+ invariants were fixed in code since February.^[from [[Concurrency & Determinism Audit (2026-06)]] — "Four of the five NON-CONFORMANT TLA+ invariants"]
- But the June 8 CI demotion functionally re-opened H7/H8/M12 for merges.^[from [[Build & CI Audit (2026-06)]] — "now effectively re-opened for the code paths that matter"]
- And the IPC proxy re-creates the spirit of fixed H5 across the process boundary.^[from [[API & Architecture Audit (2026-06)]] — "re-creates the spirit of fixed finding H5"]
- AUDIT.md itself records none of the 22 resolutions, inviting duplicate remediation.^[from [[Backlog Verification Audit (2026-06)]] — "AUDIT.md records none of the 22 resolutions, inviting duplicate work"]

## Related

- [[Vacuous Interrupt Delivery (C2)]] — the one contested "resolution"
- [[Quality Gate Demotion (2026-06-08)]] — how resolved findings regress
- [[Documentation Drift]] — why nobody can see the progress
