---
type: concept
aliases: ["C2", "PIC stub linkage"]
tags: [concept, type/concept, topic/audit, topic/determinism]
created: 2026-06-09
updated: 2026-06-09
status: draft
parent: [[overview]]
related:
  - "[[Determinism Oracle Weakness]]"
  - "[[Engine Bridge (DOSBox-X)]]"
sources:
  - "[[Concurrency & Determinism Audit (2026-06)]]"
  - "[[Backlog Verification Audit (2026-06)]]"
  - "[[Memory Safety Audit (2026-06)]]"
  - "[[Docs & Licensing Audit (2026-06)]]"
claims_status: contested
---

# Vacuous Interrupt Delivery (C2)

## Definition

Prior-audit finding C2 said the CPU bridge skips PIC event processing and NMI checks during stepped execution. Code was added to call `PIC_RunQueue()` and `CPU_Check_NMI()` — but the 2026-06 concurrency audit found the library build links a no-op stub `PIC_RunQueue`, so timer/IRQ-driven guest code still never fires during `legends_step_*`. Whether C2 is "fixed" is the audit's sharpest contradiction.

## Claims

- The bridge now processes PIC events before CPU execution at cpu_bridge.cpp:113.^[from [[Backlog Verification Audit (2026-06)]] — "Process pending PIC events before CPU execution"]
- The bridge adds the NMI check the original finding flagged as missing.^[from [[Backlog Verification Audit (2026-06)]] — "Check for NMI after execution"]
- The memory-safety auditor likewise verified the C2 calls as present.^[from [[Memory Safety Audit (2026-06)]] — "CPU bridge skips PIC_RunQueue/NMI"]
- But virtual device time does not advance during legends steps — `TIMER_AddTick` is never called on the step path.^[from [[Concurrency & Determinism Audit (2026-06)]] — "virtual device time literally does not advance"]
- No PIC event queue exists in library mode, so scheduled events (PIT IRQ0, keyboard IRQ1) never fire.^[from [[Concurrency & Determinism Audit (2026-06)]] — "No PIC event queue exists in library mode"]
- The real PIC implementation is compiled into no build target, so the library gets the stub.^[from [[Concurrency & Determinism Audit (2026-06)]] — "is not part of any CMake target"]
- Naively linking the real PIC would corrupt the bridge's consumed-cycle math.^[from [[Concurrency & Determinism Audit (2026-06)]] — "the bridge's cycle accounting only works with the stub"]
- Meanwhile the requirements doc still lists the interrupt-delivery REQs as GAP, stale in the other direction.^[from [[Docs & Licensing Audit (2026-06)]] — "REQUIREMENTS.md REQ-EX-001/002 still claim GAP"]

> [!conflict] Is prior finding C2 resolved?
> - Resolved: PIC_RunQueue()/CPU_Check_NMI() calls present at cpu_bridge.cpp:113,119 — [[Backlog Verification Audit (2026-06)]], [[Memory Safety Audit (2026-06)]], [[Docs & Licensing Audit (2026-06)]] (2026-06-09)
> - Vacuous: the linked PIC_RunQueue is a no-op stub; the real PIC is in no CMake target — [[Concurrency & Determinism Audit (2026-06)]] (2026-06-09)
> Status: contested — the source-level calls exist but the link-level analysis shows they do nothing in library builds. The deeper check wins for planning purposes: the sprint plan treats C2 as OPEN (Sprint 6, "make time real"), with a verification spike to settle it first.

## Related

- [[Determinism Oracle Weakness]] — a weak hash cannot detect that device time never advances
- [[Engine Bridge (DOSBox-X)]] — where the stub linkage lives
- [[Sprint Plan Derivation (2026-06)]] — Sprint 6
