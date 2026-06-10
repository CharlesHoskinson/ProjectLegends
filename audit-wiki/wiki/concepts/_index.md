# Concepts index

Each entry: `[[Page]] — one-line summary`.

- [[Save-State Load Path Overflow]] — confirmed critical heap overflow: engine deserializer trusts attacker-controlled memory.size as RLE decode capacity (contested vs the security read; verifier sided with the overflow).
- [[IPC Trust Boundary Gaps]] — the GPL/security boundary lacks peer auth, response correlation, fuzzing, and parity verification (SEC-01 refuted and excluded).
- [[Vacuous Interrupt Delivery (C2)]] — contested: PIC_RunQueue/CPU_Check_NMI calls exist but library builds link a no-op stub, so device time never advances.
- [[Determinism Oracle Weakness]] — determinism/roundtrip tests assert on a hash that excludes CPU registers, guest RAM, and VRAM.
- [[Quality Gate Demotion (2026-06-08)]] — commit 6900e7a moved sanitizers, fuzz, TLA+, and static analysis off the merge gate, re-opening prior fixes H7/H8/M12.
- [[Licensing Inconsistency]] — bare MIT root LICENSE over GPL code, -only vs -or-later contradiction, and GPL-isolation enforcement wired into nothing.
- [[Documentation Drift]] — records wrong in both directions: phantom capabilities (Wasm, TLS) and unrecorded real progress (22 resolutions, fixed invariants).
- [[Prior-Audit Remediation Status]] — 22 of 30 February findings verifiably resolved at HEAD; 8 open; none of it recorded in AUDIT.md.
