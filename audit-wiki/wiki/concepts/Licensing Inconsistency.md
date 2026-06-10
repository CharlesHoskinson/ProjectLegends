---
type: concept
aliases: ["lic-01", "GPL licensing defects"]
tags: [concept, type/concept, topic/audit, topic/licensing]
created: 2026-06-09
updated: 2026-06-09
status: draft
parent: [[overview]]
related:
  - "[[IPC Trust Boundary Gaps]]"
  - "[[Project Legends Documentation Corpus]]"
sources:
  - "[[Docs & Licensing Audit (2026-06)]]"
  - "[[Build & CI Audit (2026-06)]]"
  - "[[API & Architecture Audit (2026-06)]]"
claims_status: supported
---

# Licensing Inconsistency

## Definition

The project's licensing story — MIT shell over a GPL engine, kept apart by process isolation — is contradicted by its own files: the root LICENSE is a bare MIT grant over a GPL codebase (critical), docs say GPL-2.0-only while every SPDX tag says -or-later, and the mechanical enforcement of the GPL boundary exists but is wired into nothing.

## Claims

- The root LICENSE is verbatim MIT text with no component scoping, over a codebase whose engine is GPL.^[from [[Docs & Licensing Audit (2026-06)]] — "a bare MIT grant over a GPL codebase"]
- On -only vs -or-later, docs and code disagree everywhere: 107 src/ files tagged GPL-2.0-or-later, zero tagged -only.^[from [[Docs & Licensing Audit (2026-06)]] — "docs and code disagree everywhere"]
- The auditor classes the root LICENSE as a license-misrepresentation risk, not just doc drift.^[from [[Docs & Licensing Audit (2026-06)]] — "a license-misrepresentation risk, not just doc drift"]
- The design doc calls the GPL-tagged application shell proprietary — it cannot be both.^[from [[Docs & Licensing Audit (2026-06)]] — "The shell cannot be simultaneously proprietary and GPL"]
- Vendored components are unattributed: no stb, glad, zlib, or FluidSynth/MUNT entries in NOTICE/DEPENDENCIES.^[from [[Docs & Licensing Audit (2026-06)]] — "no stb, no glad, no zlib, no FluidSynth/MUNT"]
- The GPL-isolation verifier exists but no CMakeLists includes it.^[from [[Build & CI Audit (2026-06)]] — "no CMakeLists in the repository includes it"]
- Module-DAG verification skips every license-critical target.^[from [[Build & CI Audit (2026-06)]] — "the module DAG skips all license-critical targets"]
- The central isolation requirement is not verified by anything.^[from [[Build & CI Audit (2026-06)]] — "REQ-ISO-016 is not verified by anything"]
- A stray GPL link from the MIT proxy would pass configure-time verification silently.^[from [[API & Architecture Audit (2026-06)]] — "would pass DAG verification silently"]

> [!check] PARTIALLY RESOLVED 2026-06-10 (Sprint 0)
> lic-01 (the critical bare-MIT root LICENSE over GPL code) is fixed on branch `sprint-0/stop-the-bleeding` (audited PASS): LICENSE is now a multi-component overview with a per-path SPDX table, COPYING/NOTICE untouched. It deliberately does NOT resolve GPL-2.0-only vs -or-later — that owner decision is reserved for Sprint 1.7. The remaining licensing items (lic-02 -only/-or-later decision, lic-03 header dual-licensing, lic-04 attribution, unenforced GPL-isolation) stay open for Sprints 1 and 5. Provenance: [[Sprint 0 Implementation Audit (2026-06-10)]].

## Related

- [[IPC Trust Boundary Gaps]] — the unenforced boundary is the same one that is supposed to carry the legal load
- [[Project Legends Documentation Corpus]] — where the contradictions live
- [[Sprint 0 Implementation Audit (2026-06-10)]] — the LICENSE remediation and its audit
- [[Sprint Plan Derivation (2026-06)]] — Sprint 0 item 4 (LICENSE rewrite) and Sprint 5 (enforcement)
