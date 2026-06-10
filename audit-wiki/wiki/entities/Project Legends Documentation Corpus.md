---
type: entity
entity_kind: document-set
aliases: ["docs of record", "README/ARCHITECTURE/REQUIREMENTS"]
tags: [entity, type/entity, topic/audit, topic/docs]
created: 2026-06-09
updated: 2026-06-09
status: draft
related:
  - "[[Documentation Drift]]"
  - "[[Licensing Inconsistency]]"
sources:
  - "[[Docs & Licensing Audit (2026-06)]]"
  - "[[Backlog Verification Audit (2026-06)]]"
  - "[[Concurrency & Determinism Audit (2026-06)]]"
  - "[[Build & CI Audit (2026-06)]]"
---

# Project Legends Documentation Corpus

## Overview

The documents of record: README, ARCHITECTURE (38KB), REQUIREMENTS (50 EARS requirements), roadmap (213KB), TODO, CHANGELOG, AUDIT, TLA_CONFORMANCE, RELEASING, CONTRIBUTING, DEPENDENCIES, NOTICE, plus openspec/. Some sections verify exactly against source; the February-era status documents have drifted badly in both directions.

## Facts

- The doc set splits into two eras: recently refreshed docs verify exactly; February-era docs have drifted.^[from [[Docs & Licensing Audit (2026-06)]] — "The documentation set splits into two eras"]
- Sampled REQUIREMENTS statuses are wrong in both directions — fixed items still GAP, broken claims still done.^[from [[Docs & Licensing Audit (2026-06)]] — "sampled statuses wrong in both directions"]
- The README architecture-diagram counts (50 APIs, 108 message types, 89 structs, 43 cases) are all exact matches at HEAD.^[from [[Docs & Licensing Audit (2026-06)]] — "all exact matches at HEAD"]
- 27 of the 50 API functions appear nowhere in the README.^[from [[Backlog Verification Audit (2026-06)]] — "27 of 50 functions are not mentioned at all"]
- AUDIT.md was never annotated with its 22 resolutions.^[from [[Backlog Verification Audit (2026-06)]] — "AUDIT.md records none of the 22 resolutions, inviting duplicate work"]
- The TLA+ conformance document was never re-baselined after the fixes landed.^[from [[Concurrency & Determinism Audit (2026-06)]] — "the conformance document was never re-baselined"]
- RELEASING.md documents a branch/tag workflow that has never been performed.^[from [[Build & CI Audit (2026-06)]] — "documents a branch/tag workflow"]
- The CI duplication that turns one root cause into several failures was already diagnosed in-repo.^[from [[Build & CI Audit (2026-06)]] — "CI is duplicated across CI, PAL CI, Module DAG"]

## Related

- [[Documentation Drift]] — this entity's failure mode
- [[Licensing Inconsistency]] — its most dangerous instance
- [[Prior-Audit Remediation Status]] — the progress the corpus fails to record
