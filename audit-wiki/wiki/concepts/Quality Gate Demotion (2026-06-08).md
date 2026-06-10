---
type: concept
aliases: ["CI gate demotion", "commit 6900e7a"]
tags: [concept, type/concept, topic/audit, topic/ci]
created: 2026-06-09
updated: 2026-06-09
status: draft
parent: [[overview]]
related:
  - "[[Build & CI System (Project Legends)]]"
  - "[[Prior-Audit Remediation Status]]"
sources:
  - "[[Build & CI Audit (2026-06)]]"
  - "[[Test Coverage Audit (2026-06)]]"
  - "[[Backlog Verification Audit (2026-06)]]"
claims_status: supported
---

# Quality Gate Demotion (2026-06-08)

## Definition

One day before this audit, commit 6900e7a restructured CI to get a red pipeline green by moving sanitizers, fuzzing, TLA+ model checking, and static analysis off the PR/merge gate into nightly/manual-only lanes. This silently re-opened three prior-audit fixes (H7 fuzz-in-CI, H8 TLA-in-CI, M12 sanitizer matrix) for the code paths that matter.

## Claims

- Enforcement of the heavyweight checks was demoted to nightly/manual-only.^[from [[Build & CI Audit (2026-06)]] — "enforcement was demoted to nightly/manual-only"]
- Sanitizers, fuzz, TLA+, and static analysis no longer run on push or PR.^[from [[Build & CI Audit (2026-06)]] — "None of these happen on push or PR anymore"]
- The change was the 2026-06-08 CI stabilization commit.^[from [[Test Coverage Audit (2026-06)]] — "Stabilize CI and RuntimeHost adoption"]
- Memory-safety regressions can land and sit undetected until a nightly run.^[from [[Test Coverage Audit (2026-06)]] — "can now merge to main and sit for up to 24h"]
- The intended PR fuzz smoke is dead code: the job-level condition excludes PR events entirely.^[from [[Build & CI Audit (2026-06)]] — "excludes `pull_request` events entirely"]
- TSan has been allow-failure with known named races since March.^[from [[Build & CI Audit (2026-06)]] — "TSan signal has been muted since 2026-03-02"]
- The demotion effectively re-opens prior fixes H7/H8/M12 for PRs and merges.^[from [[Build & CI Audit (2026-06)]] — "now effectively re-opened for the code paths that matter"]
- The restructure split workflows into gating and non-gating lanes.^[from [[Backlog Verification Audit (2026-06)]] — "workflows split into primary vs optional lanes"]

> [!check] RESOLVED 2026-06-10 (Sprint 0)
> Reversed on branch `sprint-0/stop-the-bleeding` (audited PASS): ASan/UBSan and a fuzz smoke now run on pull_request and push-to-master, the dead PR-fuzz step is fixed, and `develop` is added to PR filters. TSan/MSan stay allow_failure but now carry dated Sprint-7 exit-plan comments. Independent actionlint exit 0. Provenance: [[Sprint 0 Implementation Audit (2026-06-10)]].

## Related

- [[Build & CI System (Project Legends)]] — the machinery exists; it is the gating that regressed
- [[Prior-Audit Remediation Status]] — three resolved findings functionally re-opened
- [[Sprint 0 Implementation Audit (2026-06-10)]] — the remediation and its audit
- [[Sprint Plan Derivation (2026-06)]] — Sprint 0 item 3 (re-arm the gates)
