# Sprint 1 Implementation Audit — 2026-06-10

Auditor: Claude (Fable 5). Subject: GPT 5.5 Codex implementation of Sprint 1
("Truthful Record") on branch `sprint-1/truthful-record` (HEAD `56f9dfa`,
11 commits off master `866a24d`). Method: three-dot diff review, independent
re-run of all three new scripts, independent re-verification of a random subset
of the `claims_verified` array against source at HEAD, verification of the three
critical corrections against source, and every attestation/scope_check vs the diff.

## Verdict: PASS (8/8 items), no defects. All three corrections honored.

This sprint's risk was that a "truthful record" pass could itself drift. It did
not. The three findings I flagged as needing a careful (non-naive) fix were all
handled correctly, verified against source.

## Scope verification (all clean)
- `git diff master...HEAD -- src/ engine/` is EMPTY — zero production code changed.
- `git diff master...HEAD -- audit-wiki/` is EMPTY — auditor record untouched.
- No SPDX header edits to source: the only diff lines matching "SPDX" are prose
  inside `decision-gpl-license.md` and the handoff JSON discussing SPDX counts.
- `CMakeLists.txt` change is COMMENT-ONLY (Wasm scaffold note + ARCHITECTURE
  pointer); the `if(LEGENDS_BUILD_WASM)` logic is untouched. In scope.
- Roadmap case collision eliminated: `ls-tree` shows only `ROADMAP.md`;
  `roadmap.md` deleted (-4061). `git ls-files | findstr /I roadmap` → one path.

## Independent script re-runs (all pass)
- `check_case_collisions.py --path .` → exit 0 ("No collisions in 2326 paths").
  Deliberate-collision repro → exit 1 (correctly detects). Stdlib, modeled on
  check_conflict_markers.py.
- `gen_readme_api_table.py` run twice → IDENTICAL output (76 lines). Deterministic.
- `check_openspec_staleness.py --path .` → exit 0. Honest INFO: 3 June
  `runtimehost-*` changes are 100% complete but left active per the directive's
  "don't touch the June set" scope (a directive-conservatism artifact, not a
  Codex error — see Observations).

## Critical corrections — verified against source
1. ROADMAP de-dup-not-restore (Correction #1): `ROADMAP.md:1-16` keeps the
   4,061-line content, sets an honest date (2026-06-10) and version
   (4.2.1-record), and adds a Truthful-record note explicitly reserving the
   427-vs-4061-line choice to the owner. roadmap.md removed from the index. CORRECT.
2. CHANGELOG reworded-not-deleted (Correction #2): `CHANGELOG.md:36-38` now reads
   "update-checker HTTPS transport uses WinHTTP secure requests
   (update_checker_win.cpp:46); AI HTTP client transport is still deferred
   (ai_http_client.cpp:212)". Accurate scope; not deleted, not overclaimed. CORRECT.
3. REQ-EX-001/002 PARTIAL-not-OK (Correction #3): `REQUIREMENTS.md:92-110` sets
   both to **PARTIAL** with evidence "cpu_bridge.cpp:113 calls PIC_RunQueue() but
   cpu_library_stubs.cpp:56-60 links a stub PIC queue ... functional delivery
   scheduled for Sprint 6". I independently opened cpu_library_stubs.cpp:56-60 and
   confirmed the stub is real (`bool PIC_RunQueue(void) { // Stub: no PIC event
   queue ... return false; }`). The PARTIAL status is the correct truth. CORRECT.

## Random-subset claim re-verification (sampled from claims_verified)
- TODO.md contradictions resolved: the six REQ IDs (MOUNT-001/002, MENU-001,
  MAPPER-001, SAVE-003, CAPTURE-003) now appear ONLY as `[x]` done lines (75,80,
  82,87,90,91); no blocker-table duplicates remain.
- ARCHITECTURE.md:195-197 constants fixed to 64 bytes / 0x53584244 "DBXS" / v3
  (was 96 / "LEGS" / v2), matching legends_embed_api.cpp:100-101,225.
- README API count: 50 LEGENDS_API functions confirmed in the header (Codex
  honestly flagged the directive's "51" as wrong and used the verified 50).
- Decision briefs present and substantive: decision-gpl-license.md (9.6 KB,
  recommends -or-later), decision-wasm.md (4.7 KB, recommends defer §15 unless
  spike funded). Both `decision_made_by_implementer: false`. PREPARED, not MADE.

## Attestations (all confirmed against the diff)
no_production_source_changed, audit_wiki_untouched, gpl_decision_not_made,
wasm_decision_not_made, no_history_rewrite_or_force_push, all_deliverables_committed
— all TRUE. corrections_honored {roadmap_dedup, changelog_reworded, req_ex_partial}
— all TRUE and independently re-verified above.

## Honest deviations Codex disclosed (all reasonable; none are defects)
- 50 vs 51 LEGENDS_API functions: directive estimate was wrong; Codex used the
  verified source count. Good.
- openspec/project.md absent at HEAD (directive referenced it): Codex adapted and
  populated specs/ directly from archived changes' specs. Reasonable.
- JSON head_commit/diffstat are the last pre-handoff-commit values (a committed
  JSON cannot contain its own commit's SHA): honestly explained; actual branch
  HEAD is 56f9dfa.

## Minor observations (not defects; candidates for follow-up)
1. Three June `runtimehost-*` OpenSpec changes are 100% complete but left active
   because my directive scoped archival to `phase-*`. The staleness script
   surfaces them as INFO. A follow-up could archive them too. (My directive's
   conservatism, not a Codex miss.)
2. The three new scripts may lack SPDX headers (repo policy tags source files).
   Cosmetic; fold into a future cleanup.

## Net effect
Documentation Drift (the audit's most universal theme) is now substantially
resolved: roadmap de-duplicated and honestly stamped; TODO/AUDIT/CHANGELOG
reconciled; Wasm demoted to planned with git-history proof; REQUIREMENTS and
TLA conformance re-baselined with verified-at stamps; README API/error tables
generated; three new CI guard scripts added. Two owner decisions are queued
(GPL -or-later; Wasm defer-or-spike).
