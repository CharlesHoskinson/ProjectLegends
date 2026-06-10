# Sprint 1 — Truthful Record: Execution Plan

> **For agentic workers:** REQUIRED SUB-SKILL: superpowers:subagent-driven-development or superpowers:executing-plans. Steps use `- [ ]` checkboxes.
>
> **Execution model:** GPT 5.5 Codex implements from the paired XML directive; Claude audits the result. This plan is the grounded spec the directive points at — every target below was verified at HEAD on 2026-06-10 (post Sprint 0 merge, commit `74908b0`). File:line citations are real reads, not audit-report summaries.

**Goal:** Make Project Legends' documents of record match the code at HEAD — eliminate contradictions, phantom capabilities, and stale statuses — without changing any production source.

**Architecture:** Documentation + verification-script changes only. Two owner-reserved decision gates are *prepared, not made*. Every status written into a doc must be backed by a file:line read at HEAD.

**Tech Stack:** Markdown docs, Python stdlib check scripts (modeled on `scripts/check_*.py`), GitHub Actions (`sprint2-checks.yml` job), OpenSpec.

---

## Context

Every one of the eight audit roles independently hit documentation drift (see `audit-wiki/wiki/concepts/Documentation Drift.md`): the records claim things that don't exist (Wasm, a blanket "TLS verification") and fail to record real progress (22 resolved findings, fixed TLA invariants, the C2 PIC/NMI calls). Sprint 0 already fixed the worst single instance (the MIT-over-GPL LICENSE). Sprint 1 fixes the rest so that Sprint 2+ planning runs on accurate data. The hazard unique to this sprint: a "truthful record" pass that itself drifts is self-defeating — so three findings need a more careful fix than the audit summaries implied (see corrections below).

---

## Ground-truth corrections to the program-level Sprint 1

These override the program plan / first-draft directive where they conflict:

1. **Roadmap (item 1.1).** `git ls-files` tracks BOTH `ROADMAP.md` and `roadmap.md`; on disk both are 4,061 lines of identical v4.2.0 content (June `1dd76b4`). The March `8e3b0b0` "source-verified" `ROADMAP.md` was only 427 lines. Do **not** blindly restore 427 lines — that drops the detailed EARS roadmap many other docs reference. Fix = (a) collapse to ONE tracked path, (b) correct the self-contradictory stamp (header says `Version: 4.2.0` + `Date: 2026-02-27` but was edited 2026-06-08), (c) re-verify the phase/status claims it makes. Whether to also slim it toward the 427-line shape is an OWNER content call — flag it, don't decide it.
2. **CHANGELOG TLS (item 1.2c).** `CHANGELOG.md:36` says "TLS verification". This is partly real: `src/app/update_checker_win.cpp:37` uses WinHTTP `WINHTTP_FLAG_SECURE` (genuine HTTPS for the update checker). The *AI* client has no transport (`src/app/ai_http_client.cpp:212` — "libcurl optional", deferred). Fix = reword to the accurate scope ("HTTPS update checks via WinHTTP on Windows; AI client transport not yet integrated"), **not** delete.
3. **REQ-EX-001 / REQ-EX-002 (item 1.4).** REQUIREMENTS.md marks both GAP ("no PIC_RunQueue call"). The calls now exist (`cpu_bridge.cpp:113,119`). But the C2 concurrency finding showed the linked `PIC_RunQueue` is a no-op stub (`audit-wiki/wiki/concepts/Vacuous Interrupt Delivery (C2).md`). So set these to **PARTIAL with a note** ("call present at cpu_bridge.cpp:113/119 but library build links a stub PIC; functional delivery is Sprint 6"), **not** a clean OK.

---

## Task 1 — Roadmap case collision + honest stamp (item 1.1)

**Files:** `ROADMAP.md`, `roadmap.md` (one to be removed from the index), new `scripts/check_case_collisions.py`, `.github/workflows/sprint2-checks.yml`.

- [ ] **1.1 Collapse the collision via git plumbing (NOT a filesystem rename — Windows is case-insensitive).** Keep `ROADMAP.md` as canonical; remove the lowercase path from the index: `git rm --cached roadmap.md` then commit. Verify `git ls-files | findstr /I roadmap` returns exactly `ROADMAP.md`.
- [ ] **1.2 Fix the false stamp in `ROADMAP.md`** header (the `Version: 4.2.0` / `Date: 2026-02-27` block is internally inconsistent with the June edits). Set the date to the real last-substantive-edit date and reconcile the version. Re-verify the "Phases -1,0,1,4 COMPLETE; 2,3 PARTIAL" line against the Sprint 0 reality and `TODO.md`.
- [ ] **1.3 Write `scripts/check_case_collisions.py`** — stdlib only, `argparse` `--path .` default, exit 0 clean / 1 on any two tracked paths differing only by case (read `git ls-files`, lowercase-key a dict, flag dups). Model on `scripts/check_conflict_markers.py` (same shape, stdlib, exit convention).
- [ ] **1.4 Wire it into `.github/workflows/sprint2-checks.yml`** as a new step in the existing `globals-registry` job (the job already runs `python scripts/check_*.py --path .` steps; no new setup needed). Prove it: run on HEAD (exit 0) and on a deliberately re-collided tree (exit 1) — capture both.

---

## Task 2 — Reconcile TODO / AUDIT / CHANGELOG (item 1.2)

**Files:** `TODO.md`, `AUDIT.md`, `CHANGELOG.md`. Evidence source (READ-ONLY): `audit-wiki/raw/backlog-miner-report.md`.

- [ ] **2.1 Kill the TODO.md done-and-missing contradictions.** Six confirmed REQ IDs appear as both `[x]` complete and as release-blocker/should-have table rows: REQ-MOUNT-001 (`TODO.md:90` vs `:167`), REQ-MOUNT-002 (`:91` vs `:168`), REQ-MENU-001 (`:75` vs `:169`), REQ-MAPPER-001 (`:82` vs `:183`), REQ-SAVE-003 (`:80` vs `:184`), REQ-CAPTURE-003 (`:87` vs `:185`). For each, verify the actual implementation file named in the `[x]` line exists at HEAD, then remove the stale blocker-table row (or mark it done) so each ID has ONE status.
- [ ] **2.2 Fix the IPC "STUB ONLY" label** at `TODO.md:257`. Ground truth: `src/legends_ipc/` is ~2,142 lines of real code (`framebuffer_shm.cpp`, `audio_ring.cpp`, `messages.cpp`); only `protocol.cpp` is a one-line stub. Reword to "transport + codec implemented (~2,100 LOC); `protocol.cpp` high-level state machine is a stub; end-to-end boot not wired (Sprint 3)".
- [ ] **2.3 Annotate `AUDIT.md`** with resolution status for all 30 prior findings from the verification matrix in `audit-wiki/raw/backlog-miner-report.md` (22 resolved / 8 open). Preserve original finding text; add a dated resolution column/section. This stops the duplicate-remediation trap (finding N5/doc-05).
- [ ] **2.4 Correct the CHANGELOG.md TLS line** (`CHANGELOG.md:36`) per Correction #2 — reword to the accurate WinHTTP-update-checker scope; cite `update_checker_win.cpp:37` (real) and `ai_http_client.cpp:212` (deferred). Do not claim a general TLS-verification feature.

---

## Task 3 — Demote Wasm to planned (item 1.3)

**Files:** `README.md`, `ARCHITECTURE.md`, `CMakeLists.txt` (comment only).

- [ ] **3.1 README.md:** reword `README.md:28` ("Wasm sandbox support …") to clearly-planned; the file-tree references at `:302-303,:309` already say "(planned)" — make the capability bullet consistent with that.
- [ ] **3.2 ARCHITECTURE.md:** the "Wasm Sandbox Architecture" section (`:611-717`, intro at `:19`) and the `wasm.md` requirements pointer (`:613`) describe artifacts that have **never existed in git history** (`git log --all -- wasm.md "wit/legends-emulator.wit"` is empty). Re-title/preface the section as planned/future; cite the git-history-empty evidence in the report. Do not delete the design content — mark it not-yet-implemented.
- [ ] **3.3 CMakeLists.txt:** `LEGENDS_BUILD_WASM` (`:38`, default OFF) and the `:455-494` block stay, but the comment should state the toolchain/artifacts are not present. No build-logic change.
- [ ] **3.4** Bounded by DECISION GATE 1.8 (Task 7) — but 3.1–3.3 proceed regardless.

---

## Task 4 — Re-verify REQUIREMENTS.md + re-baseline TLA conformance (item 1.4)

**Files:** `REQUIREMENTS.md`, `TLA_CONFORMANCE.md`. Status format is `**OK**` / `**GAP**` / `**PARTIAL**` table markers.

- [ ] **4.1 Re-verify each requirement status at HEAD and stamp `verified-at: <commit>`.** Confirmed stale samples to fix: REQ-EX-001/002 GAP→PARTIAL-with-note per Correction #3 (NOT clean OK); REQ-LC-005 still GAP (dual path real — `dosbox_context.cpp:920` stub vs `dosbox_library.cpp:371` bridge); REQ-LC-003 still GAP (handle fallback) — note Sprint 0's H5 fix is the in-process path, confirm current state; REQ-SR-001 stays PARTIAL (RAM/GPR/VGA serialization — but note Sprint 0 V5 work; re-check). Provide >=8 flipped statuses with source file:line in the handoff for the auditor's random re-check.
- [ ] **4.2 Re-baseline `TLA_CONFORMANCE.md`:** the concurrency audit found 4 of 5 previously non-conformant invariants fixed in code but undocumented (`audit-wiki/wiki/concepts/Determinism Oracle Weakness.md` and the concurrency source). Update the scorecard to HEAD; keep the genuinely-open ones (e.g. the determinism-hash gap) flagged.

---

## Task 5 — README API/error tables + ARCHITECTURE constants + honest badge (item 1.5)

**Files:** new `scripts/gen_readme_api_table.py`, `README.md`, `ARCHITECTURE.md`. Source of truth: `include/legends/legends_embed.h` (51 `LEGENDS_API` functions with Doxygen `@brief`; 14 `LEGENDS_ERR_*` macros + `LEGENDS_OK` at `:69-85`).

- [ ] **5.1 Write `scripts/gen_readme_api_table.py`** — stdlib only; parse the header's per-function Doxygen `@brief` and the error-code macros (`:69-85`); emit a deterministic markdown table for ALL public functions + all error codes. Re-running must produce byte-identical output (the auditor diffs two runs).
- [ ] **5.2 Insert the generated tables into README.md** (today it documents 23 of ~51 functions and 10 of 15 error codes). Mark the region as generated so future drift is mechanical to catch.
- [ ] **5.3 Replace the static "tests: 1500+ passing" badge** with a CI-generated badge or a link to the CI run (it is hardcoded shields.io markup; the real number is 4512 per Sprint 0's run, but a static count re-drifts — prefer generated/linked).
- [ ] **5.4 Fix ARCHITECTURE.md save-state constants** (`:195-215`): change `96 bytes`→`64`, `"LEGS"`/`0x4C454753`→`"DBXS"`/`0x53584244`, `version 2`→`3`, citing `legends_embed_api.cpp:100-101` and the `static_assert(...==64)` at `:225`. Fix the `cpu_bridge.cpp (stub)` label at `ARCHITECTURE.md:410` (the bridge is real — `cpu_bridge.cpp:113,119`), but keep it honest about the C2-vacuous nuance (call present, stub-linked).

---

## Task 6 — OpenSpec hygiene (item 1.6)

**Files:** `openspec/changes/**`, `openspec/changes/archive/` (empty), `openspec/specs/` (empty), new `scripts/check_openspec_staleness.py`, `sprint2-checks.yml`.

- [ ] **6.1 Archive completed changes.** 18 active change dirs exist; `archive/` and `specs/` are empty. The `phase-*` set (`phase-0-quick-wins` … `phase-iso-process-isolation`, Feb–Mar) is completed work; the 2026-06-08 set (`abi-parity-*`, `capability-truth-*`, `ipc-wire-*`, `runtimehost-*`) is in-progress. For each `phase-*` change, confirm its `tasks.md` is fully checked, then move it to `changes/archive/`. Do not archive the in-progress June changes.
- [ ] **6.2 Populate `openspec/specs/`** as the canonical baseline from the archived changes' specs (per the OpenSpec lifecycle in `openspec/project.md`).
- [ ] **6.3 Write `scripts/check_openspec_staleness.py`** (stdlib; flag changes whose tasks are 100% complete but still under `changes/`) and wire into `sprint2-checks.yml`. README describes OpenSpec as a quality gate — this makes that true.

---

## Task 7 — Decision gates: PREPARE, do not make (items 1.7, 1.8)

For both: produce a committed brief with facts (cited), options, recommendation, and the file-change blast radius. Change NO file whose content presupposes the outcome (mirrors how Sprint 0's LICENSE recorded SPDX facts while reserving the call).

- [ ] **7.1 `docs/superpowers/handoffs/decision-gpl-license.md`** (item 1.7): ~107 `src/` SPDX tags + upstream DOSBox-X say `GPL-2.0-or-later`; README/CONTRIBUTING say `-only`. Recommend `-or-later`. List every file each option would touch. Make ZERO SPDX edits.
- [ ] **7.2 `docs/superpowers/handoffs/decision-wasm.md`** (item 1.8): Wasm 0/50 since Feb. Options: fund a REQ-WASM-001..010 spike vs formally defer roadmap §15. Rough cost each; recommendation. Task 3 (demote-to-planned) is independent of this.

---

## New scripts — shared conventions (match `scripts/check_*.py`)

- `argparse` with `--path` / `-p` default `.`; stdlib only (no pyyaml) for the three new checks; exit `0` clean / `1` violations; print findings to stdout before `sys.exit()`. Wire all three into the `globals-registry` job in `.github/workflows/sprint2-checks.yml` as added steps (Python 3.11 + checkout already set up there). Do NOT touch the Sprint 0 gate logic in `ci.yml`.

---

## Constraints (hard)

- **Docs + scripts/CI-lint only.** `git diff master...HEAD -- src/ engine/` must be EMPTY. Do not change Sprint 0 CI gates.
- **`audit-wiki/` is READ-ONLY** — read as evidence, never modify (it is the auditor's record).
- **Every written status carries a HEAD file:line** — never from memory or the stale doc being replaced. Flag genuine unknowns as unverified rather than guessing.
- One conventional commit per task; no history rewrite/force-push; commit ALL deliverables (no untracked handoffs — Sprint 0's miss).

---

## Verification (end-to-end)

1. `python scripts/check_case_collisions.py --path .` → exit 0 on HEAD; exit 1 on a deliberately re-collided tree (show both).
2. `git ls-files` case-insensitive scan → no collisions; `git ls-files | findstr /I roadmap` → exactly one path.
3. `python scripts/gen_readme_api_table.py` twice → identical output (diff empty).
4. `python scripts/check_openspec_staleness.py --path .` → exit 0 (no completed-but-unarchived changes).
5. `actionlint .github/workflows/sprint2-checks.yml` → exit 0.
6. Grep cross-check: no REQ ID is both `[x]` and a blocker row in `TODO.md`.
7. `git diff master...HEAD -- src/ engine/ audit-wiki/` → all EMPTY.
8. Both decision briefs exist; `git diff` shows zero SPDX-header changes.

---

## Handoff note

Before handing to Codex, regenerate the Sprint 1 XML directive to fold in the three corrections above (roadmap de-dup-not-restore; CHANGELOG TLS reword-not-delete; REQ-EX-001/002 PARTIAL-not-OK) and to reference this plan's exact file:line targets. Auditor (Claude) will re-verify a random subset of the `claims_verified` array against source at HEAD, re-run the three new scripts, and confirm the `src/`+`engine/`+`audit-wiki/` diffs are empty.
