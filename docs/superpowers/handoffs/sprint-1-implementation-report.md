# Sprint 1 Implementation Report - Truthful Record

Started UTC: 2026-06-10T06:57:16.2612937Z  
Finished UTC: 2026-06-10T07:30:48.4142533Z  
Branch: `sprint-1/truthful-record`  
Base: `866a24daee96302713a3f904603eaa457c3407f0`

## Kickoff

Committed `docs/superpowers/handoffs/sprint-1-kickoff.json` first as required.

- Commit: `8cb5818b27389c6144636e77c9250d29f3682655`

## Item 1.1 - Roadmap Case Collision and Stamp

Status: complete  
Commit: `a2268bce03b0af01b653b012768df5dfaf9e8a46`

Files changed:

- `ROADMAP.md:4-15`
- `roadmap.md` removed from the index
- `scripts/check_case_collisions.py:1-97`
- `.github/workflows/sprint2-checks.yml:59-60`

Evidence:

```text
python scripts\check_case_collisions.py --path .
exit 0
OK: No case-insensitive path collisions found in 2324 git index path(s).
```

```text
deliberately collided git index
exit 1
Collision group:
  ROADMAP.md
  roadmap.md
Found 1 collision group(s) in 2 git index path(s).
```

## Item 1.2 - TODO/AUDIT/CHANGELOG Reconciliation

Status: complete  
Commit: `17574c133e77592657ab2634080ded059d4bb39d`

Files changed:

- `TODO.md:15-21`, `TODO.md:75-91`, `TODO.md:251`
- `AUDIT.md:47-92`
- `CHANGELOG.md:36-38`

Notes:

- The six done-and-blocker contradictions were removed from open blocker rows while preserving their checked implementation entries.
- `src/legends_ipc/` was reworded as partial real IPC work, with `protocol.cpp` still stubbed.
- Prior audit finding resolution status was added as 22 resolved / 8 open.
- TLS wording was narrowed: update checker HTTPS is real, AI client transport remains deferred.

Evidence:

```text
TODO.md:75:- [x] REQ-MENU-001 ...
TODO.md:80:- [x] REQ-SAVE-003 ...
TODO.md:87:- [x] REQ-CAPTURE-003 ...
TODO.md:90:- [x] REQ-MOUNT-001 ...
CHANGELOG.md:37: requests (`src/app/update_checker_win.cpp:46`); AI HTTP client transport is
AUDIT.md:52:Sprint 1 base. Tally: **22 resolved / 8 open**.
```

## Item 1.3 - Wasm Demotion to Planned

Status: complete  
Commit: `9cd8d1778d2c03e7a67b46de5036b77fceb3b577`

Files changed:

- `README.md:28`, `README.md:325-327`
- `ARCHITECTURE.md:19`, `ARCHITECTURE.md:611-722`
- `CMakeLists.txt:451-453`

Evidence:

```text
git log --all -- wasm.md "wit/legends-emulator.wit"
exit 0
<no output>
```

## Item 1.4 - Requirements and TLA Rebaseline

Status: complete  
Commit: `0b07b5d1abf7bf424bbac2e1f80db722fd724ea5`

Files changed:

- `REQUIREMENTS.md:1-566`
- `TLA_CONFORMANCE.md:1-338`

Notes:

- `verified-at` stamped to `9cd8d1778d2c03e7a67b46de5036b77fceb3b577`.
- `REQ-EX-001` and `REQ-EX-002` are PARTIAL, not OK: calls exist, but library-mode PIC links a stub.
- Summary is 42 OK / 6 PARTIAL / 2 GAP.

Representative flipped or reverified statuses:

- `REQUIREMENTS.md:49` `REQ-LC-003` = OK; source `src/legends/legends_embed_api.cpp:87-90`
- `REQUIREMENTS.md:68` `REQ-LC-005` = GAP; source `engine/src/misc/dosbox_context.cpp:973-976`
- `REQUIREMENTS.md:92` `REQ-EX-001` = PARTIAL; source `engine/src/misc/cpu_bridge.cpp:113`, `engine/src/cpu/cpu_library_stubs.cpp:56-60`
- `REQUIREMENTS.md:102` `REQ-EX-002` = PARTIAL; source `engine/src/misc/cpu_bridge.cpp:119`
- `REQUIREMENTS.md:122` `REQ-EX-004` = OK; source `src/legends/legends_embed_api.cpp:1017`
- `REQUIREMENTS.md:142` `REQ-EX-006` = OK; source `src/legends/legends_embed_api.cpp:1095`
- `REQUIREMENTS.md:166` `REQ-SR-002` = OK; source `engine/include/dosbox/engine_state.h:393`
- `REQUIREMENTS.md:349` `REQ-CP-003` = OK; source `src/legends/legends_embed_api.cpp:1633`

## Item 1.5 - README/API Tables and Architecture Constants

Status: complete  
Commit: `2175563e2e4bb71d75f02315627bbab592950f34`

Files changed:

- `scripts/gen_readme_api_table.py:1-131`
- `README.md:8`, `README.md:191-267`
- `ARCHITECTURE.md:195-197`, `ARCHITECTURE.md:410`

Notes:

- `include/legends/legends_embed.h` currently has 50 `LEGENDS_API` functions, not 51; the generated README table records the source-truth count.

Evidence:

```text
git diff --no-index -- C:\tmp\sprint1-api-table-1.md C:\tmp\sprint1-api-table-2.md
exit 0
<no output>
```

## Item 1.6 - OpenSpec Hygiene

Status: complete  
Commit: `d1879dbfa73aeb5f62560b6bbbd0a3135dc98452`

Files changed:

- `scripts/check_openspec_staleness.py:1-98`
- `.github/workflows/sprint2-checks.yml:62-63`
- Moved completed non-protected changes into `openspec/changes/archive/`
- Added baseline specs under `openspec/specs/`

Archived changes:

- `ci-stabilization-and-coverage-control` (29 checked / 0 unchecked)
- `phase-0-quick-wins` (18 checked / 0 unchecked)
- `phase-a-cpu-bridge` (19 checked / 0 unchecked)
- `phase-c-context-unification` (18 checked / 0 unchecked)

Evidence:

```text
python scripts\check_openspec_staleness.py --path .
exit 0
OK: no completed non-protected OpenSpec changes remain active.
INFO: protected active June 2026 change(s) left unarchived by directive:
  - runtimehost-adoption-next-slice: 28 checked task(s), 0 unchecked
  - runtimehost-app-service-adoption: 12 checked task(s), 0 unchecked
  - runtimehost-savemanager-adoption: 14 checked task(s), 0 unchecked
```

## Item 1.7 - GPL Decision Brief

Status: decision-prepared  
Commit: `48e976fa1cd9d617a7568ce9cebbbb533e7e0c97`

Files changed:

- `docs/superpowers/handoffs/decision-gpl-license.md:1-273`

Notes:

- No SPDX headers were changed.
- Recommendation prepared: choose `GPL-2.0-or-later`.
- Implementer did not make the owner decision.

## Item 1.8 - Wasm Decision Brief

Status: decision-prepared  
Commit: `d9e81da905c2234b69a53340b1c2ea2ad9002617`

Files changed:

- `docs/superpowers/handoffs/decision-wasm.md:1-81`

Notes:

- Recommendation prepared: formally defer roadmap section 15 unless an immediate `REQ-WASM-001..010` spike is funded.
- Implementer did not make the owner decision.

## Final Verification

```text
C:\Users\charl\AppData\Local\Microsoft\WinGet\Packages\rhysd.actionlint_Microsoft.Winget.Source_8wekyb3d8bbwe\actionlint.exe .github/workflows/sprint2-checks.yml
exit 0
<no output>
```

```text
git diff master...HEAD -- src/ engine/
exit 0
<no output>
```

```text
git diff master...HEAD -- audit-wiki/
exit 0
<no output>
```

```text
cmd.exe /c "git ls-files | findstr /I roadmap"
exit 0
ROADMAP.md
```

```text
TODO contradiction scan
exit 0
OK: no REQ ID is both done and an open blocker row in TODO.md.
```

```text
SPDX header diff scan
exit 0
OK: no SPDX header changes in source/build/script paths.
```

## Known Limitation

The committed machine handoff cannot contain the SHA of the commit that contains itself without changing that SHA. The `repo.head_commit` field records the last implementation commit before the final handoff commit, and the JSON `known_limitations` field states this explicitly. All handoff deliverables are still committed, and the final tree is expected to be clean after the handoff commit.
