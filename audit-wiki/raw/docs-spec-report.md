# Documentation, Spec Drift & Licensing Audit — Project Legends

- **Auditor role:** Documentation, spec drift & licensing
- **Audit date:** 2026-06-09 (HEAD = `ef11f20`, last commit 2026-06-09)
- **Prior audit:** `C:\projectLegends\AUDIT.md` (2026-02-24, IDs C1-C2/H1-H9/M1-M11/L1-L8)
- **Scope:** README.md, ARCHITECTURE.md, REQUIREMENTS.md, TODO.md, DEPENDENCIES.md, CONTRIBUTING.md, RELEASING.md, AGENTS.md, CHANGELOG.md, openspec/, COPYING/LICENSE/NOTICE, GPL process-isolation design vs build reality.

---

## Executive summary

The documentation set splits into two eras. Material refreshed in the last sprint cycle is accurate — the README architecture diagram's counts verified exactly against source (50 `LEGENDS_API` functions in `include/legends/legends_embed.h`, 108 message types in `include/legends_ipc/message_types.h`, 89 structs in `include/legends_ipc/messages.h`, 43 `case MsgType::` in `src/engine_host/engine_dispatcher.cpp`), and RELEASING.md matches the actual `ci.yml` job set (sanitizers, fuzz, tlaplus, coverage, packaging-on-tag all present).

Everything else has drifted, in both directions. REQUIREMENTS.md (the EARS source of truth) still reports February GAP statuses for at least six requirements that have since been fixed in code. TODO.md simultaneously marks the same requirement IDs complete and missing. ARCHITECTURE.md documents a save-state format (96-byte header, "LEGS" magic, version 2) that contradicts both the README (64 bytes) and the code ("DBXS", version 3).

Licensing is the most serious area. The repo root contains a **plain MIT LICENSE file** purporting to cover "the Software" — a repo whose bulk is a vendored GPL DOSBox-X fork — while README calls that same file a "multi-component license overview." The project cannot decide whether it is GPL-2.0-only (README, NOTICE-adjacent docs, CONTRIBUTING) or GPL-2.0-or-later (every actual SPDX tag in `src/`, DEPENDENCIES.md). And the centerpiece "Wasm sandbox support" capability in README references a `wasm.md` and `wit/legends-emulator.wit` that **have never existed in git history**.

---

## Findings

### LIC-01 (CRITICAL) — Root `LICENSE` file is a bare MIT grant over a GPL codebase

**Evidence:**
- `C:\projectLegends\LICENSE:1-21` is the verbatim MIT license: *"Permission is hereby granted... to deal in the Software without restriction..."* with no component scoping whatsoever.
- `C:\projectLegends\README.md:312` describes it as `LICENSE # Multi-component license overview`; `README.md:367` repeats: *"LICENSE — Multi-component license overview"*.
- `C:\projectLegends\CHANGELOG.md` ("Unreleased / Added"): *"License files: COPYING (GPL v2), LICENSE (multi-component overview), NOTICE..."* — same false description.
- `C:\projectLegends\COPYING:1-2` is the full GNU GPL v2 text; `README.md:6` badges the project GPL-2.0.
- Introduced by commit `8e78bfe` ("Release A: security baseline, license files...") which added `LICENSE | 21 ++` — i.e., the MIT text, never an overview.

**Why it matters:** A root-level `LICENSE` containing only MIT text is what GitHub, SPDX scanners, and downstream package tooling read as the project license. It plausibly (mis)grants MIT terms over `engine/` — ~1M lines of vendored DOSBox-X code the project has no right to relicense (vendored files are GPL "version 2 ... or any later version", e.g. `engine/src/cpu/cpu.cpp:1-8`). This is a license-misrepresentation risk, not just doc drift.

**Recommendation (Effort S):** Replace `LICENSE` content with an actual multi-component overview (component → license → directory table, pointing at COPYING and the MIT-scoped dirs), or rename it `LICENSE.md` overview and ensure GitHub detection picks up COPYING. Fix the CHANGELOG/README descriptions in the same commit.

---

### LIC-02 (HIGH) — GPL-2.0-only vs GPL-2.0-or-later: docs and code disagree everywhere

**Evidence (the "-only" side):**
- `README.md:355`: *"Engine & core ... — GPL-2.0-only, consistent with DOSBox-X"*; `README.md:364`: `SPDX expression: GPL-2.0-only AND MIT`.
- `CONTRIBUTING.md:226-233` mandates the header `// SPDX-License-Identifier: GPL-2.0-only` for `engine/`, `src/legends/`, `src/engine_host/`, `src/pal/`, `include/legends/`, `include/pal/`.

**Evidence (the "-or-later" side):**
- SPDX tally in `src/`: **107 files tagged `GPL-2.0-or-later`, 18 MIT, zero `GPL-2.0-only`** (e.g. `src/app/application.cpp:1`, `src/engine_host/engine_dispatcher.cpp:1`). `include/` has 9 `GPL-2.0-or-later` and 11 MIT, zero `-only`.
- `DEPENDENCIES.md:18`: *"All dependencies are compatible with the project's GPL-2.0-or-later license."*
- Vendored upstream: `engine/src/cpu/cpu.cpp:4-7`: *"either version 2 of the License, or (at your option) any later version"* — so the README claim that GPL-2.0-only is "consistent with DOSBox-X" is factually wrong about upstream; DOSBox-X is GPL-2.0+.
- `include/legends/legends_embed.h:5-7` uses prose ("Licensed under GNU General Public License v2.0") with no SPDX tag at all.
- Side note: `engine/` contains no COPYING/LICENSE file of its own (only `AIBOX_README.md`, `LIBRARY_CONTRACT.md`); the root COPYING is the only GPL text shipped.

**Why it matters:** -only vs -or-later determines GPLv3 compatibility for every downstream embedder; the README's SPDX expression is contradicted by 100% of the project's own file tags. The CONTRIBUTING policy is enforced by no one and followed by no file.

**Recommendation (Effort M):** Decide once (note: a derivative of GPL-2.0+ upstream *may* be distributed as -only, but the simplest consistent choice is GPL-2.0-or-later matching the file tags and upstream), then align README, CONTRIBUTING, NOTICE, DEPENDENCIES.md, and add an SPDX tag to `legends_embed.h`. Add a CI lint that greps SPDX tags against the per-directory policy.

---

### LIC-03 (HIGH) — The "non-GPL shell" story glosses over the GPL-licensed API header and in-process GPL obligations

**Evidence:**
- `src/legends_proxy/proxy_api.cpp:1` is `// SPDX-License-Identifier: MIT`, and at line 6 does `#include <legends/legends_embed.h>` — a header the project itself declares GPL (`legends_embed.h:5-7` "Licensed under GNU General Public License v2.0"; `CONTRIBUTING.md:228-229` and `README.md:277-278` assign `include/legends/` GPL-2.0-only).
- `DEPENDENCIES.md:18`: *"The MIT-licensed IPC/proxy libraries (legends_ipc, legends_proxy) do not link any GPL code."* Build comments repeat this (`CMakeLists.txt:327`, `CMakeLists.txt:422`).
- `docs/design/GPL2_PROCESS_ISOLATION_DESIGN.md:5`: the shell is described as a *"proprietary application shell"* with *"zero GPL object code"* — yet `CONTRIBUTING.md:258` says `src/app/` is GPL-2.0-only and the actual shell files are tagged GPL-2.0-or-later (`src/app/application.cpp:1`). The shell cannot be simultaneously proprietary and GPL.
- The design doc (TDD-LIC-001) never discusses the license of `legends_embed.h` itself, even though both the MIT proxy and the "non-GPL" shell must compile against it. Compare: the IPC headers were deliberately MIT-tagged for exactly this reason (`include/legends_ipc/*.h:1`), but the API header the proxy *implements* was not.
- Embedder-facing docs gloss the in-process obligation: `README.md:29-30` advertises *"Stable C ABI for FFI from Rust, Python"* and the Quick Start (`README.md:154-185`) statically links the GPL core, with no statement that in-process embedding makes the embedder's program GPL-2.0. The only place this is stated is a table cell in `ARCHITECTURE.md:553` ("Monolithic ... Entire binary is GPL-2.0"). The README License section (351-364) describes only the IPC escape hatch.

**Why it matters:** The project's headline differentiator ("embed without GPL via IPC") rests on an unexamined assumption that compiling a proprietary shell + MIT proxy against a GPL-2.0-only header is fine. Whether or not that is legally defensible (API/fair-use arguments exist), the docs claim more than the licensing files deliver, and an embedder relying on DEPENDENCIES.md:18 would be misled.

**Recommendation (Effort M):** (1) Dual-license or MIT-license `legends_embed.h` explicitly (it is the project's own work, so this is possible) and say so in the design doc; (2) reconcile the design doc's "proprietary shell" with CONTRIBUTING's GPL assignment for `src/app/` (e.g., "shell is GPL in this repo; *third-party* shells may be non-GPL in IPC mode"); (3) add an explicit "GPL obligations when embedding in-process" paragraph to README's License section.

---

### DOC-01 (HIGH) — "Wasm sandbox support" is advertised as a capability; its artifacts have never existed

**Evidence:**
- `README.md:28` Capabilities list: *"Wasm sandbox support (headless Wasmtime/WASI target for sandboxed execution)"* — present tense, alongside shipped features.
- `README.md:302-303` project tree shows `wit/ ... legends-emulator.wit`; `README.md:309` shows `wasm.md`.
- `ARCHITECTURE.md:611-716` is a full "Wasm Sandbox Architecture" section: line 613 *"Requirements document: wasm.md"*, line 615 *"The project supports an optional Wasm/WASI build target"*, line 703 *"defined in wit/legends-emulator.wit"*, lines 715-716 *"CI enforces parity ... (REQ-WASM-026, REQ-WASM-040)"*.
- `CMakeLists.txt:452`: *"See wasm.md for full requirements and wit/ for the WIT interface definition"*; the `legends_wit_generate` custom target lists `SOURCES wit/legends-emulator.wit`.
- Reality: `wasm.md` and `wit/` do not exist at HEAD, and `git log --all -- wasm.md` / `git log --all -- wit` return **nothing** — they were never committed. Commit `092590d` ("Integrate Wasm sandbox requirements...") touched only ARCHITECTURE.md, CMakeLists.txt, README.md, roadmap.md.
- `TODO.md:20`: *"Wasm Sandbox | NOT STARTED | 0 of 50"*; `TODO.md:258`: *"Wasm sandbox | NOT STARTED — documentation only"*. No CI job mentions wasm.
- Partial mitigation attempt exists: commit `18c1cf3` "mark wasm.md as planned in README" added "(planned)" to one line (`README.md:309`) but left the Capabilities bullet (line 28), the ARCHITECTURE.md section, and the CMake comments claiming present-tense support.

**Why it matters:** This is the clearest truthfulness defect in the doc set: a capability bullet and a 100-line architecture section describing CI-enforced guarantees (REQ-WASM-026/040 parity) that have zero implementation, referencing requirement and interface files that were never written.

**Recommendation (Effort S for docs):** Move the Wasm material to a clearly-labeled "Planned / Design" section or `docs/design/`, delete the capability bullet (or mark "(planned, 0/50)"), and either commit a real `wit/legends-emulator.wit` stub or remove the dangling CMake target sources.

---

### DOC-02 (HIGH) — REQUIREMENTS.md status column is ~3.5 months stale; sampled statuses wrong in both directions

REQUIREMENTS.md (dated 2026-02-24, `REQUIREMENTS.md:4`) claims 22 OK / 4 PARTIAL / 24 GAP (`REQUIREMENTS.md:560`). Sampling 10 requirements at HEAD:

| Req | Doc claims | Reality at HEAD | Evidence |
|---|---|---|---|
| REQ-EX-001 (PIC_RunQueue) | GAP (`REQUIREMENTS.md:99`) | **Fixed** | `engine/src/misc/cpu_bridge.cpp:113` calls `PIC_RunQueue()` |
| REQ-EX-002 (CPU_Check_NMI) | GAP (`REQUIREMENTS.md:109`) | **Fixed** | `cpu_bridge.cpp:119` calls `CPU_Check_NMI()` |
| REQ-LC-003 (destroy invalid handle) | GAP (`REQUIREMENTS.md:56`) | **Fixed** | `src/legends/legends_embed_api.cpp:79-82` strict `handle == inst` match; `:966-968` returns `LEGENDS_ERR_NULL_HANDLE` |
| REQ-CF-002 (cycles validation) | GAP (`REQUIREMENTS.md:471`) | **Fixed** | `legends_embed_api.cpp:841-845` range check 100..1000000 |
| REQ-BQ-004 (requirements-dev.txt) | GAP (`REQUIREMENTS.md:523`) | **Fixed** | `C:\projectLegends\requirements-dev.txt` exists (`pyyaml>=6.0`) |
| REQ-CP-003 (framebuffer sync) | GAP (`REQUIREMENTS.md:355`) | **Substantially fixed** | `legends_embed_api.cpp:1626-1685` syncs display mode, palette, text buffer from engine (Phase -1 plumbing) |
| REQ-DT-004 (HashMode::Full) | GAP (`REQUIREMENTS.md:272`) | **Still open** | `engine/src/misc/state_hash_compat.cpp:48-50` still appends only `"FULL_MODE"` marker |
| REQ-SR-007 (reinterpret_cast) | GAP (`REQUIREMENTS.md:221`) | **Likely fixed** | only 1 `reinterpret_cast` remains in `legends_embed_api.cpp` (handle cast at `:1003`) |
| REQ-LC-001 (single instance) | OK | OK | `legends_embed_api.cpp:804` CAS confirmed |
| REQ-BQ-005 (test realism) | GAP (`REQUIREMENTS.md:533`) | **Changed shape** | `tests/unit/test_legends_embed.cpp:709-726` now exercises invalid handles for crash-safety, comment still tolerates "accept if handle validation is minimal" |

**Why it matters:** This is the document AUDIT.md says all findings were "translated to 50 EARS requirements" into. Planning from it today misallocates at least 6 of 24 GAP work items toward already-fixed code, and hides which GAPs (e.g. REQ-DT-004) genuinely remain.

**Recommendation (Effort M):** Re-verify all 50 statuses against HEAD, add a "Verified at commit" column, and date-stamp each status change. Consider generating status from test results where a test exists per requirement.

---

### DOC-03 (MEDIUM) — TODO.md contradicts itself and reality

**Evidence:**
- Same IDs both complete and missing: `TODO.md:78-92` mark `[x]` REQ-SAVE-003, REQ-MAPPER-001, REQ-CAPTURE-003, REQ-MOUNT-001/002, REQ-MENU-001; the **same IDs** reappear under "Not Yet Implemented — Must-Have/Should-Have" (`TODO.md:167-186`).
- IPC status stale in the pessimistic direction: `TODO.md:19` "GPL v2 Process Isolation | STUB | 2 of 16"; `TODO.md:257` "IPC isolation | STUB ONLY — src/legends_ipc/protocol.cpp is placeholder". At HEAD, `protocol.cpp` is indeed a 1-line stub, but ~2,700 lines of real IPC/proxy/host code exist (`src/legends_ipc/messages.cpp` 905 lines, `src/legends_proxy/proxy_api.cpp` 677, `src/engine_host/engine_dispatcher.cpp` 543), `ci.yml:95-126` runs a dedicated `linux-ipc` job, and `openspec/changes/phase-iso-process-isolation/tasks.md` shows Sprint-1 items checked.
- LICENSES/ never existed: `TODO.md:47` `[x] REQ-ISO-002 — NOTICE file, LICENSES/ directory` and `TODO.md:156` `[x] REQ-OPS-022 — LICENSES/ directory + NOTICE with SPDX`. `ls C:\projectLegends\LICENSES` → not found; `git log --all -- LICENSES` → empty. Both checkboxes are false.
- CI inventory stale: `TODO.md:240` ".github/workflows/*.yml | 6" — only 4 exist (`ci.yml`, `module-dag.yml`, `pal-ci.yml`, `sprint2-checks.yml`); `soak-nightly.yml`/`fuzz-nightly.yml` named at `TODO.md:136,138` were consolidated into `ci.yml`'s schedule trigger (`ci.yml:24-25`).

**Recommendation (Effort S):** Regenerate TODO.md from one pass over HEAD; delete the duplicated "Not Yet Implemented" rows; correct REQ-ISO-002/REQ-OPS-022 to unchecked or create the LICENSES/ directory they claim.

---

### DOC-04 (MEDIUM) — ARCHITECTURE.md serialization section contradicts both code and README (prior L2 only half-fixed)

**Evidence:**
- `ARCHITECTURE.md:195-198`: "SaveStateHeader (96 bytes) / magic: 0x4C454753 ('LEGS') / version: 2".
- Code: `src/legends/legends_embed_api.cpp:92-93`: `SAVESTATE_MAGIC = 0x53584244 // "DBXS"`, `SAVESTATE_VERSION = 3`.
- README (fixed by prior audit L2): `README.md:111` "SaveStateHeader (64 bytes)".
- Also stale: `ARCHITECTURE.md:410` labels `cpu_bridge.cpp` "# CPU bridge (stub)" — the bridge is real (`cpu_bridge.cpp:113-119`); the File Organization tree (`ARCHITECTURE.md:377-426`) omits `src/app/` (~70 files), `src/engine_host/`, `src/legends_proxy/`, `include/legends_ipc/` entirely, all of which exist and are documented elsewhere in the same file (lines 543-607).

**Prior-audit link:** L2 ("README says SaveStateHeader is 96 bytes") was marked resolved for README only; ARCHITECTURE.md retains the stale numbers plus a wrong magic and version.

**Recommendation (Effort S):** Single-source the format constants (generate the doc table from `static_assert`s or cite the header), sweep ARCHITECTURE.md for "stub" labels and the file tree.

---

### LIC-04 (MEDIUM) — NOTICE and DEPENDENCIES.md omit vendored stb and glad; NOTICE has none of the claimed SPDX content

**Evidence:**
- `external/` actually contains `glad/` (glad.c, glad/, KHR/) and `stb/` (`stb_truetype.h`, `stb_image_write.h`).
- Both are compiled into the app: `src/app/ttf_renderer.cpp` / `src/app/capture.cpp` use stb (TODO.md:107 itself says "ttf_renderer.cpp via stb_truetype"); `src/app/shader_renderer.cpp` uses glad.
- `NOTICE:1-46` lists 8 components (DOSBox-X, gsl-lite, SDL3, GoogleTest, Benchmark, FluidSynth, MUNT, zlib) — **no stb, no glad/KHR**. No license texts vendored anywhere (`NOTICE:46` defers to "individual project repositories").
- `DEPENDENCIES.md:5-11` table lists 5 dependencies — no stb, no glad, no zlib, no FluidSynth/MUNT.
- Claimed-but-absent NOTICE content: `README.md:313` "NOTICE # Copyright attributions + SPDX"; `CONTRIBUTING.md:245` "check the NOTICE file for per-directory license assignments"; CHANGELOG "NOTICE (copyright attributions and SPDX identifiers)". The actual NOTICE contains no SPDX identifiers and no per-directory assignments.

**Recommendation (Effort S):** Add stb (public domain/MIT dual) and glad/KHR (MIT/Apache-2.0) entries to NOTICE and DEPENDENCIES.md; either add the promised per-directory SPDX table to NOTICE or fix the three documents that claim it exists; ideally vendor license texts in the long-promised `LICENSES/` directory (closes the false TODO checkboxes too).

---

### SPEC-01 (MEDIUM) — GPL-isolation linker verification is documented as a CI gate but is never executed

**Evidence:**
- `ARCHITECTURE.md:606-607`: *"CI verifies this isolation by scanning the linker map (REQ-ISO-016)."*
- `docs/design/GPL2_PROCESS_ISOLATION_DESIGN.md:108-110`: *"Post-build step reads linker map file and fails if any GPL symbols appear in the shell binary."*
- The mechanism exists but is orphaned: `cmake/VerifyGPLIsolation.cmake:8` says "Usage: include(VerifyGPLIsolation) after defining the project_legends target", and `scripts/verify_gpl_isolation.py` exists — but `grep -r "include(VerifyGPLIsolation"` across CMakeLists.txt/cmake/ returns **nothing**, and no workflow in `.github/workflows/` references it (grep exit 1).
- The `linux-ipc` CI job (`ci.yml:95-126`) only verifies the IPC executables exist; it does not scan the map.

**Why it matters:** This is the *only* technical control backing the project's licensing claim that the shell binary contains "zero GPL object code." The docs assert it runs; it cannot run.

**Recommendation (Effort S):** Add `include(VerifyGPLIsolation)` after the `project_legends` target definition and assert in the `linux-ipc` job that the post-build verification ran (e.g., grep build log for "Verifying GPL isolation").

---

### SPEC-02 (MEDIUM) — OpenSpec change tracking never closes the loop: empty specs/, empty archive, completed changes still "active"

**Evidence:**
- `openspec/specs/` is **empty**; `openspec/changes/archive/` is **empty**.
- 17 active change directories include fully-completed February work: `openspec/changes/phase-0-quick-wins/.openspec.yaml` (`created: 2026-02-22`) with all tasks `[x]` in its tasks.md; `phase-a-cpu-bridge/tasks.md` all `[x]`; `phase-iso-process-isolation/tasks.md` Sprint 1 all `[x]`.
- Recent commits keep adding changes without archiving: `f128e6a` ("Plan quality gate sprint") added 3 change dirs, `274ef4d` added 3, `6900e7a` added 2 — `git log --name-status -- openspec` shows only `A` (additions), never moves to archive/ or specs/.
- Meanwhile `README.md:90-93` presents "OpenSpec, Graphify, CMake DAG, capability truth, CI, tests" as the project's "Quality and architecture gates".

**Why it matters:** With specs/ permanently empty, OpenSpec degenerates into a write-only proposal folder; there is no canonical spec to diff changes against, which is the entire point of the tool, and the README oversells it as a live gate.

**Recommendation (Effort S):** Run the archive step for the ~5 completed phase-* changes (populating `openspec/specs/`), and add a lightweight CI check that fails when a change dir has all tasks checked for >30 days without archival.

---

### DOC-05 (LOW) — README API Reference covers 23 of 50 exported functions; error table omits 5 codes (prior L1 still open)

**Evidence:**
- `include/legends/legends_embed.h` exports exactly **50** `LEGENDS_API` functions (verified by grep count); README's API tables (`README.md:191-243`) document **23**. Undocumented families include `legends_mount_drive` (header `:676`), `legends_ipx_*` (`:878-912`), `legends_glide_*` (`:928-941`), `legends_set_machine_pc98` (`:961`), plus audio/MIDI/capability/printer APIs.
- README error table (`README.md:249-259`) omits `LEGENDS_ERR_ALREADY_CREATED (-3)`, `INVALID_CONFIG (-7)`, `IO_FAILED (-10)`, `NOT_SUPPORTED (-12)`, `INTERNAL (-13)` — all defined at `legends_embed.h:74-84`. (The codes it does list match the header.)
- Related minor inaccuracy: `CONTRIBUTING.md:148` says the API returns `legends_status_t`; the actual type is `legends_error_t` (`legends_embed.h:72ff`).
- `CHANGELOG.md` still says "Embeddable C API ... with 22+ functions".

**Prior-audit link:** L1 ("README documents ~18 of 22 API functions") — confirmed-open; the ratio worsened (23/50) because the API grew faster than the docs.

**Recommendation (Effort S):** Generate the README API table from the header (a 20-line script), or at minimum add the mount/device/capability families and the 5 missing error codes; fix `legends_status_t` → `legends_error_t`.

---

## Prior AUDIT.md findings re-checked (doc/licensing scope)

| Prior ID | Status at HEAD | Evidence |
|---|---|---|
| L1 (README API coverage) | **Open / worse ratio** — 23 of 50 documented | DOC-05 above |
| L2 (SaveStateHeader doc size) | **Half-fixed** — README fixed (64 B); ARCHITECTURE.md still 96 B + wrong magic/version | DOC-04 above |
| L7 (undeclared pyyaml) | **Resolved** — `requirements-dev.txt` exists with `pyyaml>=6.0`; but REQUIREMENTS.md REQ-BQ-004 still claims GAP | DOC-02 above |
| H5 (destroy fallback) | **Resolved in code** (`legends_embed_api.cpp:79-82,966-968`); REQUIREMENTS.md REQ-LC-003 still claims GAP | DOC-02 above |
| C2 (PIC_RunQueue/NMI) | **Resolved in code** (`cpu_bridge.cpp:113,119`); REQUIREMENTS.md REQ-EX-001/002 still claim GAP | DOC-02 above |
| H7 (HashMode::Full) | **Still open** (`state_hash_compat.cpp:48-50`) — REQUIREMENTS.md REQ-DT-004 correct | DOC-02 above |
| H8 (frame capture decoupled) | **Substantially resolved** (`legends_embed_api.cpp:1626-1685`); REQUIREMENTS.md REQ-CP-003 stale | DOC-02 above |

## What is accurate (verified, no finding)

- README architecture diagram counts: 50 C APIs, 108 msg types, 89 structs, 43 dispatcher cases — all exact matches at HEAD.
- RELEASING.md vs `ci.yml`: packaging on `v[0-9]*` tags via cpack (`ci.yml:21,765-833`), sanitizer matrix (`ci.yml:328-362`), fuzz (`:470`), tlaplus (`:550`), coverage (`:674`) all present.
- CONTRIBUTING.md CMake option table matches `CMakeLists.txt` options (incl. `LEGENDS_USE_IPC:37`, `LEGENDS_BUILD_WASM:38`).
- AGENTS.md documents local Graphify tooling only; no truth claims about the codebase to audit.

## Sprint suggestions

1. **Licensing reconciliation sprint (1 week):** LIC-01 + LIC-02 + LIC-04 + the LICENSES/ directory TODO.md already claims exists. One commit series: rewrite LICENSE as a real overview, pick -only vs -or-later and align all five documents + add SPDX to `legends_embed.h`, attribute stb/glad, vendor license texts under `LICENSES/`, add an SPDX-policy CI lint.
2. **Make the isolation claim enforceable (2-3 days):** LIC-03 + SPEC-01. Dual-license `legends_embed.h`, fix the "proprietary shell" vs "GPL src/app" contradiction in TDD-LIC-001/CONTRIBUTING, wire `VerifyGPLIsolation.cmake` into the IPC build and the `linux-ipc` CI job, and add the in-process GPL-obligations paragraph to README.
3. **Doc-truth sweep (3-5 days):** DOC-01 + DOC-02 + DOC-03 + DOC-04 + DOC-05. Demote Wasm to "planned", re-verify all 50 EARS statuses at HEAD with a verified-at commit column, regenerate TODO.md, fix ARCHITECTURE.md constants and file tree, generate the README API table from the header.
4. **OpenSpec hygiene (1-2 days):** SPEC-02. Archive completed phase-* changes, populate `openspec/specs/`, add a staleness check so the "quality gate" claim in README becomes true.
