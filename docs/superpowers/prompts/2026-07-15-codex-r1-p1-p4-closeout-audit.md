# Independent audit brief — R1 P1–P4 residual closeout

**For:** Codex (GPT-5.6 or later), independent senior security / correctness / CI auditor  
**Mode:** Adversarial. Do **not** trust agent chat, closed-issue comments, or residual trackers without primary evidence.  
**Authority:** Live GitHub Actions logs, `gh` API, and `git show origin/master` over narrative docs.  
**Write-only:** Produce a review under `docs/superpowers/reviews/`. Do **not** modify product code, workflows, tests, or issues unless the user separately authorizes fixes.

---

## 0. Mission

Verify whether **P1–P4 residuals** claimed after R1 mandatory-lane green are **actually complete** on a single synchronized `origin/master` SHA:

| Priority | Claim | Issue |
|----------|--------|-------|
| **P1** | Vendored FluidSynth 1.1.6-noglib **removed**; no `osv-scanner.toml` FluidSynth CVE ignores | #43 |
| **P2** | SBOM covers FetchContent pins + **all** `engine/src/libs/**` trees | #42 |
| **P3** | **No** `/wd4875` / `legends_gsl_msvc_options`; Windows builds under `/WX` with gsl-lite v1.1.0 | #44 |
| **P4** | MSan remains **absent** and re-entry is gated by checklist only | #40 |

Also re-confirm **mandatory runtime lanes** (ASan, UBSan, TSan, Fuzz, Windows) are still green on the same SHA (no regression from FluidSynth deletion).

Issue a **GO / NO-GO** for “P1–P4 residual closeout on master.”

---

## 1. Pin the tree

```bash
cd C:\ProjectLegends   # or /path/to/ProjectLegends
git fetch origin master
export AUDITED_SHA=$(git rev-parse origin/master)
echo "AUDITED_SHA=$AUDITED_SHA"
git log -12 --oneline origin/master
```

**Agent-claimed tip (re-resolve; do not trust if tip moved):**

| Field | Value |
|-------|--------|
| Claimed SHA | `d989ebda1b45e6256ecce23167b12072f7537b31` |
| Subject | `fix(security): remove vendored FluidSynth (#43); expand SBOM; drop /wd4875` |
| Prior runtime-green SHA | `621a099944f5c7d82ed1a00c607a57fbc959b4c7` / run [29440398476](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29440398476) |
| CI for claimed tip (re-query) | [29443440591](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29443440591) |

If CI for `AUDITED_SHA` is incomplete, mark affected gates **UNPROVEN** and default **NO-GO**.

---

## 2. Absolute paths (Windows host)

### This brief
```text
C:\ProjectLegends\docs\superpowers\prompts\2026-07-15-codex-r1-p1-p4-closeout-audit.md
```

### Prior audits (context only)
```text
C:\ProjectLegends\docs\superpowers\reviews\2026-07-15-codex-r1-master-closeout-audit.md
C:\ProjectLegends\docs\superpowers\prompts\2026-07-15-codex-r1-master-closeout-audit.md
C:\ProjectLegends\docs\superpowers\prompts\2026-07-15-codex-r1-reproof-pack.md
```

### Surfaces under review
```text
C:\ProjectLegends\.github\workflows\ci.yml
C:\ProjectLegends\osv-scanner.toml
C:\ProjectLegends\scripts\generate_vendored_sbom.py
C:\ProjectLegends\docs\ci\vendored-sbom.cdx.json
C:\ProjectLegends\docs\ci\seed-known-vuln.cdx.json
C:\ProjectLegends\docs\ci\msan-reentry.md
C:\ProjectLegends\docs\ci\r1-residual-closeout.md
C:\ProjectLegends\cmake\dependencies.cmake
C:\ProjectLegends\CMakeLists.txt
C:\ProjectLegends\engine\src\gui\midi.cpp
C:\ProjectLegends\engine\src\gui\midi_synth.h
C:\ProjectLegends\engine\src\dosbox.cpp
C:\ProjectLegends\engine\src\libs\          # fluidsynth/ must be absent
C:\ProjectLegends\engine\include\          # fluidsynth.h / fluidsynth/ must be absent
C:\ProjectLegends\openspec\changes\ci-stabilize-mandatory-lanes\tasks.md
C:\ProjectLegends\CI-THESIS.md
```

### Deliverable
```text
C:\ProjectLegends\docs\superpowers\reviews\YYYY-MM-DD-codex-r1-p1-p4-closeout-audit.md
```

---

## 3. Acceptance contract

### 3.1 Mandatory runtime lanes (no regression)

On **one** completed CI run for `AUDITED_SHA`:

| Job | Pass |
|-----|------|
| `address Sanitizer` | success |
| `undefined Sanitizer` | success |
| `thread Sanitizer` | success; no `WARNING: ThreadSanitizer` / `SUMMARY: ThreadSanitizer` |
| `Fuzz Testing` | success |
| `Windows (MSVC)` | success (build **and** tests) |
| `Dependency Scan` | success (see 3.2) |

Hard rule: any red mandatory lane → **NO-GO**.

### 3.2 P1 — FluidSynth security (#43)

| Check | Pass criterion |
|-------|----------------|
| Tree deleted | `engine/src/libs/fluidsynth` **does not exist** |
| Headers deleted | `engine/include/fluidsynth.h` and `engine/include/fluidsynth/` **do not exist** |
| No 1.1 inventory | SBOM has **no** FluidSynth version starting with `1.1` |
| No ignores | `osv-scanner.toml` has **no** `[[IgnoredVulns]]` (or none for FluidSynth/CVE-2021-21417/CVE-2025-56225/DEBIAN-CVE-*) |
| CI guard | Workflow asserts tree absence + empty ignores (or equivalent fail-closed check) |
| Optional path | If `LEGENDS_ENABLE_FLUIDSYNTH=ON`, only system/FetchContent modern pin (e.g. v2.5.2+); never vendored 1.1.6 |
| Legacy code | `midi_synth.h` / `midi.cpp` do not include deleted in-tree headers on default Windows without `C_FLUIDSYNTH` |
| Issue | #43 closed **only if** tree gone + ignores empty + Dependency Scan green on same SHA |

### 3.3 P2 — SBOM coverage (#42)

| Check | Pass criterion |
|-------|----------------|
| Generator | `python3 scripts/generate_vendored_sbom.py --check` passes in CI or locally on the SHA |
| Pins | All `LEGENDS_DEP_*_TAG` in `dependencies.cmake` are mapped or explicitly rejected |
| Trees | Every top-level dir under `engine/src/libs/` that still exists appears in SBOM (or document why not) |
| FluidSynth | No phantom 1.1.6; optional pin may be 2.5.x only |
| zmbv | Present if still linked in `legends_app` |
| mt32emu | Present as FetchContent pin if still declared |
| Linked honesty | `linked-default` (or equivalent) distinguishes default-linked vs tree-present-only |

### 3.4 P3 — MSVC `/wd4875` removal (#44)

| Check | Pass criterion |
|-------|----------------|
| No interface | `legends_gsl_msvc_options` **absent** from `CMakeLists.txt` |
| No flag | no `/wd4875` compile option remains |
| Windows green | `Windows (MSVC)` success on `AUDITED_SHA` with gsl-lite v1.1.0 |
| Issue | #44 closed only with Windows job URL on that SHA |

### 3.5 P4 — MSan parked (#40)

| Check | Pass criterion |
|-------|----------------|
| Matrix | sanitizer list is exactly address, undefined, thread (no memory) |
| Docs | `docs/ci/msan-reentry.md` lists concrete re-entry criteria |
| Issue | #40 remains **OPEN** (parked is correct; closing would be wrong) |
| No mute | no `allow_failure` for a memory lane |

### 3.6 Explicit non-requirements

- Full MIDI softsynth feature re-enabled with FluidSynth in CI (default OFF is OK).  
- Perfect semver for every vendored tree (coarse `vendored` may pass if paths are complete).  
- Branch protection / R2 merge binding.

---

## 4. Evidence procedures (E-suite)

| ID | Procedure |
|----|-----------|
| **E1** | Pin `origin/master`; list last 12 commits. |
| **E2** | Latest completed CI run for `AUDITED_SHA` via `gh`; record run URL + conclusion. |
| **E3** | Job conclusions: ASan, UBSan, TSan, Fuzz, Windows, Dependency Scan + job URLs. |
| **E4** | TSan log: C++23 PASS; 0 TSan warnings; empty active race suppressions in `tsan-suppressions.txt`. |
| **E5** | Windows log: no C2220/C4875 build failures; tests ran. |
| **E6** | Dependency Scan log: tree-gone assert; no IgnoredVulns for FluidSynth; production exit 0; seed fixture still fails closed. |
| **E7** | Static: `test ! -e engine/src/libs/fluidsynth` and `! -e engine/include/fluidsynth/version.h`. |
| **E8** | Static: `rg '\[\[IgnoredVulns\]\]|CVE-2021-21417|CVE-2025-56225' osv-scanner.toml` — no active ignores (comments OK). |
| **E9** | Static: `rg 'wd4875|legends_gsl_msvc' CMakeLists.txt` — no functional disable. |
| **E10** | `python3 scripts/generate_vendored_sbom.py --check`; list components; assert no 1.1.x fluidsynth; assert libs dirs covered. |
| **E11** | `ls engine/src/libs` vs SBOM `legends:source-path` / names — every present top-level dir accounted for. |
| **E12** | Issues: `gh issue view` for #40,#42,#43,#44 — states match claims. |
| **E13** | OpenSpec tasks / residual tracker / CI-THESIS do not claim FluidSynth ignores or `/wd4875` still required. |
| **E14** | Optional: local WSL headless configure after tree deletion succeeds. |
| **E15** | Adversarial: `LEGENDS_ENABLE_FLUIDSYNTH=ON` path cannot revive 1.1.6 sources. |

---

## 5. Adversarial probes

1. **Ignore theater:** Could Dependency Scan pass with empty ignores while 1.1.6 sources still exist somewhere under `engine/`?  
2. **Header leftovers:** Any `#include "fluidsynth.h"` path that still resolves in-tree on Windows default build?  
3. **SBOM theater:** Inventory lists `fluidsynth@2.5.2` while default CI never FetchContents it — is that labeled optional/honest?  
4. **P3 regression:** Windows green only because warnings are not errors on some target? Confirm `/WX` still on Tier A.  
5. **MSan sneak:** Any workflow reintroduces memory sanitizer?  
6. **Issue honesty:** Were #42/#43/#44 closed before CI for `d989ebd` completed? Flag premature close.

---

## 6. Scoring (1–5)

| Dimension | 5 means |
|-----------|---------|
| Security | No 1.1.6 tree; no CVE ignores for removed package; optional modern pin only |
| Correctness | All mandatory lanes green on audited SHA |
| Maintainability | No warning suppress for gsl; SBOM generator fail-closed |
| Documentation honesty | Closed issues match live evidence; residual tracker current |
| CI/CD integrity | Fail-closed dep-scan guards; seed still works |
| Process/governance | #40 correctly open; no allow_failure |

---

## 7. Deliverable structure

`docs/superpowers/reviews/YYYY-MM-DD-codex-r1-p1-p4-closeout-audit.md`

1. Header table (AUDITED_SHA, run URL, model)  
2. Executive summary — **PASS/FAIL**, **GO/NO-GO**, finding counts  
3. Dimension scorecard  
4. Method  
5. Mandatory gate matrix  
6. P1–P4 matrix  
7. Issue state matrix (#40/#42/#43/#44)  
8. Findings (new F-IDs if needed)  
9. E-suite results  
10. Verdict block:

```text
P1 FluidSynth remove+drop ignores: PASS | FAIL | UNPROVEN
P2 SBOM libs inventory: PASS | FAIL | UNPROVEN
P3 no /wd4875 + Windows green: PASS | FAIL | UNPROVEN
P4 MSan parked: PASS | FAIL
Mandatory runtime lanes: PASS | FAIL | UNPROVEN
OVERALL: GO | NO-GO
```

11. Ordered fixes if NO-GO  

---

## 8. Quick start commands

```bash
cd C:\ProjectLegends
git fetch origin master
$sha = git rev-parse origin/master
gh run list --branch master --workflow CI --limit 5 `
  --json databaseId,headSha,conclusion,status,url

# Tree gone?
Test-Path engine\src\libs\fluidsynth
Test-Path engine\include\fluidsynth\version.h

# Ignores / wd4875
Select-String -Path osv-scanner.toml -Pattern 'IgnoredVulns|CVE-2021|CVE-2025-56225'
Select-String -Path CMakeLists.txt -Pattern 'wd4875|gsl_msvc'

python scripts/generate_vendored_sbom.py --check
Get-ChildItem engine\src\libs -Directory | ForEach-Object Name

gh issue list --state all --search "42 OR 43 OR 44 OR 40 in:title" --limit 10
```

---

## 9. Paste for Codex

```text
You are an independent adversarial auditor.

Follow every section of:
C:\ProjectLegends\docs\superpowers\prompts\2026-07-15-codex-r1-p1-p4-closeout-audit.md

Repo: C:\ProjectLegends
Pin origin/master first. Prefer live gh Actions evidence.
Write ONLY:
C:\ProjectLegends\docs\superpowers\reviews\YYYY-MM-DD-codex-r1-p1-p4-closeout-audit.md
Do not modify product code or issues.
Default to NO-GO if CI for the audited SHA is incomplete or any mandatory lane is red.
```

---

## 10. Distrust list (agent marketing)

- “#43 closed because tree deleted” — prove CI green + tree absence on **same** SHA.  
- “#44 closed” — prove Windows success **without** `/wd4875` on that SHA.  
- “SBOM complete” — every existing `engine/src/libs/*` dir accounted for.  
- “R1 fully closed including MSan” — **false**; #40 must stay open.  
- Runtime green on `621a099` does **not** prove P1 tree deletion on `d989ebd`.

**End of brief.**
