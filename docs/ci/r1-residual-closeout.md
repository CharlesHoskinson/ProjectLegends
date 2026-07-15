# R1 residual closeout tracker

## Synchronized green (runtime) — `621a099` / run 29440398476

https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29440398476

| Gate | Result |
|------|--------|
| ASan / UBSan / TSan | success (4512/4512); empty race suppressions |
| Fuzz | success |
| Windows (MSVC) | success (4500/4500) |
| Dependency Scan | success mechanically; F017 semantic fix in follow-up commit |

Codex re-audit NO-GO on `621a099` for **F017** (FluidSynth generic purl → empty OSV; mt32 pin omitted) and doc honesty.

## F017 remediation (this track)

| Item | Action |
|------|--------|
| FluidSynth PURL | `pkg:deb/debian/fluidsynth@1.1.6` (OSV matches DEBIAN-CVE-*) |
| #43 ignores | CVE + DEBIAN-CVE + DLA + CVE-2025-68617 family |
| Positive control | CI bare FluidSynth scan must detect DEBIAN-CVE-2021-21417 & DEBIAN-CVE-2025-56225 |
| mt32emu | Inventoried from `LEGENDS_DEP_MT32EMU_TAG` |
| Dead pin | `LEGENDS_DEP_FLUIDSYNTH_TAG` documented unused |

## Issue state

| ID | State | Note |
|----|--------|------|
| #38 | closed | atomic; proven TSan green |
| #39 | open → close after F017 commit CI green with TSan still clean | mutex fix proven on 621a099 |
| #40 | open | MSan park |
| #42 | open | full tree SBOM still future |
| #43 | open | upgrade then drop ignores |
| #44 | open | scoped `/wd4875` still present |
| #45 #47 #48 | closed | lane complete |

## Prior NO-GO audits

- Closeout NO-GO `42c30c4` / 29437942535 — F013/F014  
- Re-proof NO-GO `621a099` / 29440398476 — F017 only (runtime green)
