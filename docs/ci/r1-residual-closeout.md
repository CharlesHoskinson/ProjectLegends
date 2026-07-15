# R1 residual closeout tracker

## P1–P4 implementation (this track)

| Priority | Issue | Action |
|----------|--------|--------|
| **P1** | #43 | **Removed** vendored FluidSynth 1.1.6-noglib tree + headers. MIDI softsynth requires `C_FLUIDSYNTH` + system/FetchContent **v2.5.2**. Emptied `osv-scanner.toml` ignores. |
| **P2** | #42 | SBOM generator inventories all FetchContent pins + every `engine/src/libs/**` tree (with `linked-default` property). |
| **P3** | #44 | gsl-lite v1.1.0 still emits C4875 under MSVC 19.51+/WX (audit F019). **`/wd4875` re-attached only to the third-party `gsl-lite` INTERFACE target** in `cmake/dependencies.cmake` — not project-global. #44 reopened until upstream pin drops C4875. |
| **P4** | #40 | MSan remains absent; `ci.yml` matrix comment + `docs/ci/msan-reentry.md` gate re-entry. |

## Runtime green (pre-P1) reference

`621a099` / run [29440398476](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29440398476): ASan/UBSan/TSan/Fuzz/Windows success.

## Open issues after this PR

| ID | Expected state |
|----|----------------|
| #43 | **Close** when CI green after tree removal + empty ignores |
| #42 | **Partial / close if inventory accepted** — generator covers all libs dirs; refine versions later |
| #44 | **Close** when Windows green without `/wd4875` |
| #40 | **Remain open** (parked MSan) |

## Closed earlier

#38 atomic, #39 mutex breadcrumb, #45 TSan skips, #47 ASan, #48 Windows IPC lane.
