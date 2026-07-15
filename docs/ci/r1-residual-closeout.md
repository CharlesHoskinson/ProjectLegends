# R1 residual closeout tracker

Post-merge of PR [#46](https://github.com/CharlesHoskinson/ProjectLegends/pull/46) onto `master`.

## Codex re-audit (NO-GO at `42c30c4`)

Full report: `docs/superpowers/reviews/2026-07-15-codex-r1-master-closeout-audit.md`  
CI: https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29437942535

| Gate | At `42c30c4` |
|------|----------------|
| ASan / UBSan / Fuzz / Linux | **green** |
| TSan | **red** — CrashBreadcrumb data race (F013); seqlock insufficient |
| Windows | **red** — C4875 on `legends_app` + C4324 alignas (F014) |
| Dependency Scan mechanics | green; inventory dishonest on FluidSynth pin (F015) |

## Remediation follow-up (this track)

| Item | Action |
|------|--------|
| #39 / F013 | **Mutex-serialize** breadcrumb ring (not seqlock+memcpy) |
| F014 | Attach `legends_gsl_msvc_options` to **all** gsl consumers including `legends_app` |
| F015 | SBOM inventories **runtime** `1.1.6-noglib` from `version.h`, not unused CMake pin |
| Docs honesty | Residual tracker + tasks must cite post-fix green SHA only |

## Historical pre-residual green

Mandatory stack green on `98450e6` / run [29435150647](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29435150647) — **does not** prove post-seqlock master.

## Still open (expected)

| ID | Topic |
|----|--------|
| #40 | MSan re-entry (`docs/ci/msan-reentry.md`) |
| #42 | Full vendored-tree SBOM beyond pins + fluidsynth header |
| #43 | fluidsynth upgrade; drop `osv-scanner.toml` ignores |
| #44 | Remove scoped `/wd4875` after Windows green under gsl-lite v1.1.0 without it |
