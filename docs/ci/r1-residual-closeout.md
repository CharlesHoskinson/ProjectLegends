# R1 residual closeout tracker

Post-merge of PR [#46](https://github.com/CharlesHoskinson/ProjectLegends/pull/46) onto `master` (`f39b3da`).

## Mandatory lanes (closed)

| Lane | Evidence (SHA `98450e6`, run 29435150647) |
|------|-------------------------------------------|
| address Sanitizer | [job](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29435150647/job/87419806242) |
| undefined Sanitizer | [job](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29435150647/job/87419806271) |
| thread Sanitizer | [job](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29435150647/job/87419806235) |
| Fuzz Testing | [job](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29435150647/job/87421249665) |
| Windows (MSVC) | [job](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29435150647/job/87419806152) |

Closed tracking: **#45**, **#47**, **#48** (lane-level). See issue comments for residual notes.

## Residuals still open

| ID | Topic | Status |
|----|--------|--------|
| #38 | TSan `g_active_instance` suppression | Open — green TSan with suppression; need match-count / removal if dead (atomic) |
| #39 | TSan `CrashBreadcrumb::add` | Open — fix-and-remove; not permanent document-and-keep |
| #40 | MSan re-entry | Open / parked — instrumented libc++ required |
| #42 | Automated CMake/FetchContent SBOM | Open — hand-curated CycloneDX expanded; generator not automated |
| #43 | fluidsynth CVEs | Open — ignored in `osv-scanner.toml` until upgrade |
| #44 | `/wd4875` gsl-lite | Mitigated — scoped to gsl-linked targets; remove with pin upgrade |

## Process

- Stale R1 PR **#41** closed as superseded by #46.
- OpenSpec tasks: `openspec/changes/ci-stabilize-mandatory-lanes/tasks.md` updated with job URLs (F010).
