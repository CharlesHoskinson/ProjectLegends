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

## Residuals (2026-07-15 follow-up on master)

| ID | Topic | Status |
|----|--------|--------|
| #38 | TSan `g_active_instance` | **Closed** — dead suppression removed (`std::atomic`); empty suppressions file |
| #39 | TSan `CrashBreadcrumb::add` | **Closed** — per-slot seqlock; suppressions removed |
| #40 | MSan re-entry | Open / parked — checklist `docs/ci/msan-reentry.md` |
| #42 | Automated SBOM | **Partial closed** — `scripts/generate_vendored_sbom.py` + CI `--check`; full tree SBOM still future |
| #43 | fluidsynth CVEs | Open — vendored tree upgrade required before drop ignores |
| #44 | `/wd4875` | **Partial** — scoped + gsl-lite pin **v1.1.0**; remove `/wd4875` after Windows CI proves clean |
| 4.3 | Known-vuln seed | **Closed in CI** — `docs/ci/seed-known-vuln.cdx.json` must fail closed |

## Process

- Stale R1 PR **#41** closed as superseded by #46.
- OpenSpec tasks: `openspec/changes/ci-stabilize-mandatory-lanes/tasks.md` updated with job URLs (F010).
