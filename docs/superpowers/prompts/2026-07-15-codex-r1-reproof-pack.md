# Codex re-proof pack — post F013/F014/F015 remediation

Use **after** CI for remediation SHA completes. Complements:

`C:\ProjectLegends\docs\superpowers\prompts\2026-07-15-codex-r1-master-closeout-audit.md`

## Claimed remediation tip

| Field | Value |
|-------|--------|
| Fix commit | `621a099944f5c7d82ed1a00c607a57fbc959b4c7` |
| Primary CI run | https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29440398476 |
| Prior NO-GO audit | `C:\ProjectLegends\docs\superpowers\reviews\2026-07-15-codex-r1-master-closeout-audit.md` |
| Prior NO-GO SHA | `42c30c46b88fc30891f7e6a25b629cd0808a5154` |
| Prior failed run | https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29437942535 |

## What must flip from FAIL → PASS

| Finding | Fix claim | Prove with |
|---------|-----------|------------|
| F013 TSan CrashBreadcrumb | `std::mutex` serializes add/read/clear | `thread Sanitizer` **success** on SHA ≥ `621a099`; zero `WARNING: ThreadSanitizer` on breadcrumb tests |
| F014 Windows C4875/C4324 | `legends_app` links `legends_gsl_msvc_options`; no alignas(64) Slot | `Windows (MSVC)` **success** (build+test) |
| F015 FluidSynth SBOM | version **1.1.6-noglib** from `version.h` | Dependency Scan log / SBOM JSON; not 2.3.5 |
| Honesty | #39 reopened until green | issue state + close only after TSan URL |

## Paste for Codex

```text
Re-audit Project Legends R1 master closeout after remediation.

Primary brief:
C:\ProjectLegends\docs\superpowers\prompts\2026-07-15-codex-r1-master-closeout-audit.md

Remediation context:
C:\ProjectLegends\docs\superpowers\prompts\2026-07-15-codex-r1-reproof-pack.md

Prior NO-GO (do not treat as current):
C:\ProjectLegends\docs\superpowers\reviews\2026-07-15-codex-r1-master-closeout-audit.md

Repo: C:\ProjectLegends
Pin: git fetch && git rev-parse origin/master
Require exact-SHA CI success for ASan, UBSan, TSan, Fuzz, Windows.
Write: C:\ProjectLegends\docs\superpowers\reviews\YYYY-MM-DD-codex-r1-master-reproof-audit.md
No product code changes.
```

## Intermediate signal (do not call GO early)

As of drafting: on run `29440398476`, **thread Sanitizer already success**, ASan/UBSan/Dependency Scan success; Windows/Fuzz may still be in progress. Codex must re-query live jobs.
