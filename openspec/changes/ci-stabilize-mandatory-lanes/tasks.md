## 1. TSan suppression bring-up

- [ ] 1.1 Build the `tsan` preset locally, run ctest, and capture every distinct race report; map each to a family. Verify: written triage list with one stack sample per family.
  - Partial: `docs/ci/r1-tsan-triage.md` design-named families only. Local TSan blocked on Windows; CI found missed `ConcurrentDestroyAttempts` (FINDING-003). Re-check after skip fix.
- [x] 1.2 File one tracked issue per race family with fix-and-remove exit criterion.
  - #38 global state, #39 CrashBreadcrumb (exit tightened in suppressions comments), #45 intentional wrong-thread exclusion.
- [x] 1.3 Create `tsan-suppressions.txt` with hygiene policy and issue-linked entries.
- [x] 1.4 Gate intentional wrong-thread tests out of TSan runs.
  - Fixed post-audit: `ConcurrentDestroyAttempts` has `LEGENDS_SKIP_INTENTIONAL_WRONG_THREAD()` (FINDING-003).
  - Full Family C inventory + two missed skips (`DestroyFromAnyThreadAllowed`, `ThreadAffinityConsistentAcrossMultipleCalls`) in `docs/ci/r1-tsan-triage.md`.
  - thread Sanitizer job (pending at task close): https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29426480438/job/87390083377
- [ ] 1.5 Wire suppressions + symbolizer; verify zero TSan reports on dispatch.
  - Wiring done (absolute `$GITHUB_WORKSPACE` path + llvm-symbolizer). Green thread leg still required (same job URL as 1.4).
- [ ] 1.6 Preset parity; prove green with suppressions file / red without.
  - Preset updated; local comparison still blocked (no Linux cmake on audit host).
- [x] 1.7 Remove `allow_failure` from thread matrix; pointer to suppressions + issues.
  - Mute removed. Seeded race proof still optional; real race previously failed closed.

## 2. MSan retirement

- [x] 2.1 File re-entry issue #40.
- [x] 2.2 Delete `memory` matrix entry; workflow references #40.

## 3. ASan/UBSan/fuzz triage to green

- [ ] 3.1 Reproduce address/undefined failures; one issue per root cause.
  - CI evidence: FINDING-001/#47 (ASan cascade), FINDING-002 (UBSan enum — API fix landed).
- [ ] 3.2 Fix or issue-linked quarantine ASan/UBSan to green.
  - UBSan invalid-enum path: `dosbox_*_name` now takes `int` (FINDING-002).
  - ASan: tracked in #47; not yet green.
- [ ] 3.3 Fuzz build + smoke green.
  - Configure libc++ landed earlier; `fuzz_config_parser` now links `gsl::gsl-lite-v1` (FINDING-004). Smoke still needs CI proof.

## 4. Dependency-scan fix and unmute

- [x] 4.1 Supported package source with JSON artifact.
  - Post-audit: pin osv-scanner v2.0.1 + SHA-256; scan `docs/ci/vendored-sbom.cdx.json` (FINDING-006/008). Recursive `-r` alone is insufficient on v2.x.
- [x] 4.2 Triage baseline findings.
  - #43 fluidsynth CVEs in `osv-scanner.toml`; #42 full CMake SBOM remains open.
- [ ] 4.3 Unmute with green dispatch + seeded known-vulnerable proof.
  - Mutes removed; green dispatch + seed still required.

## 5. Demotion rule and verification

- [x] 5.1 Demotion rule in CONTRIBUTING.md + OpenSpec SHALL language.
- [ ] 5.2 End-to-end: address, undefined, thread, fuzz green; no memory job; dependency-scan green on dispatch.
- [ ] 5.3 Update audit-wiki + CI-THESIS only after 5.2 green.
  - Codex audit published: `docs/superpowers/reviews/2026-07-15-codex-r1-ci-stabilize-mandatory-lanes-audit.md` (FAIL / NO-GO at ba8cc8a).
