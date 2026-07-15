## 1. TSan suppression bring-up

- [ ] 1.1 Build the `tsan` preset locally, run ctest, and capture every distinct race report; map each to a family. Verify: written triage list with one stack sample per family.
  - Design families + Family C inventory: `docs/ci/r1-tsan-triage.md`.
  - Local TSan still Windows-blocked; CI is source of truth.
- [x] 1.2 File one tracked issue per race family with fix-and-remove exit criterion.
  - #38 global state, #39 CrashBreadcrumb, #45 intentional wrong-thread exclusion (closed after skip inventory).
- [x] 1.3 Create `tsan-suppressions.txt` with hygiene policy and issue-linked entries.
- [x] 1.4 Gate intentional wrong-thread tests out of TSan runs.
  - Family C complete (`LEGENDS_SKIP_INTENTIONAL_WRONG_THREAD` / `LEGENDS_TSAN_BUILD`).
  - CI green: https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29435150647/job/87419806235
- [ ] 1.5 Wire suppressions + symbolizer; verify zero TSan reports on dispatch.
  - Wiring done (absolute suppressions path + symbolizer + g++-13 TSan).
  - Pre-residual green: run 29435150647. Post-seqlock master `42c30c4` TSan **red** (F013 CrashBreadcrumb).
  - Re-check only after mutex fix lands and exact-SHA TSan is green with empty race suppressions.
- [ ] 1.6 Preset parity; prove green with suppressions file / red without.
  - Preset updated; without-file red proof still optional; current gate is full-suite green.
- [x] 1.7 Remove `allow_failure` from thread matrix; pointer to suppressions + issues.

## 2. MSan retirement

- [x] 2.1 File re-entry issue #40.
- [x] 2.2 Delete `memory` matrix entry; workflow references #40.
  - Residual: re-entry still open until instrumented libc++ (#40).

## 3. ASan/UBSan/fuzz triage to green

- [x] 3.1 Reproduce address/undefined failures; one issue per root cause.
  - #47 ASan dual-stdlib / move leak (closed after green); FINDING-002 UBSan enum (`dosbox_*_name` → `int`).
- [x] 3.2 Fix or issue-linked quarantine ASan/UBSan to green.
  - ASan: g++-13 sanitizers + DOSBoxContext move ownership (C3 leak).
  - Green: https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29435150647/job/87419806242
  - UBSan green: https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29435150647/job/87419806271
- [x] 3.3 Fuzz build + smoke green.
  - clang-19 + libstdc++; link deps; `corpus/config` seeds.
  - Green: https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29435150647/job/87421249665

## 4. Dependency-scan fix and unmute

- [x] 4.1 Supported package source with JSON artifact.
  - Pinned osv-scanner v2.0.1 + SHA-256; scan `docs/ci/vendored-sbom.cdx.json`.
  - Generator inventories **runtime** FluidSynth from `version.h` (1.1.6-noglib), not unused CMake pin (F015).
- [x] 4.2 Triage baseline findings.
  - #43 fluidsynth CVEs in `osv-scanner.toml` (still open until upgrade/remove ignore); SBOM version matches vendored tree.
- [x] 4.3 Unmute with green dispatch + seeded known-vulnerable proof.
  - Mutes removed. Job runs on `schedule` / `workflow_dispatch` / **push to master**.
  - Seed fixture `docs/ci/seed-known-vuln.cdx.json` (lodash@4.17.20) must exit non-zero without ignores.
  - Generator `scripts/generate_vendored_sbom.py --check` keeps pins and SBOM aligned (#42 partial).

## 5. Demotion rule and verification

- [x] 5.1 Demotion rule in CONTRIBUTING.md + OpenSpec SHALL language.
- [ ] 5.2 End-to-end: address, undefined, thread, fuzz green; no memory job; dependency-scan runnable.
  - Historical green: `98450e6` / run 29435150647 (pre-empty-suppressions residual).
  - Codex NO-GO at `42c30c4` / run 29437942535: TSan + Windows red (F013/F014).
  - Re-check `[x]` only when one synchronized SHA has ASan+UBSan+TSan+Fuzz+Windows all success.
- [ ] 5.3 Update audit-wiki + CI-THESIS only after 5.2 green.
  - Codex closeout audit: `docs/superpowers/reviews/2026-07-15-codex-r1-master-closeout-audit.md` (NO-GO).
  - Residual tracker: `docs/ci/r1-residual-closeout.md`.
