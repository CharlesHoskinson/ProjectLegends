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
- [x] 1.5 Wire suppressions + symbolizer; verify zero TSan reports on dispatch.
  - Mutex breadcrumb fix (`621a099`); empty active race suppressions.
  - Exact-SHA TSan green 4512/4512: https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29440398476/job/87437543361
- [ ] 1.6 Preset parity; prove green with suppressions file / red without.
  - Preset updated; without-file red proof still optional; current gate is full-suite green.
- [x] 1.7 Remove `allow_failure` from thread matrix; pointer to suppressions + issues.

## 2. MSan retirement

- [x] 2.1 File re-entry issue #40.
- [x] 2.2 Delete `memory` matrix entry; workflow references #40.
  - Residual: re-entry still open until instrumented libc++ (#40).

## 3. ASan/UBSan/fuzz triage to green

- [x] 3.1 Reproduce address/undefined failures; one issue per root cause.
  - #47 ASan dual-stdlib / move leak (closed).
  - UBSan invalid-enum: fixed in-tree (`dosbox_*_name` takes `int`); no separate GitHub issue (FINDING-002 code-only).
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
  - FluidSynth via Debian purl `pkg:deb/debian/fluidsynth@1.1.6` (OSV-matchable); mt32emu pin inventoried; dead FluidSynth CMake pin not inventoried (F017).
- [x] 4.2 Triage baseline findings.
  - #43 ignores cover CVE + DEBIAN-CVE + DLA IDs; CI asserts bare FluidSynth scan detects DEBIAN-CVE-2021-21417 and DEBIAN-CVE-2025-56225 before ignores.
- [x] 4.3 Unmute with green dispatch + seeded known-vulnerable proof.
  - Mutes removed. Job runs on `schedule` / `workflow_dispatch` / **push to master**.
  - Seed fixture `docs/ci/seed-known-vuln.cdx.json` (lodash@4.17.20) must exit non-zero without ignores.
  - Generator `scripts/generate_vendored_sbom.py --check` keeps pins and SBOM aligned (#42 partial).

## 5. Demotion rule and verification

- [x] 5.1 Demotion rule in CONTRIBUTING.md + OpenSpec SHALL language.
- [x] 5.2 End-to-end: address, undefined, thread, fuzz green; no memory job; dependency-scan runnable.
  - Synchronized green stack `621a099` / run 29440398476 (all mandatory runtime lanes).
  - Dependency scan F017 follow-up: Debian FluidSynth purl + exercised ignores (this commit).
- [ ] 5.3 Update audit-wiki + CI-THESIS only after 5.2 green.
  - Re-proof after F017 fix; residual tracker + CI-THESIS updated in tandem with this commit.
