# CI Thesis — Project Legends (2026-06)

Project Legends does not lack CI machinery; it lacks binding. Four workflows, ten gate scripts, five sanitizer configurations, five fuzz targets, a machine-readable module DAG, and a determinism harness all exist — and none of it constrains what lands on master. Nothing connects a green verdict to the right to merge, nothing lets a developer run the mandatory gates before pushing, and the lanes guarding the highest-risk surfaces are red, muted, or structurally unable to run. The fix is not more gates. It is making the existing gates mean something: stabilize them, bind them to merging, give developers the same gates locally, and retire every gate that cannot fail honestly.

Evidence base: [audit-wiki](audit-wiki/index.md) — entity pages inventory the current state, source pages record researched practice and run-history empirics, synthesis pages derive the gaps. Every claim below links there; every wiki claim cites a repo path, run id, or retrieved URL.

## Current state

Master ran red for five months. Of 397 retained Actions runs, 77.6% failed; on master alone, 82.3%. The main CI workflow succeeded 6 times in its history — all within 27 hours of the 2026-06-08 gate demotion, meaning green was achieved by removing gates, not fixing causes ([CI Run History](audit-wiki/wiki/sources/CI%20Run%20History%20(2026-06).md)). There is no branch protection and no ruleset on master, and push events dominate the run history — 233 of 397, against 56 pull-request events ([CI Run History](audit-wiki/wiki/sources/CI%20Run%20History%20(2026-06).md)). A developer following the written docs sees 3 of 14 mandatory-tier gates before pushing; no single command reproduces the rest ([Local Dev Loop](audit-wiki/wiki/entities/Local%20Dev%20Loop.md)).

The machinery itself is duplicated and unbound: no workflow invokes any CMake preset, none declares a concurrency group, one push can trigger four redundant Linux builds of the same tree, and a full cycle costs about 3 hours of serial compute with no compiler caching ([CI Workflows](audit-wiki/wiki/entities/CI%20Workflows%20(GitHub%20Actions).md), [Build & CI System](audit-wiki/wiki/entities/Build%20&%20CI%20System%20(Project%20Legends).md)). The license firewall — the project's reason for its IPC architecture — is enforced by comments: the DAG verifier never checks the three license-critical targets, and the isolation verifier is wired to nothing ([CI Gate Coverage Map](audit-wiki/wiki/maps/CI%20Gate%20Coverage%20Map.md)).

## What the evidence shows

**Modularity.** The four workflows share a verbatim build skeleton with no reusable workflow, and their path filters diverge from the module manifest they should mirror. Workflow-level path filters make the script and DAG gates structurally ineligible to be required checks — a path-filtered required check pends forever on non-matching PRs ([Gap Analysis — Modularity](audit-wiki/wiki/syntheses/Gap%20Analysis%20—%20Modularity%20(2026-06).md); [CI Design for C++-CMake Monorepos](audit-wiki/wiki/sources/CI%20Design%20for%20C++-CMake%20Monorepos%20(2026-06).md)).

**Maintainability.** Gate logic lives in workflow YAML where nothing local can call it; ten Python gate steps are inlined in one workflow; 15 of 31 jobs have no timeout; every action is pinned to a mutable tag; SDL3 is cloned and compiled from upstream `main` on every PAL run, uncached ([Gap Analysis — Maintainability](audit-wiki/wiki/syntheses/Gap%20Analysis%20—%20Maintainability%20(2026-06).md)).

**Test coverage intelligence.** Coverage is measured and then ignored: the policy step is an echo, the 80% threshold lives in a tag-gated job that has never run, and the vendored engine skews every number because the lcov filter omits it. The fuzz lane regenerates its corpus every run and discards its own crash reports. Three integration test files compile into no target; the `soak` label is selected and excluded in four places and attached to zero tests; the determinism oracle runs in `Fast` mode that hashes only conventional memory ([Gap Analysis — Test Coverage Intelligence](audit-wiki/wiki/syntheses/Gap%20Analysis%20—%20Test%20Coverage%20Intelligence%20(2026-06).md), [Verification Lanes](audit-wiki/wiki/entities/Verification%20Lanes%20(Sanitizers,%20Fuzz,%20Coverage,%20Determinism).md)).

**Always green.** Red-after-push is the structural norm because gates run only after push, verdicts bind nothing, and the failure modes that should be loudest are quietest: TSan muted since March with its exit plan living in a YAML comment, MSan crashing on startup by construction, dependency-scan double-muted with `|| true`, and flaky SDL tests "fixed" by deleting their assertions ([Gap Analysis — Always Green](audit-wiki/wiki/syntheses/Gap%20Analysis%20—%20Always%20Green%20(2026-06).md), [Quality Gate Demotion](audit-wiki/wiki/concepts/Quality%20Gate%20Demotion%20(2026-06-08).md)).

All 36 candidate recommendations from the gap analyses survived an adversarial pass checking each against the repo: none was already implemented, none violates the GPL/MIT split, and the surviving modifications are recorded in [Recommendation Review](audit-wiki/wiki/syntheses/Recommendation%20Review%20(2026-06).md). The recommendations below consolidate the surviving candidates; ranking follows (1) unblocks always-green, (2) closes gate-coverage holes, (3) everything else. A recommendation is major when it changes what a contributor must do to land a commit or alters a CI lane's existence, trigger tier, or enforcement status — including transitively, where a later major depends on it.

## Recommendations

**R1 — Stabilize the mandatory lanes; end silent failure. Major.** (G-1, G-7)
Triage the sanitizer and fuzz lanes to deterministic green: a checked-in `tsan-suppressions.txt` with one issue-linked entry per known race, then drop `allow_failure` from the TSan leg; retire the MSan leg with a tracked re-entry condition (instrumented libc++) — it crashes on startup by construction and verifies nothing; fix the broken osv-scanner invocation before unmuting dependency-scan. Files: `.github/workflows/ci.yml` sanitizers/fuzz/dependency-scan jobs. Evidence: [Verification Lanes](audit-wiki/wiki/entities/Verification%20Lanes%20(Sanitizers,%20Fuzz,%20Coverage,%20Determinism).md), [Sanitizer Lane Strategy](audit-wiki/wiki/sources/Sanitizer%20Lane%20Strategy%20(2026-06).md). No lane is ever demoted again without a tracked exit criterion.

**R1 implementation status (branch `ci/r1-stabilize-mandatory-lanes`):** wiring landed — `tsan-suppressions.txt` + issues #38/#39, TSan `allow_failure` removed, `llvm-18` symbolizer installed, MSan matrix entry removed (#40), intentional wrong-thread tests skip under `LEGENDS_TSAN_BUILD` (#45), dependency-scan uses recursive osv-scanner + `osv-scanner.toml` baseline (#43), demotion rule in `CONTRIBUTING.md`. **Still required for R1 exit:** green `workflow_dispatch` of `address`/`undefined`/`thread`/`fuzz` and nightly dependency-scan (live triage of any remaining ASan/UBSan/fuzz reds per design D6).

**R2 — Bind merging to green. Major.** (G-2, G-4)
Active ruleset on master: require PRs, require the five exact-name checks that already run unconditionally (`Linux (gcc)`, `Linux (clang)`, `Linux IPC (gcc)`, `Windows (MSVC)`, `C ABI Verification`), require branches up to date, forbid force pushes. Defer the merge queue: at this PR volume, require-up-to-date delivers the never-merge-red invariant, and no workflow has a `merge_group` trigger anyway. Server-side setting plus a documented policy file. Evidence: [CI Workflows](audit-wiki/wiki/entities/CI%20Workflows%20(GitHub%20Actions).md), [Merge Queues & Required Checks](audit-wiki/wiki/sources/Merge%20Queues%20&%20Required%20Checks%20(2026-06).md). Sequenced strictly after R1 — protection before green freezes all merging. The required-check names must be updated in the same change whenever later consolidation (R8) renames jobs.

**R3 — One gate entry point, run by CI and developers alike. Major (transitively: R4's hook tier runs it, and it redefines what the mandatory script lanes execute).** (M-7, A-5, G-5)
Create `scripts/preflight.py` wrapping the ten CI-run check scripts, the C11 ABI compile (OS-gated for MSVC-only machines), and the OS-reachable build/test configurations; rewrite `sprint2-checks.yml`, `module-dag.yml`'s include step, and `ci.yml`'s abi-check body to invoke it. Gate logic leaves YAML; local/CI divergence becomes structurally impossible. Evidence: [Local Dev Loop](audit-wiki/wiki/entities/Local%20Dev%20Loop.md), [Local Preflight Design](audit-wiki/wiki/sources/Local%20Preflight%20Design%20(2026-06).md).

**R4 — Managed, documented, tiered hooks. Major.** (A-6, G-12)
Replace the one-check opt-in `.githooks/pre-commit` with a committed hook-manager config (pre-commit `repo: local` or lefthook — both Windows-native): staged-file checks at commit, the script suite at push, full preflight on demand. Document setup in `CONTRIBUTING.md`; run the identical config in CI so skipping hooks only delays the failure. Evidence: [Quality Gate Scripts & Hooks](audit-wiki/wiki/entities/Quality%20Gate%20Scripts%20&%20Hooks.md), [Local Preflight Design](audit-wiki/wiki/sources/Local%20Preflight%20Design%20(2026-06).md).

**R5 — Presets become the single source of build truth. Major (every mandatory lane's build definition moves into the presets R3's preflight and CI both consume).** (M-2, A-1, G-6)
Add the missing presets first (an MSVC/VS-generator preset — none exists; `ubsan`; `library-mode`; headless-PAL), reconcile the `asan` preset with CI's split lanes, then migrate every workflow configure/build/test step to `cmake --preset`/`ctest --preset`. No `msan` preset — that cell is retired under R1. Linux-pinned presets get `condition` guards so Windows preset listings stay usable. Files: `CMakePresets.json`, all four workflows. Evidence: [Build & CI System](audit-wiki/wiki/entities/Build%20&%20CI%20System%20(Project%20Legends).md), [CI Design for C++-CMake Monorepos](audit-wiki/wiki/sources/CI%20Design%20for%20C++-CMake%20Monorepos%20(2026-06).md).

**R6 — Make every gate requirable. Major.** (M-3, M-4, G-3)
Remove workflow-level `paths:` filters; compute changed paths in a cheap first job and skip at job level, with unrecognized paths defaulting to run-everything. Hand-align the filter sets with `cmake/ModuleManifest.cmake` (pal-ci narrows; `openspec/**` and `cmake/**` attach to the gates written for them; sprint2 gets a branch filter). This is what lets the script and DAG gates ever join R2's required set. Evidence: [CI Gate Coverage Map](audit-wiki/wiki/maps/CI%20Gate%20Coverage%20Map.md), [CI Design for C++-CMake Monorepos](audit-wiki/wiki/sources/CI%20Design%20for%20C++-CMake%20Monorepos%20(2026-06).md).

**R7 — Activate the license firewall. Major.** (M-5, plus the verifier halves of A-7/T-7)
Extend `legends_verify_all_dags()` to the three license-critical targets (`legends_ipc`, `legends_proxy`, `legends_engine_host`) — activating an existing configure-time FATAL_ERROR mechanism on the exact MIT↔GPL boundary; wire the orphaned `VerifyGPLIsolation.cmake`/`scripts/verify_gpl_isolation.py` into the `linux-ipc` job, fail-closed; add a REUSE compliance job; add a Windows IPC build cell so the GPL-isolating architecture is built on more than one OS at one tier. Evidence: [CI Gate Coverage Map](audit-wiki/wiki/maps/CI%20Gate%20Coverage%20Map.md), [Vendored & License-Isolated Dependency CI](audit-wiki/wiki/sources/Vendored%20&%20License-Isolated%20Dependency%20CI%20(2026-06).md).

**R8 — Consolidate the workflows; centralize policy. Major.** (M-1, A-2, M-8, A-4)
Factor the shared build skeleton into a `workflow_call` reusable workflow, one matrix cell per distinct configuration — consolidation must not drop the deliberate config deltas (PAL backends, library mode, IPC). Fold pal-ci's `abi-c-compile` into `abi-check` keeping the superset (the runtime `legends_abi_test` and the C test-file compile). Set `timeout-minutes`, `permissions: contents: read`, and `concurrency` groups on all jobs — the timeout fix has zero prerequisites and lands first. Job renames here must update R2's required-check set in the same change. Evidence: [CI Workflows](audit-wiki/wiki/entities/CI%20Workflows%20(GitHub%20Actions).md), [CI Design for C++-CMake Monorepos](audit-wiki/wiki/sources/CI%20Design%20for%20C++-CMake%20Monorepos%20(2026-06).md).

**R9 — Enforce coverage without freezing development. Major.** (T-3, G-10)
Exclude the vendored engine from the lcov denominator; gate PRs on diff coverage of new/changed lines using the artifact CI already produces (non-shallow checkout required); commit a ratchet floor per module aligned to the DAG; widen release-validation's tag-only `if:` so the 80% threshold job can be rehearsed by dispatch before it gates a real release. Files: `ci.yml` coverage and release-validation jobs. Evidence: [Verification Lanes](audit-wiki/wiki/entities/Verification%20Lanes%20(Sanitizers,%20Fuzz,%20Coverage,%20Determinism).md), [Coverage Policy Ratcheting](audit-wiki/wiki/sources/Coverage%20Policy%20Ratcheting%20(2026-06).md).

**R10 — A fuzz lane that keeps what it learns. Major.** (T-4, G-8)
Persist the corpus (cache plus committed reproducer seeds under `tests/fuzz/corpus/` — the CMake copy hook already exists, dead); upload crash artifacts with `-artifact_prefix`; convert the PR step to deterministic replay of seeds and known reproducers; fund real exploration on the existing nightly cron; raise the job timeout before funding it. Triage the currently red lane first so a persisted corpus doesn't bake in failing inputs. Files: `ci.yml` fuzz job, `tests/fuzz/`. Evidence: [Verification Lanes](audit-wiki/wiki/entities/Verification%20Lanes%20(Sanitizers,%20Fuzz,%20Coverage,%20Determinism).md), [Continuous Fuzzing in CI](audit-wiki/wiki/sources/Continuous%20Fuzzing%20in%20CI%20(2026-06).md).

**R11 — Flake management with memory. Major.** (G-9)
Adopt a quarantine convention (`DISABLED_` plus ticket, or a `flaky` CTest label excluded from gates and run nightly); add a nightly burn-in lane to `ci.yml` (`ctest --repeat until-fail:N` with shuffle); keep a flake ledger from `run_attempt` data as workflow artifacts. For the relaxed SDL tests (`tests/unit/test_pal_sdl2_backend.cpp`, `tests/unit/test_pal_sdl3_backend.cpp`): decide per test whether the deleted assertion was a real invariant — where init events are legitimate, replace with a typed assertion; where not, restore and quarantine with an owner and exit criterion. Never delete an assertion to make CI pass. Evidence: [Project Legends Test Suite](audit-wiki/wiki/entities/Project%20Legends%20Test%20Suite.md), [Flaky-Test Detection & Quarantine](audit-wiki/wiki/sources/Flaky-Test%20Detection%20&%20Quarantine%20(2026-06).md).

**R12 — A test estate that tells the truth. Major.** (M-6, T-1, T-5, T-6, T-7, T-8)
Module-level CTest labels with nonzero-selection guards on every `-L` step; a PR-tier determinism job selecting the existing `determinism` label, with a canary proving the oracle can fail, and the hash switched off hardcoded `Fast` at the library entry point (extending `Full` to VGA/devices is engine work, scoped separately); compile `test_dual_ffi.cpp` and rewrite-or-delete the two bit-rotted orphans with the removal recorded; visible `stub` labels for skip-stubs; make the `soak` label real and run soak nightly with its env gate exported and durations bounded to the runner cap. Evidence: [Project Legends Test Suite](audit-wiki/wiki/entities/Project%20Legends%20Test%20Suite.md), [Test Impact Analysis & Selection](audit-wiki/wiki/sources/Test%20Impact%20Analysis%20&%20Selection%20(2026-06).md).

**R13 — Workflow lint and supply-chain hygiene. Major (adds a lint lane).** (A-8)
actionlint job; `permissions` blocks everywhere; SHA-pin third-party actions together with a dependabot config (pinning without an updater rots). Evidence: [CI Workflows](audit-wiki/wiki/entities/CI%20Workflows%20(GitHub%20Actions).md), [Gap Analysis — Maintainability](audit-wiki/wiki/syntheses/Gap%20Analysis%20—%20Maintainability%20(2026-06).md).

**R14 — Compiler caching. Minor.** (A-3, G-11)
ccache via launcher variables on the six Ninja Linux jobs (propagates into FetchContent sub-builds, so the engine and SDL3 stop rebuilding from scratch); sccache with the native GHA backend plus a Ninja conversion for the MSVC jobs; pin and cache pal-ci's SDL3 source build; per-configuration keys with size caps against the 10 GB pool. Evidence: [CI Workflows](audit-wiki/wiki/entities/CI%20Workflows%20(GitHub%20Actions).md), [Compiler Caching on GitHub Actions](audit-wiki/wiki/sources/Compiler%20Caching%20on%20GitHub%20Actions%20(2026-06).md).

**R15 — Reconcile documentation with machinery. Minor.** (A-7 documentation half)
Fix the Tier-B claim in CONTRIBUTING.md (the helper has zero callers), implement `LEGENDS_WERROR` as a real option, correct README's gate diagram to what CI runs. Evidence: [Build & CI System](audit-wiki/wiki/entities/Build%20&%20CI%20System%20(Project%20Legends).md), [Quality Gate Scripts & Hooks](audit-wiki/wiki/entities/Quality%20Gate%20Scripts%20&%20Hooks.md).

**Deferred — test selection (T-2).** DAG-driven test selection is designed (changed-path → manifest reverse-closure with safe fallback) but activates only after the lanes hold green: selection on a noisy pipeline manufactures false confidence, and CI history at 87% failure encodes pipeline breakage, not regression signal. Revisit once R1–R2 have held.

## Defense in depth: always green

The end state has two layers. Locally: clone → documented bootstrap → hook install verified → `preflight` runs the same gates CI runs, tiered so commit-time costs seconds and push-time costs minutes, with the OS-unreachable residue (the other compiler's lanes) explicitly named rather than silently skipped. Server-side: the ruleset makes green a precondition of merging, required checks are exact-name jobs that always report, and every lane in the mandatory tier can fail honestly — no allow-failure without an issue-linked exit, no muted scanners, no assertions deleted to make red go away. A developer who skips every local layer merely moves the same failure later; nothing routes around it.

## Adoption order

Dependency-ordered; each step leaves CI no worse than it found it.

1. **R8-timeouts** (zero prerequisites) and **R14** (caching) — immediate, independent.
2. **R1** — lanes to deterministic green; everything else assumes it.
3. **R2** — ruleset binds merges to the now-green checks.
4. **R5-presets** (MSVC preset first) → **R3** (preflight consumes presets) → **R4** (hooks call preflight).
5. **R6** — path-filter redesign makes the script/DAG gates requirable; extend R2's required set.
6. **R8-consolidation** — reusable workflow over the now-preset-based jobs; update R2's required-check names in the same change.
7. **R7** — license firewall: DAG edges, verifier wiring, REUSE, Windows IPC cell. Independent of 4–6; can land any time after R1.
8. **R9, R10, R11, R12** — coverage gate, fuzz persistence, quarantine convention, test-estate truth; independent of each other.
9. **R13, R15** — lint lane, pinning, doc reconciliation, as the above settle.
10. **T-2 selection** — only after sustained green.

## Evidence index

| Claim class | Where |
|---|---|
| Run/failure empirics, demotion timeline | [CI Run History (2026-06)](audit-wiki/wiki/sources/CI%20Run%20History%20(2026-06).md) |
| Gate-to-module coverage, unguarded paths | [CI Gate Coverage Map](audit-wiki/wiki/maps/CI%20Gate%20Coverage%20Map.md) |
| Workflow inventory, duplication, tiering | [CI Workflows (GitHub Actions)](audit-wiki/wiki/entities/CI%20Workflows%20(GitHub%20Actions).md) |
| Build system, presets, DAG, license split | [Build & CI System (Project Legends)](audit-wiki/wiki/entities/Build%20&%20CI%20System%20(Project%20Legends).md) |
| Test suites, labels, fixtures, orphans | [Project Legends Test Suite](audit-wiki/wiki/entities/Project%20Legends%20Test%20Suite.md) |
| Sanitizer/fuzz/coverage/determinism enforcement reality | [Verification Lanes](audit-wiki/wiki/entities/Verification%20Lanes%20(Sanitizers,%20Fuzz,%20Coverage,%20Determinism).md) |
| Gate scripts, hooks, openspec/graphify gates | [Quality Gate Scripts & Hooks](audit-wiki/wiki/entities/Quality%20Gate%20Scripts%20&%20Hooks.md) |
| Local developer reality | [Local Dev Loop](audit-wiki/wiki/entities/Local%20Dev%20Loop.md) |
| Researched practice, per topic | the ten research-topic source pages, listed in the [sources index](audit-wiki/wiki/sources/_index.md) |
| Gap derivations, candidate recommendations | the four Gap Analysis pages under [audit-wiki/wiki/syntheses/](audit-wiki/wiki/syntheses/_index.md) |
| Adversarial verdicts and modifications | [Recommendation Review (2026-06)](audit-wiki/wiki/syntheses/Recommendation%20Review%20(2026-06).md) |
