## Context

Four workflow files, one verbatim build skeleton. The checkout→configure→build→test block at `ci.yml:63-77` repeats at `pal-ci.yml:38-51` and `module-dag.yml:138-151`, and again with deltas in sprint2's `multi-instance-tests` (`sprint2-checks.yml:98-114`) (Recommendation Review M-1). A push to `master` touching `include/**` triggers all four workflows simultaneously — real per-push duplication is four-way on Linux (ci.yml `linux`, ci.yml `coverage`, sprint2 `multi-instance-tests`, pal-ci `headless-tests`) and two-way on Windows (ci.yml `windows`, pal-ci `windows-build`); module-dag's build jobs are nightly/dispatch-only and do not add to per-push load (Recommendation Review A-2; CI Workflows entity, §Inter-workflow build duplication). The duplicates differ deliberately: PAL backend selection, `LEGENDS_LIBRARY_MODE=ON`, `LEGENDS_USE_IPC=ON`.

Policy keys are equally lopsided: `permissions:` and `timeout-minutes` exist only in ci.yml; no workflow anywhere declares a `concurrency:` group; the 15 jobs across pal-ci/module-dag/sprint2 run at GitHub's 360-minute default timeout (Recommendation Review M-8, A-4). The ABI surface is checked twice with drift: ci.yml's `abi-check` does only `gcc -std=c11 -fsyntax-only` (`ci.yml:414-419`); pal-ci's `abi-c-compile` additionally builds and runs the `legends_abi_test` binary and compiles `test_legends_abi.c` (`pal-ci.yml:237-245`).

GitHub's reusable-workflow mechanics constrain the design: reusable workflows must live directly in `.github/workflows/` (no subdirectories), are called at job level via `uses: ./.github/workflows/<file>.yml` pinned to the caller's commit, accept typed inputs, and can be invoked once per matrix combination (CI Design for C++-CMake Monorepos (2026-06), practice 2).

## Goals / Non-Goals

**Goals:**
- Explicit `timeout-minutes` on every job; `permissions: contents: read` and a `concurrency:` group on every workflow — landed first, independent of everything else.
- One reusable `build-and-test.yml` (`on: workflow_call`) owning the build skeleton; callers declare one matrix cell per distinct configuration.
- Every deliberate config delta survives as a named cell: headless/SDL2/SDL3 PAL backends, library mode, IPC.
- A single ABI job carrying the superset of both current checks.
- Required-check contexts in `docs/ci/master-ruleset.json` updated and re-applied in the same change as any rename.

**Non-Goals:**
- Path-filter redesign — that is `requirable-path-gates` (R6). This change does not alter which paths trigger which workflow.
- Preset creation or flag migration — `presets-single-source` (R5) owns moving configure/build/test steps to `cmake --preset`; this change consumes preset names as matrix values once R5 lands.
- Tier changes. Nightly-only jobs (module-dag builds, SDL3/macOS lanes) stay nightly-only; mandatory lanes stay mandatory. Which lanes are primary vs optional is `openspec/specs/ci-stabilization`.
- Compiler caching (R14), actionlint/SHA-pinning (R13), gate-script consolidation (R3).
- Merging the four workflow *files* into one. Consolidation targets the duplicated build skeleton; trigger-distinct workflows (pal-ci's path scope, module-dag's gates, sprint2's checks) keep their files and call the shared skeleton.

## Decisions

**D1 — Hygiene lands as its own first step, before any consolidation.** `timeout-minutes`, `permissions: contents: read`, and `concurrency:` are per-file edits with zero prerequisites and no behavioral coupling to the reusable workflow (Recommendation Review A-4: "Cheapest candidate in the set... Zero prerequisites"; CI-THESIS.md adoption order step 1). Alternative rejected: bundling hygiene into the consolidation commit — it would hold a free risk-reduction hostage to R5 sequencing.

**D2 — Timeout values derive from observed lane shape, generous before caches warm.** ci.yml's existing values (5–30 min by lane) are the calibration source; pal-ci/module-dag/sprint2 jobs get values matched to their nearest ci.yml analogue with headroom, because A-4's only stated risk is over-tight values flaking before R14 caching lands. Values tighten later; the change here is bounding 360-minute runaways, not optimizing.

**D3 — Concurrency groups key on workflow + ref, cancel-in-progress only for PR refs.** `group: ${{ github.workflow }}-${{ github.ref }}` with `cancel-in-progress: ${{ github.event_name == 'pull_request' }}`. Cancelling superseded PR runs is pure win (A-2: "pure win"); cancelling push/nightly runs on master could kill a run whose verdict the R2 ruleset will require. Alternative rejected: blanket `cancel-in-progress: true` — discards master verdicts.

**D4 — One reusable workflow, inputs `{runner, configuration, ctest-args}`, not one file per lane.** `build-and-test.yml` declares `on: workflow_call` with typed inputs; each caller job is a `strategy: matrix` over configuration cells invoking `uses: ./.github/workflows/build-and-test.yml`. The same-repo `uses:` form pins the callee to the caller's commit, so workflow edits are atomic per PR (CI Design source, practice 2). After R5, the `configuration` input is a preset name and the matrix contains no raw flags (practice 7). Alternative rejected: composite action instead of reusable workflow — composites cannot own jobs, runners, or timeouts, which is exactly what is duplicated here.

**D5 — Matrix cells map one-to-one onto the distinct configurations now spread across files.** The A-2 binding is the design rule: consolidation must not drop deltas. Cell inventory, by what makes each distinct:
- Linux gcc headless, Linux clang headless (ci.yml `linux` matrix)
- Linux gcc IPC (`LEGENDS_USE_IPC=ON`; ci.yml `linux-ipc`)
- Windows MSVC headless (ci.yml `windows`)
- Linux gcc library-mode (`LEGENDS_LIBRARY_MODE=ON`; sprint2 `multi-instance-tests`, including its filtered-then-full test sequence)
- Linux PAL headless / SDL2 / SDL3 backends (pal-ci `headless-tests`, `sdl2-tests`, `sdl3-tests`)
- nightly tier unchanged: SDL3/macOS lanes, module-dag `build-linux`/`build-windows` (the latter become reusable-workflow calls at their existing nightly/dispatch gate)
Cells that duplicate an existing cell with no delta (pal-ci `windows-build` vs ci.yml `windows`; module-dag `build-linux` vs ci.yml `linux` gcc + headless flag) are retired or reduced to their delta. Alternative rejected: collapsing "similar" cells (e.g. PAL headless into ci.yml linux) — the deltas are the test coverage.

**D6 — ABI fold keeps the superset in `abi-check`, retires `abi-c-compile`.** The surviving `C ABI Verification` job does all three: build and run `legends_abi_test`, compile `test_legends_abi.c`, and the `gcc -std=c11 -fsyntax-only` header check (M-1 modification: "merge the superset, don't delete"). It stays in ci.yml unconditioned, because it is one of R2's five required checks and must keep reporting on every PR. Alternative rejected: folding `abi-check` into pal-ci instead — pal-ci is workflow-level path-filtered, which would make the required check pend forever on non-matching PRs.

**D7 — Renames are governed by the merge-gating name-sync rule; prefer keeping the five required names stable.** Where consolidation can express a cell under its existing expanded name (`Linux (gcc)`, `Linux (clang)`, `Linux IPC (gcc)`, `Windows (MSVC)`, `C ABI Verification`), it does — reusable-workflow call jobs control their display name via the job `name:` key, so stability is cheap. Any name that must change updates `docs/ci/master-ruleset.json` and re-applies the ruleset in the same change (`master-ruleset-required-checks` requirement "Required-check names stay synchronized"). Note: a job calling a reusable workflow surfaces nested job names as `caller / callee` in check contexts; the caller job `name:` must be verified against the actual reported context string before the ruleset is touched.

**D8 — Sequencing: hygiene immediately; consolidation after R5 and R2.** Adoption order step 6: "reusable workflow over the now-preset-based jobs; update R2's required-check names in the same change." Consolidating before R5 would bake raw flag lists into the reusable workflow's inputs and force a second migration. Consolidating before R2 is possible but loses the name-sync discipline; with R2 live, the rename step is mechanical.

## Risks / Trade-offs

- [Over-tight timeouts flake cold-cache jobs before R14 caching lands] → calibrate from ci.yml's observed values with headroom (D2); a timeout trip is loud and adjustable in a one-line PR, unlike a 360-minute hang.
- [`cancel-in-progress` kills a run whose verdict matters] → restricted to PR refs (D3); master pushes and nightlies always run to completion.
- [A required check silently changes context string after consolidation (the `caller / callee` naming surface)] → D7's verification step: read the actual check context from a test PR before updating `docs/ci/master-ruleset.json`; the ruleset update and the rename land in the same change, so a mismatch never spans a merge window.
- [Consolidation drops a deliberate delta and a configuration goes untested] → D5's cell inventory is the checklist; tasks require a before/after configuration matrix proving every distinct flag set still builds, and the A-2 binding is restated in the spec as a requirement.
- [Reusable-workflow limits (no subdirectories, input typing, permissions narrow-only)] → known constraints, designed around (D4); `permissions: contents: read` at every level is compatible with narrow-only propagation.
- [Retiring pal-ci `windows-build`/module-dag builds loses a verdict someone watched] → the surviving cells cover the same configurations; module-dag's `summary` job logic is updated to reflect the new call structure rather than deleted.

## Migration Plan

1. **Step 1 (independent, lands first):** hygiene PR — timeouts, permissions, concurrency across all four files. No job logic changes; rollback is revert.
2. **Step 2 (after R5, R2):** add `build-and-test.yml`; convert ci.yml's build jobs to matrix calls preserving the five required-check names; verify reported check contexts on the PR itself.
3. **Step 3 (same change as 2 if names changed):** update `docs/ci/master-ruleset.json`, re-apply ruleset per the merge-gating procedure.
4. **Step 4:** convert pal-ci, sprint2, module-dag build jobs to calls; retire `abi-c-compile` and the no-delta duplicate builds; update module-dag `summary`.
5. Rollback at any step: revert the workflow-file commit; if a ruleset rename has been applied, re-apply the previous `master-ruleset.json` first so required checks keep reporting.

## Open Questions

- Whether `Linux (gcc)`/`Linux (clang)` remain separate cells or become one matrixed cell with two expanded names is decided at implementation against the actual check-context strings; either way D7's sync rule covers it (flagged as this change's question by `master-ruleset-required-checks` design).
