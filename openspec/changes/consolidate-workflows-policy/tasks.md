## 1. Hygiene: timeouts, permissions, concurrency (independent; lands first)

- [ ] 1.1 Add `timeout-minutes` to all 8 jobs in `.github/workflows/pal-ci.yml`, calibrated from the nearest ci.yml analogue with headroom (build+test jobs ~20, grep/symbol gates ~10, `sdl3-tests` higher until its SDL3 source build is cached under R14).
- [ ] 1.2 Add `timeout-minutes` to all 5 jobs in `.github/workflows/module-dag.yml` (check jobs ~10, nightly build jobs ~30, `summary` ~5).
- [ ] 1.3 Add `timeout-minutes` to both jobs in `.github/workflows/sprint2-checks.yml` (`globals-registry` ~10, `multi-instance-tests` ~20).
- [ ] 1.4 Add top-level `permissions: contents: read` to `pal-ci.yml`, `module-dag.yml`, `sprint2-checks.yml` (ci.yml already has it at `ci.yml:29-30`).
- [ ] 1.5 Add to all four workflows: `concurrency: { group: ${{ github.workflow }}-${{ github.ref }}, cancel-in-progress: ${{ github.event_name == 'pull_request' }} }`.
- [ ] 1.6 Verify on the PR itself: every job shows a non-default timeout in the run UI; pushing a second commit to the PR cancels the first run; a dispatch run is not cancelled by a subsequent dispatch.

## 2. Reusable build workflow (after `presets-single-source` and `master-ruleset-required-checks` are merged)

- [ ] 2.1 Confirm prerequisites: `presets-single-source` (R5) archived — workflows invoke `cmake --preset`/`ctest --preset`; `master-ruleset-required-checks` (R2) archived — `docs/ci/master-ruleset.json` exists and the ruleset is active. Do not proceed otherwise; section 1 is exempt.
- [ ] 2.2 Record the before matrix: every distinct configuration currently built per trigger tier across the four files (flag sets from `ci.yml:63-77,95-134,189-227`, `pal-ci.yml:27-114,247-265`, `module-dag.yml:127-181`, `sprint2-checks.yml:98-114`), as the checklist for 2.5 and 4.4.
- [ ] 2.3 Create `.github/workflows/build-and-test.yml` with `on: workflow_call`; inputs: runner image, configure/build/test preset names, extra ctest args, artifact-upload toggle; `permissions: contents: read`; `timeout-minutes` parameterized with a bounded default; steps: checkout → `cmake --preset` → `cmake --build --preset` → `ctest --preset` → failure-artifact upload.
- [ ] 2.4 Convert ci.yml build jobs (`linux`, `linux-ipc`, `windows`, and the nightly `linux-sdl3`/`windows-sdl3`/`macos`/`macos-sdl3`) to matrix cells calling `build-and-test.yml`, setting each caller job `name:` to its existing expanded display name; keep each job's current trigger condition unchanged.
- [ ] 2.5 Open a draft PR and read the reported check contexts (`gh pr checks` / checks API); confirm `Linux (gcc)`, `Linux (clang)`, `Linux IPC (gcc)`, `Windows (MSVC)` report under exactly those strings, accounting for `caller / callee` nesting; record the observed strings in the PR description.

## 3. Required-check name sync (same change as section 2 if any context changed)

- [ ] 3.1 If any required-check context string changed in 2.5: update `docs/ci/master-ruleset.json` with the observed strings and re-apply the ruleset (`gh api -X PUT repos/{owner}/{repo}/rulesets/{id} --input docs/ci/master-ruleset.json`) in the same change, per the `merge-gating` name-sync requirement.
- [ ] 3.2 Verify `gh api repos/{owner}/{repo}/rules/branches/master` lists exactly the contexts observed in 2.5 and that a fresh PR shows all required checks reporting (none pending-forever).

## 4. Fold the remaining callers; retire no-delta duplicates

- [ ] 4.1 Convert pal-ci `headless-tests`, `sdl2-tests`, `sdl3-tests` to `build-and-test.yml` calls, one cell per PAL backend; keep `sdl-firewall`, `contract-gates`, `asan-lifecycle` as-is (gate logic, not build skeleton).
- [ ] 4.2 Convert sprint2 `multi-instance-tests` to a `build-and-test.yml` call with the library-mode preset (`LEGENDS_LIBRARY_MODE=ON`), preserving its filtered-then-full test sequence via the ctest-args input.
- [ ] 4.3 Convert module-dag `build-linux`/`build-windows` to `build-and-test.yml` calls keeping their nightly/dispatch gate (`module-dag.yml:127,160`); update the `summary` job's failed/skipped logic for the new call structure.
- [ ] 4.4 Retire the no-delta duplicates: remove pal-ci `windows-build` (same configuration as ci.yml `windows`, `pal-ci.yml:253-265` vs `ci.yml:197-207`); diff the after matrix against 2.2's before matrix and show every distinct configuration still has exactly one cell at its tier — IPC, library mode, and each PAL backend included.

## 5. ABI fold

- [ ] 5.1 Extend ci.yml `abi-check` (`C ABI Verification`) to the superset: build and run `legends_abi_test`, compile `test_legends_abi.c` (both from `pal-ci.yml:237-245`), keep the existing `gcc -std=c11 -fsyntax-only` header check (`ci.yml:414-419`); job remains unconditional with no path filter.
- [ ] 5.2 Remove pal-ci `abi-c-compile` (`pal-ci.yml:216-245`) in the same PR, with a step-for-step mapping in the PR description showing each removed check now runs in `C ABI Verification`.
- [ ] 5.3 Negative test: introduce a throwaway ABI break that only the runtime `legends_abi_test` catches; confirm `C ABI Verification` fails; revert.

## 6. Verification

- [ ] 6.1 Grep `.github/workflows/` and confirm: zero jobs without `timeout-minutes`, zero workflows without `permissions:` and `concurrency:`, zero inline copies of the configure→build→test skeleton outside `build-and-test.yml` (gate-logic jobs exempt and listed).
- [ ] 6.2 Push a change touching `include/**` to a branch PR; confirm each distinct configuration builds once across all triggered workflows (no four-way Linux / two-way Windows rebuild of identical configurations).
- [ ] 6.3 Trigger `workflow_dispatch` on module-dag and pal-ci; confirm nightly-tier cells run there and not on the PR from 6.2.
- [ ] 6.4 Land one real PR through the ruleset with all required checks green under the post-consolidation names.
