# Change: fuzz-corpus-persistence

## Why

The fuzz lane discards everything it learns: CI regenerates the seed corpus from scratch on every run (.github/workflows/ci.yml:511-512), no `actions/cache` or `upload-artifact` step exists anywhere in the job (.github/workflows/ci.yml:478-578), and crash reproducers written by libFuzzer die with the runner — a 6/6-failing lane has been producing red checkmarks instead of bug reports (audit-wiki/wiki/entities/Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism).md; audit-wiki/wiki/sources/Continuous Fuzzing in CI (2026-06).md). The CMake hook that would copy a committed `tests/fuzz/corpus/` into the build tree exists and is dead (tests/fuzz/CMakeLists.txt:46-49). This implements CI-THESIS.md recommendation R10.

## What Changes

- Persist the corpus: per-target `actions/cache` over `build/tests/fuzz/corpus`, with `generate_fuzz_corpus` demoted from every-run overwriter to cold-start seeder, plus a nightly `-merge=1` prune so the cache does not accrete redundant entries.
- Commit reproducer seeds under `tests/fuzz/corpus/<target>/`, activating the existing dead copy hook (tests/fuzz/CMakeLists.txt:46-49). The prior save-state heap-overflow reproducer belongs there (audit-wiki/wiki/sources/Memory Safety Audit (2026-06).md).
- Capture crash artifacts: `-artifact_prefix` on every fuzzer invocation and an `actions/upload-artifact` step with `if: failure()` — crash files become downloadable instead of requiring a re-run (Recommendation Review row G-8: improves the Windows contributor's position).
- **BREAKING**: convert the PR-tier step from 30s-per-target fuzzing (.github/workflows/ci.yml:515-538) to deterministic replay of committed seeds plus known reproducers (libFuzzer file-list mode, ASan still active). PR red then means "a known input broke", never "someone else's undiscovered bug surfaced on my PR".
- Fund real exploration on the existing 03:00 nightly cron (.github/workflows/ci.yml:25-27) at 600s+ per target, replacing the 60s steps (.github/workflows/ci.yml:540-578); raise the job `timeout-minutes` before funding it (Recommendation Review row T-4: 15 minutes cannot host 5×600s).
- Classify resource-limit exits: `fuzz_engine_memory_blob` runs `-max_len=1048576` against default `-rss_limit_mb=2048` and a default 1200s `-timeout` exceeding the step budget, so OOM/slow-input failures masquerade as crashes unless the artifact is captured and classified (Continuous Fuzzing in CI, practice 4).

Sequencing constraint (binding, Recommendation Review row T-4): the currently red lane is triaged first — under change `ci-stabilize-mandatory-lanes` — so a persisted corpus does not bake in failing inputs.

## Capabilities

### New Capabilities

- `continuous-fuzzing`: corpus persistence across runs, committed reproducer seeds, crash-artifact capture, the PR-replay/nightly-exploration split, and the funding floor for scheduled fuzzing.

### Modified Capabilities

(none — the fuzz lane's gating tier is owned by `ci-stabilization` via change `ci-stabilize-mandatory-lanes`; this change alters what the lane runs, not where it gates)

## Impact

- `.github/workflows/ci.yml` — `fuzz` job: cache steps, corpus seeding, PR replay step, nightly fuzz steps, `-artifact_prefix`, artifact upload, `timeout-minutes`.
- `tests/fuzz/corpus/<target>/` — new committed seed directories (activates tests/fuzz/CMakeLists.txt:46-49).
- Targets covered (five): `fuzz_legends_load_state`, `fuzz_engine_load_state`, `fuzz_engine_memory_blob`, `fuzz_input_injection`, `fuzz_config_parser` (tests/fuzz/CMakeLists.txt:114, 140, 169, 198, 224). `fuzz_input_injection` currently fuzzes with no corpus directory at all (.github/workflows/ci.yml:530-532).
- Dependencies: sequenced after `ci-stabilize-mandatory-lanes` (lane triage); independent of the other R-series changes (CI-THESIS.md sequencing note 8).
- Downstream: the committed-reproducer loop becomes the regression mechanism for every future fuzz finding.
