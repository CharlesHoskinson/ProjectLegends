# Tasks: fuzz-corpus-persistence

Prerequisite: the fuzz lane is deterministically green under `ci-stabilize-mandatory-lanes` (Recommendation Review row T-4 — do not persist a corpus that bakes in failing inputs). Tasks 1.x are safe to land before that point; 3.x onward are not.

## 1. Observability first (no gating change)

- [ ] 1.1 Raise `timeout-minutes` on the `fuzz` job to accommodate build plus five 600s targets plus merge/prune (T-4 ordering: timeout before funding). Verify: a dispatch run completes within the new bound.
- [ ] 1.2 Add `-artifact_prefix=<artifact-dir>/` to every fuzzer invocation in the smoke and nightly steps (.github/workflows/ci.yml:514-578) and an `actions/upload-artifact` step with `if: failure()` over that directory. Verify: a locally seeded crashing input produces a downloadable `crash-*` artifact on a dispatch run.
- [ ] 1.3 Set explicit `-rss_limit_mb` and per-input `-timeout` on each target consistent with its `-max_len` (notably `fuzz_engine_memory_blob`, `-max_len=1048576` at .github/workflows/ci.yml:524-528, against default `rss_limit_mb=2048` and default 1200s timeout). Verify: an over-RSS input yields an `oom-*` artifact, not a generic crash.

## 2. Corpus cache layer

- [ ] 2.1 Add per-target `actions/cache` over `build/tests/fuzz/corpus/<target>` with versioned per-target keys and `restore-keys` fallback to the latest entry. Verify: second consecutive dispatch run logs a cache hit per target.
- [ ] 2.2 Make `generate_fuzz_corpus` (.github/workflows/ci.yml:511-512) conditional on cache miss — cold-start seeder, never an overwriter of a restored corpus. Verify: on a warm run the generator step is skipped and the corpus carries entries not produced by the generator.
- [ ] 2.3 Add the nightly `-merge=1` prune: merge each target's corpus into a fresh minimized directory before the cache save step. Verify: post-prune corpus is no larger than pre-prune and a follow-up run's coverage does not regress.

## 3. Committed seeds and the copy hook

- [ ] 3.1 Create `tests/fuzz/corpus/<target>/` for all five targets (`fuzz_legends_load_state`, `fuzz_engine_load_state`, `fuzz_engine_memory_blob`, `fuzz_input_injection`, `fuzz_config_parser`) with a small curated seed set per format; include the minimized reproducer of the prior save-state heap-overflow finding (Memory Safety Audit (2026-06)) once its fix is confirmed in the triaged lane. Verify: configure-time copy hook (tests/fuzz/CMakeLists.txt:46-49) populates the build tree.
- [ ] 3.2 Give `fuzz_input_injection` a corpus directory in its CI invocation (currently none, .github/workflows/ci.yml:530-532). Verify: no fuzzer invocation in ci.yml lacks a corpus argument.
- [ ] 3.3 Document the reproducer loop in `tests/fuzz/` (README or header comment): nightly crash → artifact → `-minimize_crash=1` locally → commit under `tests/fuzz/corpus/<target>/` → PR replay covers it forever.

## 4. PR tier: deterministic replay

- [ ] 4.1 Replace the 30s-per-target PR smoke (.github/workflows/ci.yml:515-538) with file-list replay: invoke each target binary with the committed seeds and reproducers as file arguments (libFuzzer regression mode, no mutation), ASan active. Verify: step output shows N files executed, zero mutation runs; wall time well under the smoke it replaces.
- [ ] 4.2 Prove the gate both ways: a seeded reproducer for a known-fixed bug passes; reverting that fix on a scratch branch fails the replay step. Verify: both dispatch runs recorded.

## 5. Nightly tier: funded exploration

- [ ] 5.1 Raise the scheduled steps (.github/workflows/ci.yml:540-578) to `-max_total_time=600`+ per target, reading from and writing back to the cached corpus (cron already exists at .github/workflows/ci.yml:25-27). Verify: nightly run logs ≥600s per target and the cache save succeeds after prune.
- [ ] 5.2 Confirm new-crash flow end to end on the first funded nightlies: crash → uploaded artifact → issue with reproducer attached. Verify: process exercised on at least one real or seeded finding.

## 6. Verification and bookkeeping

- [ ] 6.1 End-to-end check: PR run shows replay-only behavior; dispatch run shows cache hit, generator skipped, artifacts wired; nightly shows funded durations and prune. Grep ci.yml: every fuzz invocation has corpus dir, `-artifact_prefix`, explicit `-rss_limit_mb` and `-timeout`.
- [ ] 6.2 Record the ClusterFuzzLite re-evaluation trigger (design D7) as a tracked note/issue: adopt for batch + prune lanes if cache eviction, novelty filtering, or affected-target selection become recurring manual burdens.
- [ ] 6.3 Update audit-wiki Verification Lanes (Fuzz section) and CI-THESIS.md R10 status once the split lane holds, so corpus-handling facts (regeneration, dead hook, no artifacts) reflect the new reality.
