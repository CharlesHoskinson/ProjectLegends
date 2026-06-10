# Design: fuzz-corpus-persistence

## Context

The `fuzz` job (.github/workflows/ci.yml:478-578) builds five libFuzzer targets with clang-18 + ASan (.github/workflows/ci.yml:497-509) and runs on PRs, pushes to master, nightly cron, and dispatch (.github/workflows/ci.yml:482-486). Its corpus handling defeats coverage-guided fuzzing: the seed corpus is regenerated from `generate_fuzz_corpus` into `build/tests/fuzz/corpus` on every run (.github/workflows/ci.yml:511-512), so each execution re-explores the same shallow frontier; `tests/fuzz/CMakeLists.txt:46-49` would copy a committed `tests/fuzz/corpus/` into the build tree, but no such directory exists in the tree; no cache or artifact step exists in the job, so crash reproducers are destroyed with the runner (audit-wiki/wiki/entities/Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism).md, Fuzz section). PR and push runs fuzz 30s per target (.github/workflows/ci.yml:515-538), other triggers 60s (.github/workflows/ci.yml:540-578) — both below the 600s CIFuzz documented floor (audit-wiki/wiki/sources/Continuous Fuzzing in CI (2026-06).md, practice 2). `fuzz_input_injection` fuzzes with no corpus directory at all (.github/workflows/ci.yml:530-532). The lane failed 6 of 6 sampled executions (audit-wiki/wiki/sources/CI Run History (2026-06).md). Save-state deserialization is the documented attack surface with a prior heap-overflow finding (audit-wiki/wiki/sources/Memory Safety Audit (2026-06).md).

Binding modifications from the adversarial review (audit-wiki/wiki/syntheses/Recommendation Review (2026-06).md rows T-4, G-8): raise `timeout-minutes: 15` before funding 5×600s nightly; triage the red lane before persisting a corpus that may bake in failing inputs; the nightly cron already exists, so the split is wiring, not new infra.

## Goals / Non-Goals

**Goals:**
- Corpus survives across runs: cache for the generated corpus, committed seeds for reproducers, nightly prune.
- Every crash leaves a downloadable artifact.
- PR tier is a deterministic replay gate; nightly tier owns exploration at a funded budget.
- Resource-limit exits (OOM, slow input) are distinguishable from memory-safety crashes in triage.

**Non-Goals:**
- Triaging the currently red lane to green — owned by `ci-stabilize-mandatory-lanes` (R1) and sequenced strictly before this change.
- Gating-tier or required-check policy (R1/R2 territory).
- New fuzz targets (the unfuzzed IPC boundary is a named candidate in Security Audit (2026-06) — separate scope).
- Affected-target selection on PRs (ClusterFuzzLite's coverage-guided selection; see Alternatives).
- Format dictionaries and captured real save-state seeds (Continuous Fuzzing in CI, practice 6) — high-leverage but separable; tracked as an open question.

## Decisions

**D1 — Two-layer corpus persistence: `actions/cache` for the generated corpus, git for reproducer seeds.**
Per-target cache over `build/tests/fuzz/corpus/<target>` with a per-target key and `restore-keys` falling back to the latest entry; `generate_fuzz_corpus` runs only when the cache misses (cold-start seeder, not every-run overwriter). Curated seeds — crash reproducers after minimization, plus a small set of valid inputs per format — are committed under `tests/fuzz/corpus/<target>/`, which activates the existing copy hook (tests/fuzz/CMakeLists.txt:46-49) so local builds and CI see the same seed floor. Rationale: this is the documented reconciliation of the corpus-location dispute — small curated seed corpus in revision control, large generated corpus in external storage where its churn does not pollute history (Continuous Fuzzing in CI, practice 1 conflict note). Alternative rejected: committing the whole generated corpus — churn and size belong in a cache, not git history. Alternative rejected: a separate corpus storage repo (the ClusterFuzzLite pattern) — adds a second repository to administer before the in-repo mechanism has been tried.

**D2 — Nightly `-merge=1` prune keeps the cache minimal.**
The nightly run merges the cached corpus into a fresh minimized set (`-merge=1 NEW_DIR FULL_DIR`) before saving the cache. Corpus pruning is documented as mandatory once batch accumulation starts (Continuous Fuzzing in CI, practice 1). Without it the cache grows monotonically against the shared 10 GB Actions quota.

**D3 — Crash artifacts: `-artifact_prefix` plus `upload-artifact` on failure.**
Every fuzzer invocation gets `-artifact_prefix=<job-artifact-dir>/`; the job gains an `actions/upload-artifact` step with `if: failure()` covering that directory. Rationale: every documented CI integration treats this as mandatory plumbing; without it the lane produces red checkmarks instead of bug reports (Continuous Fuzzing in CI, practice 4). G-8 notes the side benefit: the Windows contributor downloads the reproducer instead of re-running a Linux-only lane.

**D4 — PR tier becomes deterministic replay, not short fuzzing.**
The PR step passes the committed seed files and known reproducers to each `fuzz_*` binary as a file list — libFuzzer's documented regression-test mode: files re-run as test inputs, no mutation (Continuous Fuzzing in CI, practice 2 conflict note). ASan stays active. Rationale: 30s on a regenerated corpus is below every documented floor and cannot reach deep states — fuzzing theater occupying a job slot; replay is cheap, deterministic, and catches regressions of every fixed bug forever. This also supplies the regression-vs-new-bug separation the hand-rolled job lacks (practice 3): the replay set contains only vetted inputs, so a PR red is always attributable to the PR. Alternative rejected: funding PR fuzzing to the 600s floor — burns PR latency on nondeterministic exploration whose proper home is the cron, and reintroduces unrelated-failure reds.

**D5 — Nightly owns exploration; timeout raised before funding.**
The existing 03:00 cron (.github/workflows/ci.yml:25-27) runs each of the five targets at 600s+ (`-max_total_time`), replacing the 60s steps. Ordering is binding (T-4): `timeout-minutes` on the job is raised first — 15 minutes cannot host 5×600s plus build — in its own commit, then the durations are funded. New crashes surface only here, with artifacts uploaded per D3; the triage loop is minimize (`-minimize_crash=1`), commit under `tests/fuzz/corpus/<target>/`, and the PR replay regression-tests it permanently.

**D6 — Per-target invocations get explicit resource limits so failures classify.**
`fuzz_engine_memory_blob` currently runs `-max_len=1048576` (.github/workflows/ci.yml:524-528) against the default `-rss_limit_mb=2048` and a default 1200s per-input `-timeout` longer than the whole step budget — an OOM or slow input is indistinguishable from a crash in the log (Continuous Fuzzing in CI, practice 4). Set explicit `-rss_limit_mb` and `-timeout` consistent with each target's `-max_len`, so an uploaded artifact named `oom-*`/`timeout-*`/`crash-*` states its own class. `fuzz_input_injection` gets a corpus directory like every other target (currently none, .github/workflows/ci.yml:530-532).

**D7 — Alternative considered explicitly: ClusterFuzzLite. Decision: in-repo wiring first; adopt ClusterFuzzLite later if it proves insufficient.**
ClusterFuzzLite is the eligible managed option — hosted OSS-Fuzz and CIFuzz are out (admission bar: "significant user base and/or critical to the global IT infrastructure"; CIFuzz requires OSS-Fuzz integration), while ClusterFuzzLite runs natively on GitHub Actions and packages, as configuration, everything D1-D6 builds by hand: storage-repo corpus persistence, 600s code-change fuzzing scoped to affected targets, continuous-build novelty filtering, crash artifact upload, prune and coverage crons (Continuous Fuzzing in CI, practice 5). The five targets already use the `LLVMFuzzerTestOneInput` ABI, so integration cost is a `.clusterfuzzlite/` Dockerfile plus a build script re-expressing the existing CMake invocation. Reasons to defer rather than adopt now: (a) the OSS-Fuzz base container's pinned clang must cope with the C++23 codebase — an unverified compatibility risk; (b) the engine build's size makes the continuous-builds artifact quota warning live; (c) required-check semantics are easier to reason about over a single in-repo replay job than a matrixed external action; (d) G-8 found the split is wiring on infrastructure that already exists. The in-repo design deliberately mirrors ClusterFuzzLite's lane structure (replay gate / batch cron / prune), so a later adoption replaces mechanisms without changing the model. Re-evaluation trigger: if corpus cache eviction, novelty filtering, or affected-target selection become recurring manual burdens, adopt ClusterFuzzLite for the batch + prune lanes and keep the in-repo replay as the required check.

## Risks / Trade-offs

- [Persisted corpus bakes in failing inputs if the lane is still red when caching lands] → Hard sequencing: this change lands only after `ci-stabilize-mandatory-lanes` has the fuzz lane deterministically green (T-4 binding modification). The cache key is also versioned so a poisoned corpus can be abandoned by bumping the key.
- [`actions/cache` eviction (7-day unused / 10 GB repo quota) silently loses the generated corpus] → Committed seeds set the recovery floor; nightly runs touch the cache daily, keeping it warm; the prune in D2 keeps it small. Loss degrades exploration depth, never correctness.
- [Cache poisoning: a corpus entry that crashes deterministically turns the nightly red permanently] → Crash inputs are written to the artifact dir (D3), not merged back; the `-merge=1` step only keeps inputs that execute cleanly under the merge run.
- [Replay set grows until PR replay is slow] → Reproducers are minimized before commit (D5); seed directories are curated, not accumulative — the generated corpus stays in the cache layer.
- [Funded nightly surfaces a backlog of pre-existing crashes as red nightlies] → Expected and desired post-triage; each becomes artifact → minimize → committed reproducer → tracked issue. The PR gate is insulated by design (D4).
- [Committed binary seeds in a GPL/MIT-split tree] → Seeds are data, not code; they live under `tests/fuzz/` which is already in the GPL lane with the harnesses.

## Migration Plan

1. (Prerequisite, separate change) fuzz lane green under `ci-stabilize-mandatory-lanes`.
2. Raise `timeout-minutes` on the fuzz job (zero-risk, lands first per T-4).
3. Add `-artifact_prefix` + `upload-artifact` on failure (D3) and explicit per-target limits (D6) — pure observability, no gating change.
4. Add per-target cache with `generate_fuzz_corpus` as cold-start fallback (D1) and the nightly `-merge=1` prune (D2).
5. Create `tests/fuzz/corpus/<target>/` seed directories (activates the copy hook); convert the PR step to file-list replay (D4).
6. Fund the nightly to 600s+ per target (D5).
Rollback: each step is an independent revert; reverting D4 restores the previous 30s smoke; bumping the cache key abandons a bad corpus without touching git history.

## Open Questions

- Seed/dictionary investment (Continuous Fuzzing in CI, practice 6): captured real save-states and per-format `.dict` files are the highest-leverage exploration improvement for the load_state targets — same files, separable change; decide whether to fold into step 5 or track separately.
- Whether the nightly should adopt `-fork=N` so one crash does not end a 600s session early (libFuzzer fork mode, practice 4) — decide from the first weeks of funded-nightly behavior.
- Cache granularity: one cache entry per target vs. one entry for all five — per-target keys are the default for independent eviction; revisit if quota pressure appears.
