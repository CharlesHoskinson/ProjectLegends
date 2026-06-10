# Sprint 0 Implementation Audit — 2026-06-10

Auditor: Claude (Fable 5). Subject: GPT 5.5 Codex implementation of Sprint 0
("Stop the bleeding") on branch `sprint-0/stop-the-bleeding` (HEAD `3ff9754`,
5 commits off master `ce6a847`). Method: git-diff review of all 11 changed
files, adversarial source analysis, independent re-build + re-run of the two
regression tests, independent 60s fuzz run, independent actionlint, and
verification of every handoff attestation against the diff.

## Verdict: PASS (5/5 items), no code defects found.

This is high-quality work. Every fix is genuine (not cosmetic), every regression
test is real and exploit-shaped, scope discipline held exactly, and the new code
introduces no new out-of-bounds reads. Independent verification corroborated the
handoff on every dimension checked.

## Per-item findings

### 0.1 mem-01 (CRITICAL save-state heap overflow) — PASS, genuine
- Root cause removed: the three lines that overwrote `ctx->memory.size/pages/handler_pages`
  from blob contents (`dosbox_library.cpp` ~1355 pre-fix) are deleted, replaced
  by a comment that allocation fields are live-engine-owned. The separate
  DOS-*reported* page counts are still restored from the blob — a correct,
  sophisticated distinction between physical allocation (live) and reported
  memory (blob).
- Decode hardened: RAM/VRAM now decode into a local `std::vector` sized to the
  LIVE allocation (`ctx->memory.size` / `vga_mem_size()`), then memcpy `decoded`
  bytes into the live buffer. Decode capacity is independent of any blob field.
- Early reject pass added (v>=5): rejects `mem.size > live_memory_size`, parses
  the V5 sub-block directory with bounds checks, rejects RAM `orig_size` beyond
  live/serialized size and VRAM beyond `vga_mem_size()`.
- No new OOB read: the inserted reads at `ptr + header.memory_offset` and
  `ptr + ENGINE_STATE_SIZE_V5_BASE` are preceded by `validate_offset(memory_offset)`
  at line 1154 and the `buffer_size >= header.total_size` check at 1125; the
  early-pass directory/entry reads are each guarded against `header.total_size`.
- Test `LoadRejectsOversizedSerializedMemorySizeBeforeRamDecode` is genuinely
  adversarial: sets `memory.size = live+1`, re-encodes an oversized zero-RLE RAM
  blob, recomputes CRC32 (penetrating the CRC wall), loads, asserts INVALID_STATE
  AND unchanged state hash. Pre-fix this drives a real heap overflow (decode
  capacity live+1 into a live-sized buffer; ASan catches it). All V5 constants
  used are real header definitions with static_asserts (`ENGINE_STATE_SIZE_V5_BASE==792`,
  `V5_DIR_MAGIC=0x44423556`, `V5SubBlockDir`/`V5DirEntry` sized 8/16).
- Independent run: engine-state group 25/25 PASS.

### 0.2 mem-02 (HIGH create-error-path brick) — PASS, genuine
- The leak was the `catch(std::exception)` path deleting `inst` without
  destroying a live `engine_handle`, leaving the engine's `g_instance_exists`
  stuck true. New `fail_create` lambda centralizes cleanup (destroys the handle
  if non-null, resets machine, clears g_active_instance, deletes inst); the catch
  path and all early returns route through it.
- Test `CreateLateFailureReleasesEngineHandle` injects failure right after engine
  acquisition via a `LEGENDS_TESTING`-gated hook, then asserts a SUBSEQUENT
  `legends_create` succeeds — directly testing the brick scenario.
- Root `CMakeLists.txt` change (adds `LEGENDS_TESTING=1` to legends_core under
  LEGENDS_BUILD_TESTS and to legends_unit_tests) is justified: it wires the
  test-only injection hook, which is `#ifdef`-compiled-out of release builds.
- Independent run: lifecycle group 15/15 PASS.

### 0.3 CI gate re-arm (HIGH) — PASS
- `pull_request.branches` gains `develop` in ci.yml and pal-ci.yml (ci-04).
- sanitizers + fuzz jobs' `if:` now include `pull_request` and `push`-to-master;
  ASan/UBSan required (`continue-on-error: allow_failure==true`), TSan/MSan carry
  dated 2026-06-10 Sprint-7 exit-plan comments.
- The previously-dead PR-fuzz step is fixed: the job now runs on the events the
  step targets; the smoke step also wires in the new `fuzz_engine_memory_blob`.
- Independent actionlint on both workflows: exit 0.

### 0.4 lic-01 (CRITICAL root LICENSE) — PASS
- LICENSE rewritten as a multi-component overview with a per-path SPDX table.
- Explicitly does NOT resolve GPL-2.0-only vs -or-later: "the owner decision is
  reserved for the separate licensing cleanup work" — records tags as facts only.
- COPYING and NOTICE confirmed untouched (git diff empty). SPDX spot-checks held:
  `src/legends_ipc` genuinely tagged MIT as the table claims.

### 0.5 test-fuzz-05 (HIGH, partial scope) — PASS
- New `fuzz_engine_memory_blob.cpp` with a real `LLVMFuzzerCustomMutator` that
  recomputes CRC32 after mutating the RAM blob and metadata — the CRC-wall
  penetration the directive required. Seeds from genuine saved V5 states; one
  mutation strategy sets oversized `memory.size`/`orig_size` to hammer the
  mem-01 path. Instruments crc_valid_ram_inputs / rle_decode_reached /
  oversized_ram_rejections. Wired into fuzz CMake (fuzz-all, fuzz-quick) and CI.
- Independent 60s run: 228,237 execs, exit 0, ZERO crashes, rle_decode_reached
  =109552, oversized_ram_rejections=5360 (guard fires and rejects cleanly).

## Attestation verification (all confirmed against the diff)
- no_existing_assertions_weakened: TRUE — all test diffs are additions; no
  existing assertion edited or removed.
- no_out_of_scope_files_touched: TRUE — 11 files, all in scope; audit-wiki/,
  plan, COPYING, NOTICE, ROADMAP/TODO/CHANGELOG all untouched.
- no_history_rewrite_or_force_push: TRUE — linear 5-commit history on a fresh branch.
- gpl_only_vs_or_later_decision_not_made: TRUE — LICENSE explicitly reserves it.
- audit_wiki_untouched: TRUE.

## Independent verification summary
- Incremental rebuild of both test targets from committed tree: `ninja: no work
  to do`, exit 0 (binaries are current with committed source; build is clean).
- mem-01 regression + group: 25/25 PASS. mem-02 regression + group: 15/15 PASS.
- fuzz_engine_memory_blob 60s: 0 crashes. actionlint: exit 0.
- Full ctest (4512-test headline): launched separately to corroborate.

## Minor / process findings (NOT code defects; fold into next directive)
1. Handoff artifacts (`docs/superpowers/handoffs/*.md,*.json`) were left UNTRACKED,
   not committed to the branch — so `working_tree_clean=false` (honestly disclosed).
   The audit trail is stronger if the handoff is committed. → require in next XML.
2. `started_at_utc` is null (lost to context compaction). → require start-stamp at kickoff.
3. "0 new warnings" is heavily caveated and the auditor repro needs manual flag
   overrides (`-DCMAKE_CXX_FLAGS="/EHsc /wd4875"`, a `/std` override). This points
   at pre-existing dev-preset build friction on Windows (ties to backlog build-02).
   Not a Sprint 0 regression. → next XML should make the implementer surface any
   preset/flag overrides and state whether they reflect pre-existing breakage.
4. mem-01's early-pass directory parse duplicates the late decode loop's directory
   logic. Both are individually safe (decode is bounded regardless), but the
   duplicated parse is a latent drift risk. Optional cleanup, not a defect.
