## 1. Entry Point Skeleton

- [ ] 1.1 Create `scripts/preflight.py` with subcommands `scripts`, `abi`, `build`, `all`, an `--only <gate>` filter, and a `--require` flag for the ABI gate; per-gate PASS/FAIL/SKIPPED lines plus a summary table; exit non-zero iff any attempted gate fails, after all gates have run
- [ ] 1.2 Implement the gate registry: name, command (defined once), OS-reachability predicate, ordering constraint; populate with the ten CI-run check-script gates using the exact arguments from `sprint2-checks.yml:44-85` and `module-dag.yml:64-66`; exclude `check_compiler.py`
- [ ] 1.3 Launch all child gate scripts via `sys.executable`, never a bare `python` string; verify the suite runs when started with the Windows `py` launcher

## 2. Graphify Pair and ABI Gate

- [ ] 2.1 Encode the graphify gate as an inseparable ordered pair: `enrich_graphify_projectlegends.py` (with `--allow-missing-graphify`) runs first; `check_graphify_enrichment.py --strict --strict-tests fail --allow-missing-graphify` runs only after enrich succeeds; enrich failure fails the gate without running the check
- [ ] 2.2 Implement the ABI gate compiler probe (`gcc`, then `clang`, then `cl` C-mode) compiling `include/legends/legends_embed.h` with semantics mirroring `ci.yml:414-419`; label the MSVC path an approximation of CI's gcc invocation in output
- [ ] 2.3 Implement detect-and-skip: no C11 compiler found prints a named SKIPPED line stating CI covers the gate and does not fail the run; `--require` converts that skip into FAIL
- [ ] 2.4 Verify on a gcc-less Windows machine: `preflight abi` reports SKIPPED or the MSVC approximation and exits zero; `preflight abi --require` without any compiler exits non-zero

## 3. Build/Test Configurations

- [ ] 3.1 Add the OS-gated build/test configurations to the registry, mirroring the mandatory-tier flag sets (`ci.yml:63-77` gcc/clang Release, `ci.yml:108-127` IPC Debug, `ci.yml:197-207` MSVC Release) as raw-flag fallbacks with a comment pointing at `presets-single-source` (R5) for the preset switch
- [ ] 3.2 Print every OS-unreachable configuration by name with its reason ("requires gcc-13/clang-18: runs in CI"); no silent skip path exists
- [ ] 3.3 Verify `preflight all` on Windows lists the Linux-toolchain configurations as unreachable and builds/tests the reachable set; verify the converse on Linux

## 4. CI Rewiring

- [ ] 4.1 Rewrite `sprint2-checks.yml`'s gate job: replace the ten inline `python scripts/check_*.py` and graphify steps (`sprint2-checks.yml:44-85`) with one `python scripts/preflight.py scripts` step; keep job name, triggers, path filters, and the `pyyaml` install
- [ ] 4.2 Rewrite `module-dag.yml`'s include-rules step (`module-dag.yml:64-66`) to `python scripts/preflight.py scripts --only check_includes`
- [ ] 4.3 Rewrite `ci.yml`'s abi-check job body (`ci.yml:414-419`) to `python scripts/preflight.py abi --require`, preserving the header-guard check the job also performs
- [ ] 4.4 Grep the three workflows after rewiring: no inline `scripts/check_*.py`, `enrich_graphify`, or `gcc -std=c11` gate command remains in their step bodies

## 5. Verification

- [ ] 5.1 Run `python scripts/preflight.py scripts` on a clean tree and confirm gate-for-gate parity with the last green sprint2 run (same checks, same arguments, same verdicts)
- [ ] 5.2 Break one gate deliberately (e.g. introduce a conflict marker), confirm preflight fails locally and the rewired CI job fails on the same tree with the same gate named, then revert
- [ ] 5.3 Confirm a full CI cycle is green on the rewired workflows before merge; rollback path is reverting the workflow commit (the script is inert without consumers)
- [ ] 5.4 Document the entry point in `CONTRIBUTING.md`: one line per tier (`preflight scripts`, `preflight all`), the `pyyaml` prerequisite, and the OS-residue contract
