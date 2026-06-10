## 1. TSan suppression bring-up

- [ ] 1.1 Build the `tsan` preset locally, run ctest, and capture every distinct race report; map each to a family (engine `g_active_instance`, `CrashBreadcrumb::add()`, intentional wrong-thread tests, anything new). Verify: a written triage list with one stack sample per family.
- [ ] 1.2 File one tracked issue per race family; each issue names the racing symbol(s) and its fix-and-remove-suppression exit criterion.
- [ ] 1.3 Create `tsan-suppressions.txt` at repo root: header comment stating hygiene policy (one entry per root cause, issue link mandatory, no module-wide globs); `race:g_active_instance`-style entries for globals; function-frame entries elsewhere; each entry preceded by its issue link. Verify: every entry has an issue link; no entry matches more than its family.
- [ ] 1.4 Gate the intentional wrong-thread tests out of TSan runs (compile-time guard or a `tsan-excluded` CTest label per design D1/open question); confirm non-TSan lanes still run them. Verify: test count unchanged in the `linux` job, reduced only under TSan.
- [ ] 1.5 Wire `suppressions=` into the `thread` matrix env (`TSAN_OPTIONS`, .github/workflows/ci.yml:360) and add `llvm-18` to the sanitizers install step (.github/workflows/ci.yml:379-381). Verify: a dispatch run shows suppressions matching (TSan report count zero, `llvm-symbolizer` resolving frames).
- [ ] 1.6 Add the same `TSAN_OPTIONS` suppressions path to the `tsan` test preset in `CMakePresets.json`. Verify: local `ctest --preset tsan` is green with the file, red without it.
- [ ] 1.7 Remove `allow_failure: true` from the `thread` matrix entry (.github/workflows/ci.yml:361) and delete the stale exit-plan comment (.github/workflows/ci.yml:351-356), replacing it with a pointer to `tsan-suppressions.txt` and the tracking issues. Verify: a seeded test race fails the workflow; reverting the seed restores green.

## 2. MSan retirement

- [ ] 2.1 File the re-entry issue: condition is an MSan-instrumented libc++ plus instrumented dependency surface (engine, SDL); re-entry placement nightly-only; no `msan` preset while retired.
- [ ] 2.2 Delete the `memory` matrix entry and its comment block (.github/workflows/ci.yml:362-373); confirm `tests/fuzz/CMakeLists.txt` `ENABLE_MSAN` paths are unreferenced by CI and leave them for local use. Verify: matrix expands to `address, undefined, thread` on a dispatch run; the workflow references the re-entry issue in the removal commit/PR.

## 3. ASan/UBSan/fuzz triage to green

- [ ] 3.1 Reproduce the `address` and `undefined` leg failures locally (`asan` preset mirrors the flags; note CI splits the legs, .github/workflows/ci.yml:343-350); record one issue per root cause.
- [ ] 3.2 Fix root causes where viable; quarantine the remainder with issue-linked `DISABLED_` (pattern: tests/integration/test_ipc_integration.cpp:42). No assertion deletions or relaxations. Verify: both legs green on dispatch; every `DISABLED_` added has an issue link in the adjacent comment.
- [ ] 3.3 Reproduce the fuzz job failures (`fuzz-all` + `generate_fuzz_corpus`, smoke commands at .github/workflows/ci.yml:514-537); attach reproducer inputs to per-crash issues; fix crashes reachable in the smoke window. Verify: `fuzz` job green on dispatch and on a PR run.

## 4. Dependency-scan fix and unmute

- [ ] 4.1 Replace the unparseable `--lockfile cmake/dependencies.cmake` invocation (.github/workflows/ci.yml:784) with supported modes (recursive scans of the vendored trees) emitting JSON the artifact step uploads (.github/workflows/ci.yml:789-794). Verify: dispatch run produces a non-empty findings artifact.
- [ ] 4.2 Triage findings from the first honest run into tracked issues (or record a clean baseline).
- [ ] 4.3 Remove `|| true` (lines 784, 786) and `continue-on-error: true` (line 787) and drop "Optional" from the job display name (line 770), in the same PR as evidence of a green dispatch run. Verify: a seeded known-vulnerable manifest fails the job; baseline run passes.

## 5. Demotion rule and verification

- [ ] 5.1 Record the demotion rule where contributors see it (CONTRIBUTING.md CI section): any allow-failure/mute/retirement/trigger-narrowing/assertion-relaxation requires a tracked issue with an exit criterion; YAML comments do not count.
- [ ] 5.2 End-to-end verification: one dispatch of ci.yml shows `address`, `undefined`, `thread`, `fuzz` green and no `memory` job; nightly (or dispatch) shows `dependency-scan` green and unmuted; grep of `.github/workflows/ci.yml` finds no `allow_failure`, no `|| true` in gate steps.
- [ ] 5.3 Update audit-wiki Verification Lanes entity and CI-THESIS.md R1 status once lanes hold green, so the wiki reflects enforcement reality.
