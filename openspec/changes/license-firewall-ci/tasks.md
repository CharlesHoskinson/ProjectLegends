## 1. Configure-time DAG verification of the license boundary

- [ ] 1.1 Add `if(TARGET ...)`-guarded `legends_verify_dag()` calls for `legends_ipc`, `legends_proxy`, `legends_engine_host` to `legends_verify_all_dags()` (cmake/ModuleDAG.cmake:191-209) and add the three names to `legends_detect_cycles()`'s module list (cmake/ModuleDAG.cmake:124). Verify: a clean `LEGENDS_USE_IPC=ON` configure reports all six modules verified; a non-IPC configure still passes.
- [ ] 1.2 Add the strict transitive check for the MIT targets: a function that walks `INTERFACE_LINK_LIBRARIES` from `legends_ipc` and `legends_proxy` and FATAL_ERRORs on any `aibox_core`, `legends_core`, or engine-prefixed target, reusing the `EXTERNAL_PATTERNS` classification (cmake/ModuleDAG.cmake:52-61) for leaf nodes. Verify: seeded direct (`legends_core` added to `legends_proxy`) and laundered (interface-propagated) violations both fail configure with the offending edge named; clean tree passes.
- [ ] 1.3 Update `legends_print_dag()` (cmake/ModuleDAG.cmake:220-233) to render the six-module graph including the MIT/GPL annotations from the manifest comment block (cmake/ModuleManifest.cmake:53-62).

## 2. Artifact-level isolation verification, fail-closed

- [ ] 2.1 Add `option(LEGENDS_REQUIRE_GPL_VERIFICATION ... OFF)` and convert the three degrade paths in `cmake/VerifyGPLIsolation.cmake` (no Python3, :16-19; missing script, :23-26; unknown compiler, :37-40) to `FATAL_ERROR` when the option is ON. Verify: configure with the option ON and `Python3_EXECUTABLE` pointed at a nonexistent path fails; with the option OFF it warns and continues.
- [ ] 2.2 Add `include(VerifyGPLIsolation)` to the top-level `CMakeLists.txt` after the shell target is defined in the IPC branch (near the stated invariants at CMakeLists.txt:362, 423). Verify: an IPC build emits the map file and the post-build "Verifying GPL isolation" step; the build log contains the verifier PASS line.
- [ ] 2.3 Seeded-violation proof: on a scratch branch, link a GPL object into the shell (or feed a known-bad map) and confirm the post-build step fails the build with symbols reported; revert.

## 3. CI wiring — linux-ipc

- [ ] 3.1 Add `-DLEGENDS_REQUIRE_GPL_VERIFICATION=ON` to the `linux-ipc` configure step (.github/workflows/ci.yml:108-116).
- [ ] 3.2 Add a step running `python3 tests/scripts/test_verify_gpl_isolation.py` to `linux-ipc` before the build step. Verify: the step fails the job when a verifier pattern regression is seeded locally against the same command.
- [ ] 3.3 Replace the "Verify IPC executables exist" step body (.github/workflows/ci.yml:121-124) with an assertion that the GPL-isolation scan ran and passed (grep the build log for the verifier PASS line or re-invoke the script against the produced map), keeping the existence checks. Verify: dispatch run green with the new steps visible in the log.

## 4. CI wiring — windows-ipc cell

- [ ] 4.1 Add a `windows-ipc` job (name: `Windows IPC (MSVC)`) to ci.yml mirroring the `windows` job shape (.github/workflows/ci.yml:189-220) plus `-DLEGENDS_USE_IPC=ON -DLEGENDS_REQUIRE_GPL_VERIFICATION=ON`, with `timeout-minutes` set, initially gated to `workflow_dispatch` for bring-up.
- [ ] 4.2 Bring-up: dispatch until green — this configuration compiles `shared_memory_win.cpp`, `control_channel_win.cpp`, `engine_spawner_win.cpp` (CMakeLists.txt:338-343) in CI for the first time; file an issue per real defect found; update `verify_gpl_isolation.py` patterns/allowlist only with accompanying test fixtures if MSVC maps false-positive. Verify: `legends_engine_host.exe` exists, ctest passes, the MSVC `/MAP` scan reports PASS.
- [ ] 4.3 Promote the job to the pull-request/push tier (remove the dispatch gate) in a PR that links the green rehearsal run; record the exact job name for the master-ruleset change's required-check set.

## 5. REUSE compliance

- [ ] 5.1 Create `LICENSES/` with the text of every SPDX identifier currently tagged in the tree (MIT, GPL-2.0-or-later, and any others `reuse lint` enumerates; both GPL texts if both `-only` and `-or-later` appear). No tag is edited to reduce the identifier set.
- [ ] 5.2 Create root `REUSE.toml` with `[[annotations]]` covering `engine/**` (`precedence = "closest"`, license per the `NOTICE`/`COPYING` engine status), leaving upstream files untouched.
- [ ] 5.3 Sweep project-owned untagged files (e.g. `include/legends/legends_embed.h`): add an SPDX tag matching the LICENSE table's documented status, or a `REUSE.toml` annotation where header edits are undesirable. Verify: `reuse lint` exits 0 locally; the diff contains no license-identity change to any previously tagged file.
- [ ] 5.4 Add a `reuse` job to ci.yml using `fsfe/reuse-action` on push and pull request with no path filter, landed in the same PR as the green lint state. Verify: a PR adding an untagged source file fails the job; the clean tree passes; record the job name for the ruleset handoff.

## 6. Include-direction residue check

- [ ] 6.1 Extend `scripts/check_includes.py` with the license-boundary rule: files under `src/legends_ipc/`, `include/legends_ipc/`, `src/legends_proxy/` must not include `engine/include/**`, `engine/src/**`, `dosbox/`- or `aibox/`-prefixed headers, or private `src/legends/**` headers. The public C ABI header `<legends/legends_embed.h>` stays permitted (design D7; counsel item recorded, not adjudicated). Verify: current tree passes; a seeded `#include <dosbox/dosbox.h>` in `src/legends_ipc/` fails with file and include named.
- [ ] 6.2 Confirm the rule executes at the mandatory tier (check_includes.py already runs in CI and the pre-commit hook); document the new rule in the script's header comment.

## 7. Verification and handoff

- [ ] 7.1 End-to-end dispatch of ci.yml: `linux-ipc` shows verifier tests + fail-closed configure + map-scan PASS; `windows-ipc` green; `reuse` green; seeded violations from 1.2, 2.3, 5.4, 6.1 each demonstrated to fail in their respective gate.
- [ ] 7.2 Hand the final exact job names (`Linux IPC (gcc)` unchanged, `Windows IPC (MSVC)`, REUSE job name) to the master-ruleset-required-checks change so the required set is extended in that change.
- [ ] 7.3 Update audit-wiki: CI Gate Coverage Map rows for `legends_ipc`/`legends_proxy`/`legends_engine_host` (Windows coverage, isolation gate), the Structurally Unguarded platform-gap entry, and CI-THESIS.md R7 status.
