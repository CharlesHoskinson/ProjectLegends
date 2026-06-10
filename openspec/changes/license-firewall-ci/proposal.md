# Change: license-firewall-ci

## Why

The license firewall is the project's reason for its IPC architecture, and it is enforced by comments: `legends_verify_all_dags()` verifies only `legends_core`, `legends_pal`, and `aibox_core` (cmake/ModuleDAG.cmake:191-209) while the MIT↔GPL edges sit declared-but-unchecked in the manifest (cmake/ModuleManifest.cmake:63-68); `cmake/VerifyGPLIsolation.cmake` is included by nothing and degrades to `message(WARNING)` + `return()` when prerequisites are missing (cmake/VerifyGPLIsolation.cmake:16-26); `scripts/verify_gpl_isolation.py` runs in no workflow and its test suite (`tests/scripts/test_verify_gpl_isolation.py`) has no CI runner; no job anywhere checks licenses (the only scanner is vulnerability-only and advisory, .github/workflows/ci.yml:769-794); and `legends_proxy`/`legends_engine_host` are never compiled on any OS but Linux at any tier (audit-wiki/wiki/maps/CI Gate Coverage Map.md). This implements CI-THESIS.md recommendation R7 (Recommendation Review rows M-5 plus the verifier halves of A-7/T-7).

## What Changes

- Extend `legends_verify_all_dags()` and `legends_detect_cycles()` (cmake/ModuleDAG.cmake:122-124, 191-209) to the three license-critical targets `legends_ipc`, `legends_proxy`, `legends_engine_host` — activating the existing configure-time FATAL_ERROR mechanism on the exact MIT↔GPL boundary the manifest already declares (`LEGENDS_DAG_legends_proxy "legends_ipc"`, cmake/ModuleManifest.cmake:67). For the two MIT targets, add a stricter rule: no engine-prefixed or `legends_core` dependency ever, including transitively via `INTERFACE_LINK_LIBRARIES`.
- Wire the orphaned `cmake/VerifyGPLIsolation.cmake` into the IPC build (`include()` in the top-level IPC branch) and make it fail closed: a `LEGENDS_REQUIRE_GPL_VERIFICATION` option turns every missing-prerequisite `WARNING`+`return()` path into `FATAL_ERROR`; CI IPC jobs set it. The `linux-ipc` job's "Verify IPC executables exist" step (.github/workflows/ci.yml:121-124) becomes "verify the MIT binary contains no GPL symbols".
- Run `tests/scripts/test_verify_gpl_isolation.py` in CI at the same tier the verifier gates, so the gate itself is tested (Recommendation Review row T-7: the python verifier runner strengthens the firewall).
- Add a REUSE compliance job (`fsfe/reuse-action`) on push and pull request, with a `REUSE.toml` bulk-annotating the vendored `engine/` tree (`precedence = "closest"` so upstream in-file headers win) and a `LICENSES/` directory — per-file SPDX tags become the checked ground truth behind the prose `LICENSE` overview.
- Add a Windows IPC build cell (`windows-ipc`, `LEGENDS_USE_IPC=ON`) so the GPL-isolating architecture is built on more than one OS at the mandatory tier and the verifier's MSVC `/MAP` path is exercised; today `linux-ipc` is the sole job at any tier that sets `LEGENDS_USE_IPC=ON` (.github/workflows/ci.yml:116).
- Enforce the include-direction residue of the firewall: no engine-internal header (`engine/include/**`, `engine/src/**`) and no private `src/legends/**` header may be included from `src/legends_ipc/`, `include/legends_ipc/`, or `src/legends_proxy/`. The FSF shared-memory caveat itself (whether flat framebuffer/PCM shared-memory layouts are "complex internal data structures" per the FSF FAQ) is flagged for counsel and stays out of CI scope; this include rule is its CI-checkable residue (audit-wiki/wiki/sources/Vendored & License-Isolated Dependency CI (2026-06).md, conflict callout).

## Capabilities

### New Capabilities

- `license-firewall`: configure-time DAG verification of the license-critical targets, fail-closed post-build GPL-symbol scanning of MIT-side binaries, a CI-tested verifier, REUSE compliance over the whole repository including the vendored engine, include-direction enforcement across the MIT↔GPL boundary, and two-OS coverage of the IPC split.

### Modified Capabilities

- `ci-stabilization`: the Primary CI Signal requirement (openspec/specs/ci-stabilization/spec.md) enumerates the high-signal required validation set; this change extends that set with the Linux IPC lane (already running, never named), the new Windows IPC lane, and the REUSE compliance lane.

## Impact

- `cmake/ModuleDAG.cmake` — `legends_verify_all_dags()`, `legends_detect_cycles()` module list, transitive-link check for MIT targets.
- `cmake/VerifyGPLIsolation.cmake` — fail-closed option, inclusion; top-level `CMakeLists.txt` IPC branch gains the `include()` (near the stated invariants at CMakeLists.txt:362, 423).
- `.github/workflows/ci.yml` — `linux-ipc` job (verification + verifier-test steps, `-DLEGENDS_REQUIRE_GPL_VERIFICATION=ON`), new `windows-ipc` job, new `reuse` job.
- New repo files: `REUSE.toml`, `LICENSES/` (license texts for SPDX identifiers in use). Untagged project-owned files get SPDX tags or `REUSE.toml` annotations recording their currently documented status; no file is relicensed and the `-only`-vs-`-or-later` declaration stays with the maintainer (LICENSE, "License policy clarification").
- `scripts/verify_gpl_isolation.py` pattern/allowlist updates only if Windows bring-up surfaces false positives; every change gated by its test suite.
- Downstream: the master ruleset change (CI-THESIS.md R2) must add the new exact-name checks (`Windows IPC (MSVC)`, REUSE job name) to the required set in the same change that introduces them as mandatory.
