# Project Legends End-to-End Review Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:dispatching-parallel-agents for the independent audit domains, then use superpowers:writing-plans for any remediation plan that changes code. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Produce a current, source-verified release-readiness review and identify the next remediation plan to execute.

**Architecture:** Treat this as a verification project before a coding project. First establish a reproducible baseline, then reconcile old audit claims against the current tree, then split the codebase into independent audit domains whose findings roll up into one prioritized next-step backlog.

**Tech Stack:** C++23, CMake, GoogleTest, CTest, GitHub Actions, TLA+, Python verification scripts, SDL2/SDL3, IPC/GPL isolation.

---

## Current Snapshot From 2026-06-08 Triage

- Repository: `CharlesHoskinson/ProjectLegends`, default branch `master`.
- Local checkout: `C:\Users\charl\ProjectLegends`.
- Pre-existing local change: `ROADMAP.md` is modified by 3994 insertions and 360 deletions. Do not overwrite it during review.
- Local build blocker: CMake 4.3.3 is installed, but no C++ compiler and no Ninja are currently on `PATH`. `build/CMakeCache.txt` is configured for Ninja with `CMAKE_MAKE_PROGRAM-NOTFOUND`.
- Lightweight policy gates already pass:
  - `python scripts/check_current_context.py --path .`
  - `python scripts/check_includes.py --path . --strict`
  - `python scripts/check_gsl_lite_usage.py --path .`
- Source spot-checks show several March P0 findings are fixed, including CRC-32 generation, IPC payload cap, SDL3 zero-channel validation, SDL3 mouse shutdown null-window removal, invalid-handle destroy behavior, and `legends_step_cycles()` context-pointer error handling.
- Still-open release concerns found in source:
  - `src\pal\sdl2\audio_sink_sdl2.cpp`: `volume_`, `dropped_frames_`, and `paused_` are still plain fields touched across audio/main threads.
  - `src\app\error_reporter.cpp`: all public methods are no-ops.
  - `src\app\crash_reporter.cpp`: `install`, `uninstall`, `enable`, and `disable` are no-ops or unconditional success.
  - `src\app\ssim.cpp`: one-line stub.
  - `src\legends_ipc\protocol.cpp`: one-line stub but included in `legends_ipc`.
  - `src\app\update_checker_linux.cpp` and `src\app\update_checker_mac.cpp`: fetch path returns empty.
  - Integration stubs still skip: `test_cross_platform_smoke.cpp`, `test_determinism_hash.cpp`, `test_frame_timing.cpp`, `test_golden_visual.cpp`, `test_pairwise_config.cpp`, `test_replay_determinism.cpp`, `test_save_state_compat.cpp`, and `test_visual_regression.cpp`.

## Task 1: Establish A Reproducible Baseline

**Files:**
- Read: `CMakePresets.json`
- Read: `CMakeLists.txt`
- Read: `CONTRIBUTING.md`
- Read: `.github/workflows/ci.yml`
- Create during execution: `docs/superpowers/reviews/2026-06-08-baseline.md`

- [ ] **Step 1: Record git state without touching user edits**

Run:
```powershell
git -c safe.directory=C:/Users/charl/ProjectLegends -C C:\Users\charl\ProjectLegends status --short --branch
git -c safe.directory=C:/Users/charl/ProjectLegends -C C:\Users\charl\ProjectLegends diff --name-status
```

Expected: `ROADMAP.md` is the only modified file unless the user has added more changes.

- [ ] **Step 2: Record local toolchain state**

Run:
```powershell
cmake --version
ninja --version
python scripts/check_compiler.py --json
Get-Command gcc,g++,clang,clang++,cl,mingw32-make,make,nmake -ErrorAction SilentlyContinue | Select-Object Name,Source,Version
```

Expected today: CMake exists; Ninja and C++ compilers are missing from `PATH`.

- [ ] **Step 3: Choose the first verification lane**

Use this order:
1. If Visual Studio Build Tools are available, configure `cmake -B build-vs -G "Visual Studio 17 2022" -A x64 -DLEGENDS_BUILD_TESTS=ON -DLEGENDS_HEADLESS=ON`.
2. If MinGW is available, configure `cmake --preset dev-mingw`.
3. If neither local compiler lane exists, run verification through GitHub Actions or install a compiler plus Ninja before claiming build/test status.

- [ ] **Step 4: Save the baseline note**

Create `docs/superpowers/reviews/2026-06-08-baseline.md` with:
- git branch and dirty files
- local tools available/missing
- chosen verification lane
- exact commands run
- exact pass/fail/blocker result

## Task 2: Run Cheap Source Policy Gates

**Files:**
- Read: `scripts/check_current_context.py`
- Read: `scripts/check_includes.py`
- Read: `scripts/check_gsl_lite_usage.py`
- Create during execution: `docs/superpowers/reviews/2026-06-08-policy-gates.md`

- [ ] **Step 1: Run context policy**

Run:
```powershell
python scripts/check_current_context.py --path .
```

Expected from triage: `OK: No current_context() violations in production code`.

- [ ] **Step 2: Run include boundary policy**

Run:
```powershell
python scripts/check_includes.py --path . --strict
```

Expected from triage: `OK: All include rules passed`.

- [ ] **Step 3: Run gsl-lite policy**

Run:
```powershell
python scripts/check_gsl_lite_usage.py --path .
```

Expected from triage: `OK: No forbidden gsl-lite patterns found`.

- [ ] **Step 4: Save policy gate output**

Create `docs/superpowers/reviews/2026-06-08-policy-gates.md` with command output summaries and any exceptions.

## Task 3: Reconcile Old Audit Claims Against Current Source

**Files:**
- Read: `AUDIT_REPORT.md`
- Read: `AUDIT.md`
- Read: `TODO.md`
- Read: `docs/superpowers/plans/2026-03-20-audit-remediation-master.md`
- Read: `docs/superpowers/plans/2026-03-20-plan-1-critical-bugs.md`
- Create during execution: `docs/superpowers/reviews/2026-06-08-audit-refresh.md`

- [ ] **Step 1: Build a current finding table**

Create a table with columns:
`Old Finding`, `Current Status`, `Evidence`, `Risk`, `Recommended Disposition`.

Use these statuses only:
- `verified fixed`
- `still open`
- `partially fixed`
- `needs build/test confirmation`
- `obsolete`

- [ ] **Step 2: Verify the March P0/P1 sample set**

Run:
```powershell
rg -n "computeCRC32|kCRC32Table|KnownVector|HelloWorld" src/app/save_manager.cpp tests/unit/test_save_manager.cpp
rg -n "kMaxPayloadSize|payload_size >|RejectsOversized" include/legends_ipc/message_codec.h src/legends_ipc/message_codec.cpp tests/unit/test_ipc_message_codec.cpp
rg -n "channels == 0|sample_rate == 0|SDL_SetWindowRelativeMouseMode" src/pal/sdl3 tests/unit/test_pal_audio_sink.cpp
rg -n "std::atomic<bool> connected_|reinterpret_cast<legends_handle>" src/legends_proxy
rg -n "volume_|dropped_frames_|audioCallback" src/pal/sdl2/audio_sink_sdl2.cpp
rg -n "Stub|not yet implemented|GTEST_SKIP" src tests/integration
```

Expected: classify each old issue with source evidence, not memory or old docs.

- [ ] **Step 3: Save the refresh document**

Save `docs/superpowers/reviews/2026-06-08-audit-refresh.md` and do not edit `AUDIT_REPORT.md` until the refresh has been reviewed.

## Task 4: Dispatch Independent Domain Reviews

**Files:**
- Create during execution: `docs/superpowers/reviews/2026-06-08-domain-embedding.md`
- Create during execution: `docs/superpowers/reviews/2026-06-08-domain-ipc-gpl.md`
- Create during execution: `docs/superpowers/reviews/2026-06-08-domain-pal-app.md`
- Create during execution: `docs/superpowers/reviews/2026-06-08-domain-security-ai-config.md`
- Create during execution: `docs/superpowers/reviews/2026-06-08-domain-tests-ci.md`

- [ ] **Step 1: Embedding, determinism, save-state**

Review:
- `include/legends/legends_embed.h`
- `src/legends/legends_embed_api.cpp`
- `engine/src/misc/dosbox_library.cpp`
- `engine/src/misc/cpu_bridge.cpp`
- `tests/unit/test_legends_embed*.cpp`
- `tests/integration/test_workflow_*.cpp`

Questions:
- Are all public ABI calls honest about success, failure, and unsupported features?
- Does save/load preserve the documented observable state?
- Are determinism tests meaningful or synthetic?

- [ ] **Step 2: IPC and GPL isolation**

Review:
- `include/legends_ipc`
- `src/legends_ipc`
- `src/legends_proxy`
- `src/legends_engine_host`
- `scripts/verify_gpl_isolation.py`
- IPC CI jobs in `.github/workflows/ci.yml`

Questions:
- Is process isolation actually exercised in CI?
- Are message sizes, sequence IDs, shared memory, reconnects, and process crashes handled defensively?
- Does `src/legends_ipc/protocol.cpp` need implementation or removal?

- [ ] **Step 3: PAL and app shell**

Review:
- `include/pal`
- `src/pal`
- `src/app`
- `tests/unit/test_pal_*.cpp`
- `tests/unit/test_*audio*.cpp`

Questions:
- Are SDL2/SDL3/headless behavior and tests equivalent where intended?
- Are app-level components real, stubbed, or intentionally deferred?
- Are thread-affinity, audio callback, and UI/event-loop interactions safe?

- [ ] **Step 4: Security, AI, config, mounts**

Review:
- `src/app/config_parser.cpp`
- `src/app/ai_*`
- `src/app/mount_manager.*`
- `src/app/image_validator.*`
- `tests/unit/test_config_parser.cpp`
- `tests/unit/test_ai_*.cpp`
- `tests/integration/test_mount_lifecycle.cpp`
- `docs/security`

Questions:
- Are field limits and path confinement enforced by code and tests?
- Is the AI prompt/response boundary explicit enough to resist guest-controlled text injection?
- Are secrets and update checks handled consistently across platforms?

- [ ] **Step 5: Tests, CI, fuzzing, TLA+**

Review:
- `tests`
- `tests/fuzz`
- `.github/workflows`
- `spec/tla`
- `TLA_CONFORMANCE.md`
- `tlaAudit.md`

Questions:
- Which release-gate tests still skip?
- Does CI build every mode that is claimed release-relevant?
- Do fuzz/TLA jobs cover the same invariants claimed by docs?

## Task 5: Run Build And Test Gates

**Files:**
- Create during execution: `docs/superpowers/reviews/2026-06-08-build-test-results.md`

- [ ] **Step 1: Configure headless tests**

Preferred command once a compiler and generator are available:
```powershell
cmake --preset dev-mingw
```

Alternative Visual Studio lane:
```powershell
cmake -B build-vs -G "Visual Studio 17 2022" -A x64 -DLEGENDS_BUILD_TESTS=ON -DLEGENDS_HEADLESS=ON
```

Expected: configure completes without missing compiler/generator errors.

- [ ] **Step 2: Build test targets**

Run one of:
```powershell
cmake --build build/dev-mingw --parallel
cmake --build build-vs --config Debug --parallel
```

Expected: `legends_unit_tests`, `legends_integration_tests`, `legends_abi_test`, and toolchain tests build.

- [ ] **Step 3: Run non-soak tests**

Run one of:
```powershell
ctest --test-dir build/dev-mingw --output-on-failure --label-exclude soak
ctest --test-dir build-vs -C Debug --output-on-failure --label-exclude soak
```

Expected: no failures. Skipped tests must be listed and classified as intentional, release-blocking, or obsolete.

- [ ] **Step 4: Run IPC lane**

Run:
```powershell
cmake -B build-ipc -G Ninja -DCMAKE_BUILD_TYPE=Debug -DLEGENDS_BUILD_TESTS=ON -DLEGENDS_HEADLESS=ON -DLEGENDS_USE_IPC=ON
cmake --build build-ipc --parallel
ctest --test-dir build-ipc --output-on-failure
```

Expected: IPC tests build and run; `legends_engine_host` exists.

- [ ] **Step 5: Save build/test results**

Create `docs/superpowers/reviews/2026-06-08-build-test-results.md` with:
- configure/build/test commands
- pass/fail/skipped counts
- first failure per failing domain
- environment/toolchain details

## Task 6: Decide The Next Remediation Plan

**Files:**
- Create during execution: `docs/superpowers/plans/YYYY-MM-DD-<remediation-topic>.md`

- [ ] **Step 1: Prioritize findings**

Use this severity rule:
- `P0`: security flaw, crash/data race, false success from stubbed code, ABI contract violation, release-gate test missing for core claim.
- `P1`: correctness risk, CI coverage gap, platform inconsistency, important docs mismatch.
- `P2`: cleanup, modernization, docs polish, deferred feature wiring.

- [ ] **Step 2: Select exactly one next remediation plan**

Recommended based on 2026-06-08 triage:
1. `P0 Release Honesty and Runtime Safety`: fix SDL2 audio data race, no-op reporter false success, one-line SSIM/protocol stubs, and skipped release-gate tests.
2. `P1 Build Baseline and CI Parity`: unblock local build, align CMake presets with available generator lanes, and ensure CI covers headless, IPC, SDL2/SDL3, fuzz, and TLA claims.
3. `P1 Security and Config Truth`: verify field limits, mount path confinement, AI prompt/response boundaries, update checks, and secret-handling claims.

- [ ] **Step 3: Write the implementation plan**

Use superpowers:writing-plans. Save the chosen remediation plan under `docs/superpowers/plans/` with exact files, tests, commands, and commits.

## Recommended Immediate Next Step

Do **Task 1** first. The codebase cannot be honestly reviewed end-to-end until a reproducible build/test lane exists. In parallel, start **Task 3** to refresh the stale March audit findings against the current source. Do not begin broad refactoring or feature work until the build baseline and audit-refresh table exist.
