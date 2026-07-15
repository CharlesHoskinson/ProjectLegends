# CI audit — Windows & Linux (2026-07-15)

**Branch under test:** `ci/r1-stabilize-mandatory-lanes` (PR #46)  
**Evidence:** GitHub Actions run `29423049754` and prior master nightlies.

## Snapshot (PR #46 @ e721855)

| Lane | Platform | Result | Notes |
|------|----------|--------|-------|
| Linux (gcc) | Ubuntu | **PASS** | ~5m |
| Linux (clang) | Ubuntu + libc++ | **PASS** | ~7m |
| Linux IPC (gcc) | Ubuntu | **PASS** | ~6m |
| Windows (MSVC) | windows-latest (VS 18 2026) | **FAIL** | build |
| Fuzz Testing | Ubuntu clang-18 | **FAIL** | configure |
| address / undefined / thread | Ubuntu | (pending / flaky cancel) | R1 wiring |
| Coverage | Ubuntu | PASS | |
| C ABI / Module DAG / Sprint2 | — | PASS | |

Master nightlies have been red for days (same classes of failure + optional PAL).

---

## Root causes (verified)

### W1 — Windows MSVC: gsl-lite C4875 under `/WX` (Critical for Windows green)

| | |
|--|--|
| **Symptom** | `error C2220` at `gsl-lite.hpp:2218` while building `legends_core` / `legends_ipc` |
| **Cause** | MSVC 19.51 (VS 18 2026) warns C4875 on non-string-literal `[[gsl::suppress]]`; Tier-A targets use `/WX` |
| **Not** | Project source bugs — warning is inside FetchContent gsl-lite v1.0.0 |
| **Prior art** | Issue [#44](https://github.com/CharlesHoskinson/ProjectLegends/issues/44); fix commit `7d0db36` on `ci/r1-stabilize-lanes` never merged to this branch |
| **Fix** | `/wd4875` on `legends_compile_options` (MSVC INTERFACE); keep until gsl-lite pin advances |
| **Exit** | Upgrade gsl-lite past upstream suppress fix → remove `/wd4875` → green Windows run |

### L1 — Linux Fuzz: clang-18 without libc++ fails C++23 check (Critical for fuzz green)

| | |
|--|--|
| **Symptom** | Configure dies: `std::expected` not in namespace `std` (Clang 18.1.3) |
| **Cause** | Fuzz job installs only `clang-18`, uses default **libstdc++**, which on the runner lacks C++23 `<expected>` for that clang |
| **Contrast** | Linux (clang) matrix already installs `libc++-18-dev` and passes `-stdlib=libc++` — and **passes** |
| **Fix** | Install `libc++-18-dev libc++abi-18-dev`; set `CMAKE_CXX_FLAGS`/`EXE_LINKER_FLAGS` to `-stdlib=libc++` (same as Linux clang cell) |
| **Exit** | Fuzz configure + `fuzz-all` + 30s smoke green on PR |

### L2 — Sanitizer matrix (R1; in progress)

| | |
|--|--|
| **Symptom** | First thread run failed immediately (empty suppressions path); address/undefined cancelled via fail-fast |
| **Mitigation landed** | Runtime `$GITHUB_WORKSPACE` suppressions path; `llvm-symbolizer` symlink; `fail-fast: false` |
| **Remaining** | Need green address/undefined/thread on a full run after W1/L1 noise reduced |

### Structural debt (not blocking this PR’s Win/Linux headless green)

| ID | Issue | Severity | Track |
|----|-------|----------|-------|
| S1 | Four overlapping workflows (CI, PAL, Module DAG, Sprint2) | Medium | CI-THESIS R8 |
| S2 | No branch protection / required checks | High | R2 after R1 |
| S3 | Master nightlies red for months | High | Same root causes |
| S4 | Path filters make some gates unrequirable | Medium | R6 |
| S5 | Dependency-scan was muted (R1 partially fixed) | Medium | R1 task 4/5 |
| S6 | macOS optional-only | Low | Later |

---

## Resolution plan

### Phase A — Unblock PR #46 headless Win + Linux (this change set)

1. **Windows:** apply `/wd4875` (issue #44) on `legends_compile_options`.
2. **Fuzz:** align clang fuzz job with Linux-clang libc++ toolchain.
3. Push → confirm:
   - `Windows (MSVC)` build + ctest green
   - `Fuzz Testing` smoke green
   - Linux gcc/clang/IPC stay green
4. Then re-evaluate sanitizer legs (R1 tasks 3.x / 5.2).

### Phase B — Linux depth (same week, separate commits if noisy)

| Priority | Action | Files |
|----------|--------|-------|
| B1 | Ensure sanitizer install includes `llvm-18` + symbolizer (done on R1 branch) | `ci.yml` |
| B2 | If ASan/UBSan still red: triage per `docs/ci/r1-asan-fuzz-triage.md`, issue-linked `DISABLED_` only | tests + issues |
| B3 | Fuzz corpus persistence (R10) — after smoke is green | `ci.yml`, `tests/fuzz/` |
| B4 | Optional: ccache on Linux Ninja jobs (R14) | `ci.yml` |

### Phase C — Windows depth

| Priority | Action | Files |
|----------|--------|-------|
| C1 | Land `/wd4875`; document in CONTRIBUTING / issue #44 (this PR) | `CMakeLists.txt` |
| C2 | After green build, fix any MSVC **test** failures (not build) with real fixes or issue-linked quarantine | `tests/` |
| C3 | Windows IPC cell (R7) — currently zero Windows IPC coverage | `ci.yml` |
| C4 | sccache for MSVC (R14) | `ci.yml` |
| C5 | gsl-lite pin upgrade → drop `/wd4875` | `cmake/dependencies.cmake` |

### Phase D — System-level (after A green on master)

| Order | Item | Thesis |
|------:|------|--------|
| 1 | R1 complete (enforced TSan, unmuted depscan, demotion rule) | R1 |
| 2 | R2 ruleset: require Linux gcc/clang, Linux IPC, Windows, C ABI | R2 |
| 3 | R3 preflight + R5 presets so local == CI | R3/R5 |
| 4 | R8 workflow consolidation (cut duplicate noise) | R8 |
| 5 | R7 license firewall on IPC | R7 |

---

## Acceptance criteria (Phase A)

- [ ] `Windows (MSVC)` job: configure + Release build + ctest exit 0  
- [ ] `Linux (gcc)`, `Linux (clang)`, `Linux IPC (gcc)` remain green  
- [ ] `Fuzz Testing` configure succeeds; 30s smoke per target exit 0  
- [ ] No new mutes (`allow_failure`, `|| true` on these jobs)  
- [ ] Issue #44 remains open with exit criterion until gsl-lite upgrade  

## Non-goals for Phase A

- Fixing all sanitizer races (R1 suppressions + burndown issues)  
- Making optional SDL3/macOS required  
- Branch protection ruleset (needs green first)  
- Assertion deletion to force green  
