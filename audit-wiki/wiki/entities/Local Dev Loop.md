---
type: entity
entity_kind: system
aliases: ["developer workflow", "build.cmd", "local build loop"]
tags: [entity, type/entity, topic/audit, topic/ci, topic/dev-loop]
created: 2026-06-10
updated: 2026-06-10
status: draft
related:
  - "[[CI Gate Coverage Map]]"
  - "[[Build & CI System (Project Legends)]]"
  - "[[CI Workflows (GitHub Actions)]]"
  - "[[Quality Gate Scripts & Hooks]]"
---

# Local Dev Loop

What a developer's local edit-build-test loop actually exercises, versus what the mandatory CI tier enforces after push. Gate scripts themselves are inventoried in [[Quality Gate Scripts & Hooks]]; per-path-family CI coverage is in [[CI Gate Coverage Map]]; the workflows are described in [[CI Workflows (GitHub Actions)]] and [[Build & CI System (Project Legends)]].

## build.cmd

The repository ships **no** build script at its root — the root directory contains only `CMakeLists.txt` and `CMakePresets.json` as build entry points (root directory listing; no `*.cmd`/`*.bat`/`*.sh` at top level). The only `build.cmd` in the tree is `llm-wiki/_scratch/build.cmd`, an audit-local convenience script (its own comment: "AUDIT-LOCAL (2026-06-05): LEGENDS_WERROR=OFF so audit build compiles through F-009 discards", `llm-wiki/_scratch/build.cmd:5`). Step by step:

1. Sources the MSVC environment via `vcvars64.bat` (VS 2022 BuildTools) (`llm-wiki/_scratch/build.cmd:2`).
2. Probes for `ninja` on PATH (`llm-wiki/_scratch/build.cmd:3`).
3. **Ninja path:** configures with `cmake --preset dev -DLEGENDS_WERROR=OFF` (the `dev` preset is Debug + `LEGENDS_BUILD_TESTS=ON`, Ninja generator, `build/dev` binary dir — `CMakePresets.json:28-35` region, preset list), then `cmake --build C:\ProjectLegends\build\dev --parallel` (`llm-wiki/_scratch/build.cmd:6-9`).
4. **Fallback path (no ninja):** configures `build/dev-vs` with the "Visual Studio 17 2022" x64 generator, `LEGENDS_BUILD_TESTS=ON`, `LEGENDS_WERROR=OFF`, and builds the Debug config (`llm-wiki/_scratch/build.cmd:11-14`).
5. Logs configure/build output to `llm-wiki/_scratch/configure.log` and `build.log`; echoes `BUILD_OK`/`CONFIGURE_FAILED`/`BUILD_FAILED` (`llm-wiki/_scratch/build.cmd:6-16`).

It compiles only: it never runs `ctest`, any `scripts/check_*.py` gate, sanitizers, or fuzzers (`llm-wiki/_scratch/build.cmd:1-17` — no such invocations). It also disables `LEGENDS_WERROR`, which CI builds do not do (no `LEGENDS_WERROR` flag in any workflow configure step, `.github/workflows/ci.yml:63-71`).

The repo's `CMakePresets.json` does define presets for the specialized configurations — configure presets `default-ninja`, `dev`, `dev-mingw`, `release`, `asan`, `tsan`, `ipc`, `coverage`, `fuzz` plus matching build/test presets (`CMakePresets.json`, `configurePresets`/`buildPresets`/`testPresets` arrays) — but CI does not use presets; every workflow passes raw `-D` flags (`.github/workflows/ci.yml:64-71`, `.github/workflows/sprint2-checks.yml:99-105`, `.github/workflows/module-dag.yml:104-109`, `.github/workflows/pal-ci.yml:39-45`).

## Gate table: local default vs hooks vs CI mandatory tier

Column definitions. **Local by default** = exercised by the documented build-and-test loop (`cmake -B build -G Ninja -DLEGENDS_BUILD_TESTS=ON; cmake --build build; ctest --test-dir build --output-on-failure`, `README.md:146-150`; same loop in `CONTRIBUTING.md:43-49`) with no extra setup. **With hooks** = additionally after `git config core.hooksPath .githooks` (`.githooks/pre-commit:3`). **CI mandatory tier** = workflow jobs that run on PR + push with no `schedule`/`workflow_dispatch`/tag-only `if:` condition (derivation in [[CI Gate Coverage Map]]); path-filter caveats noted per row.

| Gate | Runs locally by default? | Runs locally if hooks installed? | Runs in CI mandatory tier? |
|---|---|---|---|
| Compile | Yes — single default configure (Ninja, tests ON, no preset; `README.md:147-148`). `build.cmd` variant uses the `dev` preset or a VS fallback (`llm-wiki/_scratch/build.cmd:6, 11`) | Same (hook adds nothing; `.githooks/pre-commit:7`) | Yes — `ci.yml`: `linux` gcc-13 + clang-18/libc++ Release (`ci.yml:36-74`), `linux-ipc` gcc Debug + `LEGENDS_USE_IPC=ON` (`ci.yml:95-119`), `windows` MSVC Release (`ci.yml:189-204`), `coverage` gcc Debug (`ci.yml:707-735`); path-filtered: `sprint2-checks` `multi-instance-tests` Release + `LEGENDS_LIBRARY_MODE=ON` (`sprint2-checks.yml:98-108`), `module-dag` `cmake-dag` configure-only DAG check (`module-dag.yml:103-118`) |
| Unit tests | Yes — `ctest` in the documented loop (`README.md:149`) | Same | Yes — `ctest` in `linux`, `linux-ipc`, `windows`, `coverage` (`ci.yml:76-77, 126-127, 206-207, 737-738`); full `legends_unit_tests` run in sprint2 `multi-instance-tests` (`sprint2-checks.yml:110-114`) |
| Integration tests | Yes — the documented `ctest` line has no label filter, so integration tests run with the rest (`README.md:149`; label split documented at `CONTRIBUTING.md:99-102`) | Same | Yes — CI `ctest` invocations also carry no label filter (`ci.yml:77`) |
| Include rules (`check_includes.py`) | No — not part of any documented build/test command (`README.md:146-150`; `CONTRIBUTING.md` has no `scripts/` mention) | **Yes** — the hook's only check (`.githooks/pre-commit:7`) | Yes — `module-dag` `include-rules` (`module-dag.yml:64-66`); path-filtered (`module-dag.yml:18-45`) |
| Globals registry suite (`check_current_context`, `check_migration_status`, `check_globals`, `check_gsl_lite_usage`) | No | No | Yes — `sprint2-checks` `globals-registry` (`sprint2-checks.yml:44-54`); path-filtered (`sprint2-checks.yml:3-27`) |
| Conflict markers (`check_conflict_markers.py`) | No | No | Yes — `sprint2-checks.yml:56-57`; path-filtered |
| Case collisions (`check_case_collisions.py`) | No | No | Yes — `sprint2-checks.yml:59-60`; path-filtered |
| OpenSpec staleness (`check_openspec_staleness.py`) | No | No | Yes — `sprint2-checks.yml:62-63`; path-filtered, and `openspec/**` is not among the trigger paths (`sprint2-checks.yml:3-27`) |
| Capability matrix (`check_capability_matrix.py`) | No | No | Yes — `sprint2-checks.yml:65-66`; path-filtered |
| Graphify enrichment (enrich + strict check) | No | No | Yes — `sprint2-checks.yml:68-85`; path-filtered |
| Sanitizers (ASan/UBSan/TSan/MSan) | No — opt-in only: documented ASan/UBSan configure (`CONTRIBUTING.md:84-90`) and `asan`/`tsan` presets (`CMakePresets.json`) exist but are not in the default loop | No | Partial — runs on every PR and on pushes **to master only** (`ci.yml:333-337`); ASan/UBSan block, TSan/MSan are `allow_failure: true` (`ci.yml:332, 357-373`) |
| Fuzz (libFuzzer, 5 targets, 30s smoke) | No — `fuzz` preset exists (`CMakePresets.json`) but is in no documented loop | No | Partial — every PR and pushes to master only (`ci.yml:482-487, 515-537`) |
| Coverage | No — `coverage` preset exists; lcov listed as optional prerequisite (`CONTRIBUTING.md:32`) | No | Runs on PR + push but is report-only: "no minimum threshold is enforced by CI yet" (`ci.yml:707-764, 749`); the 80% threshold exists only in tag-gated `release-validation` (`ci.yml:877-921`) |
| clang-tidy (static analysis) | No — clang-tidy-18 listed as optional prerequisite (`CONTRIBUTING.md:33`), no documented invocation | No | **No** — `static-analysis` job is `schedule`/`workflow_dispatch` only (`ci.yml:435-439`) |

Also in the mandatory tier with no local-default counterpart: the `abi-check` job, which C11-syntax-compiles `include/legends/legends_embed.h` with `-Werror` and checks header guards (`ci.yml:406-430`, unconditional).

## Replicating the mandatory CI tier locally

No single command — documented or scripted — reproduces the mandatory tier. The documented developer instructions cover only configure + build + `ctest` (`README.md:146-150, 347-357`; `CONTRIBUTING.md:43-49, 93-105`) plus an opt-in sanitizer configure (`CONTRIBUTING.md:84-90`). Neither `README.md` nor `CONTRIBUTING.md` mentions any `scripts/check_*.py` gate, the pre-commit hook, or the sprint2/module-dag workflows (grep for `check_` and `scripts/` over both files: no matches). There is no Makefile, task runner, or aggregate gate script at the repo root (root directory listing), and `llm-wiki/_scratch/build.cmd` compiles only (`llm-wiki/_scratch/build.cmd:1-17`).

Replicating the tier today takes, at minimum, manually running:

1. Build + `ctest` in the CI configurations: Release gcc and clang/libc++ (`ci.yml:63-77`), Debug + `LEGENDS_USE_IPC=ON` (`ci.yml:108-127`), MSVC Release (`ci.yml:197-207`), Release + `LEGENDS_LIBRARY_MODE=ON` with the `MultiInstance*` filter and full suite (`sprint2-checks.yml:98-114`).
2. `python scripts/check_includes.py --path . --verbose` (`module-dag.yml:64-66`) — the only step the opt-in hook automates (`.githooks/pre-commit:7`).
3. The nine `globals-registry` script steps: `check_current_context`, `check_migration_status`, `check_globals`, `check_gsl_lite_usage`, `check_conflict_markers`, `check_case_collisions`, `check_openspec_staleness`, `check_capability_matrix`, and the graphify enrich + strict check pair (`sprint2-checks.yml:44-85`), with `pyyaml` installed (`sprint2-checks.yml:41-42`).
4. For PR parity: ASan and UBSan builds + `ctest` (`ci.yml:343-350, 383-401`), the five 30-second fuzz smoke targets (`ci.yml:515-537`), and the C11 ABI syntax check (`ci.yml:414-419`).
5. A configure with `PAL_BACKEND_HEADLESS=ON` for the DAG check (`module-dag.yml:103-109`) and, when `src/pal/**`/`include/**` paths are touched, the pal-ci backend builds and firewall greps (`pal-ci.yml:27-265`).

Of the fourteen gate rows above, the documented default loop covers three (compile, unit tests, integration tests — in one configuration, not the CI matrix); installing the hook adds exactly one more (include rules). Every other mandatory-tier gate runs for the first time after push.

## Related

- [[Quality Gate Scripts & Hooks]] — what each script gate checks and where it is wired
- [[CI Gate Coverage Map]] — tier derivation and per-path coverage
- [[CI Workflows (GitHub Actions)]] — the four workflow files
- [[Build & CI System (Project Legends)]] — parent subsystem assessment
