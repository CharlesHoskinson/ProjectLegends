# Wasm Spike-or-Defer Decision Brief

Prepared: 2026-06-10  
Prepared by: GPT 5.5 Codex  
Resolution status (2026-06-10): the recommended Option B (defer roadmap §15) was applied in the working session — `ROADMAP.md` §15 and `TODO.md` now mark Wasm as deferred with restart entry criteria; `README.md`/`ARCHITECTURE.md` already state "planned". No engineering work was committed; this is a roadmap-status clarification.

## Facts Verified at HEAD

- Wasm is currently not delivered: `TODO.md:20` says "Wasm Sandbox | NOT STARTED | 0 of 50" and `TODO.md:252` says "documentation only".
- The 50 Wasm requirements are present in the roadmap: `ROADMAP.md:2556-3159` defines `REQ-WASM-001` through `REQ-WASM-050`; `ROADMAP.md:3342-3391` marks all 50 as `Missing`.
- The roadmap says the Wasm section was integrated in February: `ROADMAP.md:3855-3862` records v4.1.0 dated 2026-02-25 with `REQ-WASM-001` through `REQ-WASM-050`.
- The advertised capability has now been demoted to planned wording: `README.md:28`, `README.md:325-327`, `ARCHITECTURE.md:611-722`.
- The build option exists but is incomplete by design: `CMakeLists.txt:38` defines `LEGENDS_BUILD_WASM=OFF`; `CMakeLists.txt:451-453` states that `wasm.md`, `wit/legends-emulator.wit`, and a checked-in complete toolchain path are absent.
- Git history does not contain the referenced Wasm artifacts. `git log --all -- wasm.md "wit/legends-emulator.wit"` returns no output.

## Option A: Fund a REQ-WASM-001..010 Spike

Goal: prove the core Wasm path is real enough to keep roadmap section 15 active.

Minimum spike scope:

- `REQ-WASM-001`: Wasmtime host runner can instantiate a Project Legends component.
- `REQ-WASM-002` / `REQ-WASM-003`: choose WASI Preview 2 primary path and either implement or explicitly park Preview 1 fallback.
- `REQ-WASM-004`: pin Wasmtime, wasm-tools, and related tool versions in repo-controlled metadata.
- `REQ-WASM-005`: add one reproducible build command or preset that produces a Wasm artifact.
- `REQ-WASM-006`: document host prerequisites.
- `REQ-WASM-007..010`: create initial WIT package with lifecycle, stepping, and capture operations.
- Add one CI or local validation path proving component validation and a create/step/capture/destroy smoke test.

Rough cost:

- Spike proof: 5-8 engineering days if limited to headless lifecycle/step/capture and a single host platform.
- Production-quality first slice: 2-4 engineering weeks once CI, pinned tools, cross-platform host notes, deterministic parity, and failure-mode tests are included.

Primary risks:

- WASI Preview 2/component-model tooling churn.
- DOSBox-X/native dependencies may not be cleanly separable into a headless WASI build without more PAL work.
- CI time and dependency installation cost may be non-trivial.

Blast radius if this option is chosen:

- Add `wasm.md`.
- Add `wit/legends-emulator.wit`.
- Add Wasm toolchain metadata such as `cmake/wasm-toolchain.cmake`, `CMakePresets.json` entries, or an equivalent script/manifest.
- Update `CMakeLists.txt` to make `LEGENDS_BUILD_WASM` complete rather than scaffold-only.
- Add Wasm host runner code and tests, likely under new docs/tests/tooling paths.
- Update `.github/workflows/ci.yml` or a dedicated workflow for Wasm validation.
- Update `README.md`, `ARCHITECTURE.md`, `ROADMAP.md`, and `TODO.md` from planned/not-started to spike status only after the spike exists.

## Option B: Formally Defer Roadmap Section 15

Goal: keep the record honest by treating Wasm as a future roadmap area, not an active delivery promise.

Minimum defer scope:

- Keep README and architecture wording planned, not delivered.
- Mark roadmap section 15 as deferred with owner-approved rationale.
- Leave `LEGENDS_BUILD_WASM` off by default and either keep the scaffold with explicit warnings or remove the incomplete WIT generation target until artifacts exist.
- Track a future decision point with entry criteria for restarting Wasm.

Rough cost:

- 0.5-1 engineering day for documentation cleanup and one CI/docs check that prevents re-advertising Wasm as delivered.
- No production engineering cost until the owner funds a new Wasm spike.

Blast radius if this option is chosen:

- `ROADMAP.md`
- `TODO.md`
- `README.md`
- `ARCHITECTURE.md`
- `CMakeLists.txt` only if the owner wants to remove or hard-disable the incomplete scaffold rather than retain it as planned/off-by-default.

## Recommendation

Recommended owner decision: formally defer roadmap section 15 unless the owner is ready to fund a focused `REQ-WASM-001..010` spike immediately.

Rationale: the repository has carried Wasm as 0/50 since the February roadmap entry, no referenced `wasm.md` or WIT artifact ever existed in git history, and the current native/proxy/security work has nearer-term audit and correctness pressure. Deferring is the lower-risk truthful-record action; funding a spike is viable only if it is explicitly staffed and measured by real artifact creation.

This brief does not apply either option.
