# CI/CD Quality-Gate Audit — Design

Date: 2026-06-10
Status: approved
Baseline: master `fe61d45`

## Goal

Produce a well-scoped thesis on improving the ProjectLegends CI/CD system along four
axes: modularity, maintainability, intelligent test coverage, and always-green commits
(defense in depth: local preflight mirroring CI plus server-side enforcement). The
thesis must rest on a navigable, cited evidence base, and its major recommendations
must arrive as openspec change proposals ready for implementation sprints.

## Scope

The full quality-gate stack:

- GitHub workflows: `ci.yml`, `pal-ci.yml`, `module-dag.yml`, `sprint2-checks.yml`
- Build system: `CMakeLists.txt`, `CMakePresets.json`, `cmake/ModuleManifest.cmake`,
  `cmake/ModuleDAG.cmake`, `cmake/dependencies.cmake`, `build.cmd`
- Test infrastructure: `tests/{unit,integration,fuzz}`, `engine/tests`, CTest
  registration, sanitizer/coverage/determinism lanes
- Quality gates: `scripts/check_*.py`, `.githooks/pre-commit`, openspec validation,
  graphify enrichment validation
- Local dev loop: what a developer runs before commit, and what nothing currently
  forces them to run

Out of scope: implementing recommendations, fixing currently-red or allow-failure
lanes, engine code changes. Every "should" becomes an openspec proposal, not an edit.

## Deliverables

1. **Evidence wiki** — pages added to the committed `audit-wiki/`, following its
   existing schema and `audit-wiki/CLAUDE.md` conventions:
   - `wiki/entities/` — one page per CI subsystem
   - `wiki/sources/` — one page per researched best-practice topic
   - `wiki/syntheses/` — one gap-analysis page per audit axis
2. **Thesis** — `CI-THESIS.md` at repo root (the `AUDIT.md`/`CIFix.md` convention),
   synthesizing the wiki with links into it, recommendations ranked.
3. **Openspec proposals** — one change proposal per major recommendation, drafted via
   the repo's `openspec-propose` skill, passing `openspec validate --strict`.

## Pipeline

### P1 — Graph (gate-coverage map)

Run `graphify` (AST mode, local, no API key) over `src/`, `engine/`, `tests/`,
`cmake/`, `.github/`, `scripts/`. Join three graph layers:

- graphify's knowledge graph (`graphify-out/GRAPH_REPORT.md`)
- the repo's CI-validated enrichment JSON
  (`graphify-out/projectlegends-enrichment.json`)
- the ModuleDAG (`cmake/ModuleManifest.cmake` + `cmake/ModuleDAG.cmake`)

Output: a gate-coverage map recording, for each module and path family, which
workflows/jobs/hooks/scripts guard it and under what trigger conditions — and which
paths no mandatory gate guards. This map is itself a wiki entity page.

### P2 — Inventory (current state, cited)

Subagents write one `wiki/entities/` page per subsystem:

- each of the four workflows (jobs, triggers, tiering, caching, artifacts)
- CMake presets and build options
- test infrastructure (suites, registration, fixtures, labels)
- sanitizer, fuzz, coverage, and determinism lanes (including allow-failure status
  and the report-only coverage policy)
- Python check scripts, pre-commit hook, openspec and graphify gates
- local dev loop as it exists today

Plus one empirical page built from `gh api` run history (all retained runs, capped at
the API's history window): per-job durations, failure rates, which gates fire in
practice, flake signatures (recent SDL test relaxation commits indicate live
flakiness). Every claim cites a file path or a concrete CI run.

### P3 — Research (best practices, scraped and cited)

Parallel agents, one topic each, matched to this architecture (C++23, CMake, vendored
GPL engine, IPC license split, three-OS matrix, ~5,600 unit tests):

1. C++/CMake monorepo CI design
2. Merge queues and required status checks
3. Compiler caching (ccache/sccache) on GitHub Actions
4. Test impact analysis and test selection at scale
5. Coverage policy ratcheting (report-only to enforced)
6. Sanitizer lane strategy (which, when, allow-failure discipline)
7. Continuous fuzzing in CI (ClusterFuzzLite / OSS-Fuzz patterns)
8. Flaky-test detection and quarantine
9. Vendored-dependency and license-isolation build practices
10. Local preflight design (mirroring CI cheaply on developer machines)

Agents discover sources via web search; scrapling performs all fetching. Each topic
becomes a `wiki/sources/` page with URL + retrieval date per citation.

### P4 — Gap analysis

Four `wiki/syntheses/` pages — modularity, maintainability, intelligent coverage,
always-green — each confronting P2 evidence with P3 practice. A finding states: what
the repo does (cited to P2), what practice supports (cited to P3), the gap, and a
candidate recommendation.

### P5 — Thesis and proposals

Adversarial pass first: every candidate recommendation is checked against repo
reality — not already implemented, compatible with the Windows+Linux dev loop,
respects GPL isolation, cost stated. Survivors enter `CI-THESIS.md`, ranked. A
recommendation is major when it changes what a contributor must do to land a commit
or alters a CI lane's existence, trigger tier, or enforcement status; each major
recommendation becomes an openspec change proposal.

## Quality rules

- Every wiki claim cites a file path, CI run id, or URL with retrieval date. No
  uncited assertion reaches the thesis.
- No time estimates; no quantifying work by counts of items produced; no
  review-process meta in deliverables.
- Wiki pages follow `audit-wiki/CLAUDE.md`; the wiki log records each ingest.

## Dependencies (verified 2026-06-10)

- Python 3.14.2, pip 25.3
- scrapling 0.4.7 with fetchers (import verified)
- graphify 0.8.36 (installed via uv from github.com/safishamsi/graphify, user-authorized)
- mkdocs 1.6.1 (uv tool)
- cmake, gh, uv, git on PATH; ninja/MSVC via `build.cmd` (vcvars64)
- clang not local — Linux CI lanes only; not required for the audit
