# CI/CD Quality-Gate Audit Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a cited evidence base in `audit-wiki/`, then a thesis (`CI-THESIS.md`) and openspec change proposals for improving the CI/CD quality-gate stack along four axes: modularity, maintainability, intelligent test coverage, always-green commits.

**Architecture:** Five-phase evidence-first pipeline per `docs/superpowers/specs/2026-06-10-cicd-audit-design.md`: graph the gate coverage (graphify + repo enrichment + ModuleDAG), inventory the current state into wiki entity pages, research best practices via web-search agents + scrapling fetches into wiki source pages, write four gap-analysis syntheses, then adversarially filter recommendations into the thesis and openspec proposals.

**Tech Stack:** graphify 0.8.36 (CLI), scrapling 0.4.7 (Python), `gh api`, llm-wiki conventions (`audit-wiki/CLAUDE.md`), openspec.

**Baseline:** master `47cdbac`. All paths relative to `C:\ProjectLegends`.

**Standing rules (apply to every task):**
- Every wiki claim cites a repo path (optionally `:line`) at the current commit, a CI run id/URL, or a URL + retrieval date. Uncited claims are defects.
- Wiki pages use `[[wikilinks]]`, land in their category `_index.md`, and each ingest appends one line to `audit-wiki/log.md` and is one atomic git commit staging only wiki paths.
- Existing pages (`Build & CI System (Project Legends)`, `Project Legends Test Suite`, concept `Quality Gate Demotion (2026-06-08)`) are updated, never duplicated. Contradictions append + flag with `> [!conflict]`, never overwrite.
- Terse human prose. No time estimates, no work-volume counts, no review-process meta in any deliverable.
- Subagents write files and report back; they never run git. The orchestrator commits.

---

### Task 1: Build the graphify graph

**Files:**
- Create (generated, not committed): `graphify-out/graph.json`, `graphify-out/GRAPH_REPORT.md`

- [ ] **Step 1: Record which graphify-out files git currently tracks**

Run: `git -C C:\ProjectLegends ls-files graphify-out`
Expected: `graphify-out/projectlegends-enrichment.json` (possibly others). Whatever is listed is the *only* graphify-out content that may ever be committed by later tasks — and this plan never modifies it.

- [ ] **Step 2: Run the AST extraction**

Run (repo root): `graphify update . --no-cluster`
Expected: exit 0; `graphify-out/graph.json` created/updated. This is local tree-sitter extraction, no LLM, no API key. If runtime exceeds ~15 minutes on the vendored engine, rerun scoped: `graphify update src` then `graphify update engine/src` (the graph accumulates).

- [ ] **Step 3: Cluster and generate the report without LLM naming**

Run: `graphify cluster-only . --no-label --no-viz`
Expected: exit 0; `graphify-out/GRAPH_REPORT.md` exists and names communities as `Community N`.

- [ ] **Step 4: Verify nothing tracked changed**

Run: `git -C C:\ProjectLegends status --short graphify-out`
Expected: only untracked (`??`) new files. If `projectlegends-enrichment.json` shows modified, run `git -C C:\ProjectLegends checkout -- graphify-out/projectlegends-enrichment.json` and note in the task report that graphify touched it.

No commit in this task (generated artifacts stay untracked).

---

### Task 2: Gate-coverage map page

**Files:**
- Create: `audit-wiki/wiki/maps/CI Gate Coverage Map.md`
- Create: `audit-wiki/wiki/maps/_index.md`
- Modify: `audit-wiki/index.md` (maps line), `audit-wiki/log.md`

- [ ] **Step 1: Dispatch a subagent to derive the map**

Subagent prompt (verbatim, fill nothing):

> Read, in this order: `C:\ProjectLegends\graphify-out\GRAPH_REPORT.md`, `C:\ProjectLegends\cmake\ModuleManifest.cmake`, `C:\ProjectLegends\cmake\ModuleDAG.cmake`, the `paths:` triggers and job `if:` conditions in all four files under `C:\ProjectLegends\.github\workflows\`, `C:\ProjectLegends\.githooks\pre-commit`, and the job steps that invoke `scripts/check_*.py`.
> Write `C:\ProjectLegends\audit-wiki\wiki\maps\CI Gate Coverage Map.md`: for each module in ModuleManifest (legends_core, legends_pal, aibox_core, legends_ipc, legends_proxy, legends_engine_host) plus the path families `.github/workflows/**`, `scripts/**`, `cmake/**`, `docs/**`, `openspec/**`, `audit-wiki/**`, a table row: module/path → which workflow jobs build or test it, on which trigger tier (PR+push / nightly / tag / manual), which hook or check script guards it locally, and `NONE` where no mandatory gate fires. Close with a "Structurally unguarded" section listing every NONE row and every gate that exists only on the nightly/manual tier. Every row cites the workflow file and line range or script path that proves it. Use `[[wikilinks]]` to `Build & CI System (Project Legends)` and `Project Legends Test Suite`. Start the file with a one-line purpose sentence. Do not run git.

- [ ] **Step 2: Verify the map**

Check: file exists; every row has a citation; the "Structurally unguarded" section is present and consistent with the table (spot-check 3 rows against the workflow files yourself).

- [ ] **Step 3: Wire into the wiki**

Create `audit-wiki/wiki/maps/_index.md`:

```markdown
# Maps

Topic MOCs.

- [[CI Gate Coverage Map]] — which gates guard which modules/paths, and what nothing guards.
```

In `audit-wiki/index.md` replace `- Maps: see `wiki/maps/`` with `- [[wiki/maps/_index|Maps]] — topic MOCs (1 entry)`. Append to `audit-wiki/log.md`: `- 2026-06-10 — ingest: CI Gate Coverage Map (graphify + ModuleDAG + workflow triggers).`

- [ ] **Step 4: Commit**

```powershell
git -C C:\ProjectLegends add audit-wiki/wiki/maps "audit-wiki/index.md" "audit-wiki/log.md"
git -C C:\ProjectLegends commit -m "wiki: add CI gate coverage map"
```

---

### Task 3: Empirical CI run-history page

**Files:**
- Create: `audit-wiki/raw/ci-run-history-2026-06.json`
- Create: `audit-wiki/wiki/sources/CI Run History (2026-06).md`
- Modify: `audit-wiki/wiki/sources/_index.md`, `audit-wiki/index.md` (sources count), `audit-wiki/log.md`

- [ ] **Step 1: Pull run history**

```powershell
gh api --paginate "repos/CharlesHoskinson/ProjectLegends/actions/runs?per_page=100" --jq '.workflow_runs[] | {id, name, event, status, conclusion, run_started_at, updated_at, head_branch, run_attempt}' > $env:TEMP\runs.jsonl
```

Expected: one JSON object per line; if empty, the repo retains no runs — record that fact on the wiki page and skip Step 2.

- [ ] **Step 2: Pull per-job timings for the most recent 30 runs**

```powershell
Get-Content $env:TEMP\runs.jsonl | Select-Object -First 30 | ForEach-Object { $r = $_ | ConvertFrom-Json; gh api "repos/CharlesHoskinson/ProjectLegends/actions/runs/$($r.id)/jobs?per_page=100" --jq '.jobs[] | {run_id: .run_id, name, conclusion, started_at, completed_at}' } > $env:TEMP\jobs.jsonl
```

Expected: job lines with timestamps.

- [ ] **Step 3: Aggregate**

Write `$env:TEMP\ci_stats.py`:

```python
import json, sys, collections, datetime, pathlib
def load(p): return [json.loads(l) for l in pathlib.Path(p).read_text().splitlines() if l.strip()]
runs, jobs = load(sys.argv[1]), load(sys.argv[2])
by_wf = collections.Counter((r["name"], r["conclusion"]) for r in runs)
reruns = [r for r in runs if r.get("run_attempt", 1) > 1]
dur = collections.defaultdict(list)
for j in jobs:
    if j["started_at"] and j["completed_at"]:
        s = datetime.datetime.fromisoformat(j["started_at"].replace("Z", "+00:00"))
        e = datetime.datetime.fromisoformat(j["completed_at"].replace("Z", "+00:00"))
        dur[j["name"]].append(((e - s).total_seconds(), j["conclusion"]))
out = {
    "window": {"runs": len(runs), "oldest": min(r["run_started_at"] for r in runs), "newest": max(r["run_started_at"] for r in runs)},
    "conclusions_by_workflow": {f"{k[0]}::{k[1]}": v for k, v in sorted(by_wf.items())},
    "rerun_runs": [{"id": r["id"], "name": r["name"], "attempt": r["run_attempt"]} for r in reruns],
    "job_seconds": {k: {"n": len(v), "median": sorted(x[0] for x in v)[len(v)//2], "max": max(x[0] for x in v), "fail": sum(1 for x in v if x[1] not in ("success", "skipped"))} for k, v in sorted(dur.items())},
}
print(json.dumps(out, indent=2))
```

Run: `python $env:TEMP\ci_stats.py $env:TEMP\runs.jsonl $env:TEMP\jobs.jsonl > C:\ProjectLegends\audit-wiki\raw\ci-run-history-2026-06.json`
Expected: valid JSON with the four top-level keys.

- [ ] **Step 4: Write the source page**

Create `audit-wiki/wiki/sources/CI Run History (2026-06).md` summarizing, from the raw JSON only: pass/fail mix per workflow, jobs with `run_attempt > 1` (re-run = flake or infra signal), slowest and most failure-prone jobs, and how often nightly-only lanes actually ran. Every figure cites `raw/ci-run-history-2026-06.json` plus at least one concrete run id formatted as a GitHub URL. Add the page to `wiki/sources/_index.md`, bump the sources count in `index.md`, append a log line.

- [ ] **Step 5: Commit**

```powershell
git -C C:\ProjectLegends add audit-wiki/raw/ci-run-history-2026-06.json "audit-wiki/wiki/sources" "audit-wiki/index.md" "audit-wiki/log.md"
git -C C:\ProjectLegends commit -m "wiki: ingest CI run history"
```

---

### Task 4: Subsystem inventory pages

**Files:**
- Modify: `audit-wiki/wiki/entities/Build & CI System (Project Legends).md`
- Modify: `audit-wiki/wiki/entities/Project Legends Test Suite.md`
- Create: `audit-wiki/wiki/entities/CI Workflows (GitHub Actions).md`
- Create: `audit-wiki/wiki/entities/Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism).md`
- Create: `audit-wiki/wiki/entities/Quality Gate Scripts & Hooks.md`
- Create: `audit-wiki/wiki/entities/Local Dev Loop.md`
- Modify: `audit-wiki/wiki/entities/_index.md`, `audit-wiki/index.md`, `audit-wiki/log.md`

- [ ] **Step 1: Dispatch four subagents in parallel** (they touch disjoint files)

Common preamble for all four prompts:

> You are writing inventory pages for the Project Legends audit wiki at `C:\ProjectLegends\audit-wiki\`. Read `audit-wiki/CLAUDE.md` first and follow its conventions. Pages are factual current-state inventory — no recommendations, no opinions. Every claim cites a repo file path (with `:line` where line-specific) as it stands on master. Use `[[wikilinks]]` between related pages. Do not run git. Do not edit `_index.md`, `index.md`, or `log.md`.

Subagent A — `CI Workflows (GitHub Actions).md` (new): one section per workflow (`ci.yml`, `pal-ci.yml`, `module-dag.yml`, `sprint2-checks.yml`): triggers, path filters, job list with runner/timeout/trigger tier, caching, artifacts, allow-failure jobs, inter-workflow overlap (which jobs build the same targets twice). Source: the four files under `.github/workflows/`.

Subagent B — update `Build & CI System (Project Legends).md`: append a dated section "Build system inventory (2026-06-10)" covering CMake presets (all 11, with compiler/flags/test enablement from `CMakePresets.json`), build options in `CMakeLists.txt`, two-tier warning policy, FetchContent dependencies from `cmake/dependencies.cmake`, ModuleManifest/ModuleDAG enforcement, the IPC license split build targets, and `build.cmd`. Flag with `> [!conflict]` anything that contradicts existing page content rather than rewriting it.

Subagent C — update `Project Legends Test Suite.md` with a dated section "Test infrastructure inventory (2026-06-10)": suites and registration (`gtest_discover_tests` sites in `CMakeLists.txt`, `engine/tests`), directory layout under `tests/`, labels (e.g. `soak`), fixture status (planned `test_utils/` per `docs/superpowers/plans/2026-03-20-plan-2-test-infrastructure.md`), and which presets run which suites. New page `Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism).md`: each lane's config (preset + workflow job), enforcement status (enforced / allow-failure / report-only — coverage has no threshold per `ci.yml`), fuzz targets and CI fuzz durations, determinism test scope and the H7 gap noted in `AUDIT.md`.

Subagent D — new pages `Quality Gate Scripts & Hooks.md`: every `scripts/check_*.py` (what it checks, where CI invokes it, whether the pre-commit hook in `.githooks/pre-commit` runs it), openspec validation gate, graphify enrichment gate in `sprint2-checks.yml`; and `Local Dev Loop.md`: what `build.cmd` does, what the pre-commit hook covers vs what CI requires (the delta is the page's core table: gate → runs locally? → runs in CI?), and the fact that hook installation requires `git config core.hooksPath .githooks` (cite where, if anywhere, that is documented).

- [ ] **Step 2: Verify**

For each page: spot-check 3 citations against the cited files; confirm no recommendations crept in; confirm dated-section updates appended rather than rewrote.

- [ ] **Step 3: Wire and commit (orchestrator)**

Add the four new pages to `wiki/entities/_index.md`, bump entity count in `index.md`, append one log line per page. Then:

```powershell
git -C C:\ProjectLegends add "audit-wiki/wiki/entities" "audit-wiki/index.md" "audit-wiki/log.md"
git -C C:\ProjectLegends commit -m "wiki: inventory CI subsystems"
```

---

### Task 5: Best-practice research fan-out

**Files (per topic i of 10):**
- Create: `audit-wiki/raw/research/<slug>.md`
- Create: `audit-wiki/wiki/sources/<Title> (2026-06).md`
- Modify: `audit-wiki/wiki/sources/_index.md`, `audit-wiki/index.md`, `audit-wiki/log.md`

Topics and slugs:

| # | Title | slug |
|---|---|---|
| 1 | CI Design for C++/CMake Monorepos | cpp-cmake-monorepo-ci |
| 2 | Merge Queues & Required Checks | merge-queues-required-checks |
| 3 | Compiler Caching on GitHub Actions | compiler-caching-actions |
| 4 | Test Impact Analysis & Selection | test-impact-analysis |
| 5 | Coverage Policy Ratcheting | coverage-ratcheting |
| 6 | Sanitizer Lane Strategy | sanitizer-lane-strategy |
| 7 | Continuous Fuzzing in CI | continuous-fuzzing-ci |
| 8 | Flaky-Test Detection & Quarantine | flaky-test-quarantine |
| 9 | Vendored & License-Isolated Dependency CI | vendored-license-isolation-ci |
| 10 | Local Preflight Design | local-preflight-design |

- [ ] **Step 1: Dispatch research subagents in parallel batches of 5**

Per-topic prompt template (replace `<TITLE>`, `<SLUG>`, `<FOCUS>` only):

> Research current best practice for **<TITLE>** as it applies to this project: C++23, CMake presets, vendored GPL DOSBox-X engine with an MIT IPC proxy split, three-OS GitHub Actions matrix, GoogleTest suites at thousands-of-tests scale, libFuzzer targets, lcov coverage currently report-only. Focus: <FOCUS>.
> Method: use web search to find 3–6 authoritative sources (engineering blogs of major C++ shops, official GitHub/CMake/LLVM docs, conference talks, peer-reviewed work — not SEO listicles). Fetch each with scrapling, not WebFetch:
> ```python
> from scrapling.fetchers import Fetcher
> page = Fetcher.get("<url>")          # add stealthy_headers=True if blocked
> print(page.get_all_text())
> ```
> Run via a temp file: `python $env:TEMP\fetch_<SLUG>.py`. If a site blocks Fetcher, try `from scrapling.fetchers import StealthyFetcher; page = StealthyFetcher.fetch("<url>")`; if still blocked, drop the source and say so.
> Write two files, then stop (no git):
> 1. `C:\ProjectLegends\audit-wiki\raw\research\<SLUG>.md` — per source: URL, retrieval date 2026-06-10, and the relevant extracted passages (quoted or tightly paraphrased). This is the immutable raw record.
> 2. `C:\ProjectLegends\audit-wiki\wiki\sources\<TITLE> (2026-06).md` — synthesis: the practices that apply here, each marked `^[from <URL> (retrieved 2026-06-10)]`, with a short "applicability to Project Legends" note per practice citing the repo path it would touch. Note explicit disagreement between sources with `> [!conflict]`.

FOCUS lines:
1. job/workflow factoring, reusable workflows, matrix design, path-filter correctness, tiering mandatory vs nightly
2. GitHub merge queue mechanics, required-check selection, branch protection vs rulesets, batching trade-offs
3. ccache/sccache on Actions for MSVC+gcc+clang, cache key design, FetchContent interplay, expected hit rates
4. selecting tests by changed paths in CMake/CTest projects, label-based tiering, risk-based selection, known failure modes of TIA
5. moving lcov from report-only to enforced without freezing development: ratchets, per-target thresholds, diff coverage
6. which sanitizers gate PRs vs nightly at major C++ shops, allow-failure discipline, TSan-on-legacy-globals strategies
7. ClusterFuzzLite vs OSS-Fuzz vs in-repo libFuzzer jobs, corpus management in CI, crash triage flow
8. detection (rerun signatures, attempt counts), quarantine workflows, ownership and exit criteria for quarantined tests
9. building/testing vendored GPL code separately from MIT code, license firewalls in CI, SBOM/dependency scanning placement
10. designing a `preflight` target that mirrors CI's mandatory tier in minutes on a developer machine; hook vs script vs both; Windows specifics

- [ ] **Step 2: Verify each topic** (orchestrator, as agents return)

Raw file has ≥3 sources with URLs + dates; source page practices all carry `^[from …]` markers; applicability notes cite real repo paths (spot-check against the repo).

- [ ] **Step 3: Wire and commit per topic**

After verifying each topic: add page to `wiki/sources/_index.md`, bump count in `index.md`, append log line, then:

```powershell
git -C C:\ProjectLegends add "audit-wiki/raw/research/<SLUG>.md" "audit-wiki/wiki/sources" "audit-wiki/index.md" "audit-wiki/log.md"
git -C C:\ProjectLegends commit -m "wiki: ingest <SLUG> research"
```

---

### Task 6: Gap-analysis syntheses

**Files:**
- Create: `audit-wiki/wiki/syntheses/Gap Analysis — Modularity (2026-06).md`
- Create: `audit-wiki/wiki/syntheses/Gap Analysis — Maintainability (2026-06).md`
- Create: `audit-wiki/wiki/syntheses/Gap Analysis — Test Coverage Intelligence (2026-06).md`
- Create: `audit-wiki/wiki/syntheses/Gap Analysis — Always Green (2026-06).md`
- Modify: `audit-wiki/wiki/syntheses/_index.md`, `audit-wiki/index.md`, `audit-wiki/log.md`

- [ ] **Step 1: Dispatch four subagents in parallel**, one per axis. Common prompt skeleton (replace `<AXIS>`, `<AXIS-SCOPE>`, `<FILENAME>`):

> Read `C:\ProjectLegends\audit-wiki\CLAUDE.md`, then the entity pages under `audit-wiki/wiki/entities/`, the map `audit-wiki/wiki/maps/CI Gate Coverage Map.md`, and the source pages under `audit-wiki/wiki/sources/` (both the 2026-06 research pages and `CI Run History (2026-06)`).
> Write `C:\ProjectLegends\audit-wiki\wiki\syntheses\<FILENAME>`: a gap analysis for **<AXIS>** — <AXIS-SCOPE>. Structure: numbered findings. Each finding has exactly four parts: **Current** (cited to entity/map pages via `[[wikilink]]` plus the underlying repo path), **Practice** (cited to source pages via `[[wikilink]]`), **Gap** (one or two sentences), **Candidate recommendation** (imperative, concrete, names the files/workflows it would change). End with a table of candidate recommendations: id (`<AXIS-LETTER>-1`…), one-line summary, affected gates. No ranking, no cost estimates — that is Task 7's job. Do not run git, do not edit index or log files.

AXIS-SCOPE lines:
- Modularity (`M`): workflow factoring and overlap, reusable-workflow opportunities, module-DAG alignment of CI jobs, path-filter precision, duplication across the four workflows. Filename `Gap Analysis — Modularity (2026-06).md`.
- Maintainability (`A`): YAML size and drift risk, script sprawl in `scripts/`, hook installation friction, caching, job runtimes from [[CI Run History (2026-06)]], doc/CI mismatch. Filename `Gap Analysis — Maintainability (2026-06).md`.
- Test Coverage Intelligence (`T`): suite tiering, test selection, coverage ratcheting, fuzz cadence and corpus, determinism oracle scope, fixture debt. Filename `Gap Analysis — Test Coverage Intelligence (2026-06).md`.
- Always Green (`G`): the local-vs-CI gate delta from [[Local Dev Loop]], preflight design, required checks vs actual merges, merge queue, flake/rerun evidence, allow-failure lane discipline. Filename `Gap Analysis — Always Green (2026-06).md`.

- [ ] **Step 2: Verify** — every finding has all four parts and both citation directions; candidate-recommendation ids unique across the four pages (M-, A-, T-, G- prefixes).

- [ ] **Step 3: Wire and commit**

Add the four pages to `wiki/syntheses/_index.md`, bump count in `index.md`, four log lines, then:

```powershell
git -C C:\ProjectLegends add "audit-wiki/wiki/syntheses" "audit-wiki/index.md" "audit-wiki/log.md"
git -C C:\ProjectLegends commit -m "wiki: add CI gap analyses"
```

---

### Task 7: Adversarial recommendation review

**Files:**
- Create: `audit-wiki/wiki/syntheses/Recommendation Review (2026-06).md`
- Modify: `audit-wiki/wiki/syntheses/_index.md`, `audit-wiki/index.md`, `audit-wiki/log.md`

- [ ] **Step 1: Collect all candidate recommendations** from the four gap-analysis tables into one working list (id, summary, affected gates).

- [ ] **Step 2: Dispatch one adversarial subagent per ~8 candidates** (batch to keep prompts small). Prompt template:

> You are a skeptical reviewer. For each candidate below, answer four checks against the repo at `C:\ProjectLegends` (read the actual files — do not trust the summary): (1) **Already done?** Is it already implemented, partially or fully? Cite the file that proves or disproves. (2) **Dev-loop fit:** does it work for contributors on Windows (MSVC, `build.cmd`) and Linux? (3) **License fit:** does it respect the GPL engine / MIT proxy split (no step may link GPL code into MIT artifacts or move GPL sources into MIT-only lanes)? (4) **Cost:** one sentence on what it costs (infra, runtime, contributor friction) — no time estimates. Verdict per candidate: `keep` / `keep-modified (state the modification)` / `drop (state why)`. Candidates: <LIST>.

- [ ] **Step 3: Write the review page**

`Recommendation Review (2026-06).md`: table of every candidate id → verdict → one-line justification with citation. Dropped candidates stay in the table (the record of why matters). Wire into `_index.md`/`index.md`/`log.md`.

- [ ] **Step 4: Commit**

```powershell
git -C C:\ProjectLegends add "audit-wiki/wiki/syntheses" "audit-wiki/index.md" "audit-wiki/log.md"
git -C C:\ProjectLegends commit -m "wiki: adversarial review of CI recommendations"
```

---

### Task 8: Write CI-THESIS.md

**Files:**
- Create: `CI-THESIS.md` (repo root)
- Modify: `audit-wiki/wiki/overview.md` (link the thesis), `audit-wiki/log.md`

- [ ] **Step 1: Draft the thesis** (orchestrator writes this one — it is the synthesis voice)

Structure (exact top-level sections):

```markdown
# CI Thesis — Project Legends (2026-06)

One-paragraph statement of the thesis.

## Current state
## What the evidence shows        ← per axis, linking audit-wiki pages
## Recommendations                ← only `keep`/`keep-modified` survivors, ranked
## Defense in depth: always green ← the local-preflight + server-enforcement end state
## Adoption order                 ← dependency-ordered, no dates
## Evidence index                 ← table: every claim class → wiki page links
```

Ranking rule: order by (1) unblocks always-green, (2) reduces gate-coverage holes from the map, (3) everything else. Each recommendation: id (from gap tables), what to change (files/workflows named), evidence links (≥1 entity/map page and ≥1 source page), and its Recommendation Review verdict reference. Mark each recommendation **major** or **minor** per the spec rule: major iff it changes what a contributor must do to land a commit, or alters a CI lane's existence, trigger tier, or enforcement status.

- [ ] **Step 2: Style pass**

Terse, declarative, no hedging. Strip anything resembling: time estimates, item counts as work-volume claims, review-process narration, "key insight"/"crucially" filler.

- [ ] **Step 3: Verify citations**

Every recommendation's evidence links resolve to existing wiki pages; every major/minor tag consistent with the spec rule. Add a `See: CI-THESIS.md` line to `audit-wiki/wiki/overview.md` and a log line.

- [ ] **Step 4: Commit**

```powershell
git -C C:\ProjectLegends add CI-THESIS.md "audit-wiki/wiki/overview.md" "audit-wiki/log.md"
git -C C:\ProjectLegends commit -m "docs: add CI thesis"
```

---

### Task 9: Openspec proposals for major recommendations

**Files:**
- Create: `openspec/changes/<change-id>/...` per major recommendation (ids assigned by the openspec-propose skill)

- [ ] **Step 1: List major recommendations** from `CI-THESIS.md` (the ones tagged major).

- [ ] **Step 2: For each major recommendation, invoke the repo's `openspec-propose` skill** (`.claude/skills/openspec-propose/`) with the recommendation text + its thesis evidence links as input. One proposal per recommendation; group only when two recommendations modify the same workflow file inseparably.

- [ ] **Step 3: Validate each**

Run: `openspec validate <change-id> --strict`
Expected: exit 0 per change. Fix and re-validate on failure.

- [ ] **Step 4: Commit**

```powershell
git -C C:\ProjectLegends add openspec/changes
git -C C:\ProjectLegends commit -m "openspec: propose CI improvement changes"
```

---

### Task 10: Wiki lint and final verification

**Files:** none new (fixes only)

- [ ] **Step 1: Lint the wiki** — invoke the `llm-wiki` skill's lint operation over `audit-wiki/`: orphan pages, broken `[[wikilinks]]`, pages missing from `_index.md`, uncited claims on entity/concept pages. Fix findings; uncited claims get a citation or get cut.

- [ ] **Step 2: Repo hygiene gates**

```powershell
python C:\ProjectLegends\scripts\check_conflict_markers.py
python C:\ProjectLegends\scripts\check_case_collisions.py
```

Expected: both exit 0 (run from repo root; pass `--path .` if the script requires it).

- [ ] **Step 3: Confirm no generated graph artifacts staged**

Run: `git -C C:\ProjectLegends log --stat --oneline 47cdbac..HEAD -- graphify-out`
Expected: no commits touch `graphify-out/` (Task 1 Step 1's tracked list unchanged).

- [ ] **Step 4: Final commit (lint fixes, if any)**

```powershell
git -C C:\ProjectLegends add audit-wiki
git -C C:\ProjectLegends commit -m "wiki: lint fixes"
```

(Skip if Step 1 found nothing.)

---

## Self-review record

Spec coverage: P1→Tasks 1–2, P2→Tasks 3–4, P3→Task 5, P4→Task 6, P5→Tasks 7–9, quality rules→standing rules + Task 10. Deliverables: wiki pages (2,3,4,5,6,7), CI-THESIS.md (8), openspec proposals (9). Dependency verification was completed before this plan (spec "Dependencies" section). Naming checked: page titles, slugs, and candidate-id prefixes (M/A/T/G) are used consistently across Tasks 5–8.
