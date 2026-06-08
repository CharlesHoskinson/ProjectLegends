# ProjectLegends Graphify Interface

This repository uses Graphify as the raw AST graph and a deterministic ProjectLegends overlay for domain evidence.

The repo-facing entry point is:

```powershell
python scripts/graphify_projectlegends.py <command> --repo .
```

## Commands

Local full refresh:

```powershell
python scripts/graphify_projectlegends.py update --repo .
```

This runs `graphify update . --no-cluster`, rebuilds `graphify-out/projectlegends-enrichment.json`, rebuilds `graphify-out/projectlegends-graph-enriched.json`, regenerates `docs/architecture/graphify-enrichment-report.md`, and runs the strict checker.

Source-only CI refresh:

```powershell
python scripts/graphify_projectlegends.py update --repo . --source-only
```

This skips raw Graphify and validates only the source-derived ProjectLegends overlay. CI uses this mode because `graphify-out/graph.json` is generated and may not be checked into a clean runner.

Strict check:

```powershell
python scripts/graphify_projectlegends.py check --repo . --strict --strict-tests fail
```

Summary:

```powershell
python scripts/graphify_projectlegends.py summary --repo .
```

Explain one public API:

```powershell
python scripts/graphify_projectlegends.py explain-api legends_mount_drive --repo .
```

Print common commands:

```powershell
python scripts/graphify_projectlegends.py commands
```

## Artifacts

* `graphify-out/graph.json` - Raw Graphify AST graph. Generated locally.
* `graphify-out/projectlegends-enrichment.json` - ProjectLegends domain overlay.
* `graphify-out/projectlegends-graph-enriched.json` - Disposable merged graph.
* `docs/architecture/graphify-enrichment-report.md` - Generated human-readable summary.
* `docs/superpowers/reviews/2026-06-08-graphify-enrichment-qa.md` - QA handoff for the initial enrichment implementation.

## Audit Rule

Use the interface before architecture or capability claims:

```powershell
python scripts/graphify_projectlegends.py update --repo .
python scripts/graphify_projectlegends.py explain-api <legends_api> --repo .
```

The graph is evidence, not authority. Any claim that changes source behavior must still pass the normal build and test gates.
