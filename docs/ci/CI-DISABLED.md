# CI temporarily disabled

**Date:** 2026-07-15  
**Reason:** Sprint velocity — full GitHub Actions suite was dominating iteration time.  
**Intent:** Rebuild CI after product sprints land.

## How it was disabled

Workflows were **disabled in the GitHub UI/API** (not deleted):

```text
gh workflow disable "CI"
gh workflow disable "Module DAG"
gh workflow disable "Optional PAL CI"
gh workflow disable "Sprint 2 Checks"
```

Workflow YAML remains under `.github/workflows/` for later restoration.

## How to re-enable

```bash
cd C:\ProjectLegends
gh workflow enable "CI"
gh workflow enable "Module DAG"
gh workflow enable "Optional PAL CI"
gh workflow enable "Sprint 2 Checks"
```

Or: GitHub → **Actions** → select workflow → **…** → **Enable workflow**.

## Local verification (until CI returns)

```bash
cmake -B build -G Ninja -DLEGENDS_BUILD_TESTS=ON -DLEGENDS_HEADLESS=ON
cmake --build build
ctest --test-dir build --output-on-failure
```

Windows GUI path: see `docs/superpowers/plans/2026-07-15-windows-gui-compile-and-run.md`.

## Do not

- Assume `master` is continuously green on Actions while this is in effect.
- Delete workflow files without a replacement plan.
