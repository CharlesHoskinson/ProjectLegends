## 1. OpenSpec

- [ ] 1.1 Validate this change with `openspec.cmd validate runtimehost-proxy-parity-quality-gates --strict --json`.
- [ ] 1.2 Keep this task list current as implementation progresses.

## 2. Validators

- [ ] 2.1 Strengthen `scripts/check_capability_matrix.py` only where required by new variable-payload proxy APIs.
- [ ] 2.2 Add a proxy parity report command or generated Markdown section listing remaining missing/partial proxy APIs.
- [ ] 2.3 Ensure unsupported direct APIs are not accidentally promoted to `proxy-supported`.

## 3. Graphify And CI

- [ ] 3.1 Refresh Graphify source overlay.
- [ ] 3.2 Verify RuntimeHost app bypasses remain exactly two lifecycle calls.
- [ ] 3.3 Wire any new deterministic validator into `Sprint 2 Checks`.

## 4. QA Artifact

- [ ] 4.1 Create `docs/superpowers/reviews/2026-06-08-gemini-35-flash-openspec-runtimehost-proxy-parity-qa.md`.
- [ ] 4.2 Include before/after proxy capability counts.
- [ ] 4.3 Include passed/failed commands and top five Codex audit targets.

## 5. Verification

- [ ] 5.1 `python scripts/check_capability_matrix.py --repo .`
- [ ] 5.2 `python scripts/graphify_projectlegends.py update --repo . --source-only`
- [ ] 5.3 `python scripts/graphify_projectlegends.py runtimehost-bypasses --repo .`
- [ ] 5.4 `python scripts/check_graphify_enrichment.py --repo . --overlay graphify-out/projectlegends-enrichment.json --strict --strict-tests fail --allow-missing-graphify`
- [ ] 5.5 `python scripts/check_conflict_markers.py --path .`
- [ ] 5.6 `git diff --check`
