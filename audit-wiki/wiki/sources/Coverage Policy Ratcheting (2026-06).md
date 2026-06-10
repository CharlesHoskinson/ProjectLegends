---
type: source
aliases: ["Coverage Ratcheting Research"]
tags: [source, type/source, topic/research, topic/ci]
created: 2026-06-10
updated: 2026-06-10
status: draft
title: Coverage Policy Ratcheting (2026-06)
authors: [research synthesis from external sources]
url:
publisher:
published: 2026
accessed: 2026-06-10
source_type: research-synthesis
covers:
  - "[[Build & CI System (Project Legends)]]"
  - "[[Project Legends Test Suite]]"
---

# Coverage Policy Ratcheting (2026-06)

## Summary

Research synthesis on moving Project Legends' coverage lane from report-only to enforced without freezing development. Raw notes with full quoted passages: `raw/research/coverage-ratcheting.md`. Six sources, all retrieved 2026-06-10: Codecov status-check and components docs, the diff-cover tool docs, the lcov/genhtml 2.x manual, the qntm ratchets experience report, and a Codecov legacy-codebase guide.

Current repo state this applies to: the per-PR `coverage` job (ci.yml:707-764) builds with gcc-13 `--coverage`, captures with lcov, filters `coverage.filtered.info` by removing only `/usr/*`, `*/build/_deps/*`, `*/tests/*` (ci.yml:744-747), then writes `"Coverage policy: report-only; no minimum threshold is enforced by CI yet."` (ci.yml:749). Codecov upload runs only `if: env.CODECOV_TOKEN != ''` (ci.yml:759-764). The only enforced threshold in the repo is 80% on `*/src/app/*` inside `release-validation` (ci.yml:907-921), which is gated on `startsWith(github.ref, 'refs/tags/v')` (ci.yml:879) and has never executed because no tag has been pushed.

## Applicable practices

### 1. Gate PRs on diff (patch) coverage, not absolute coverage

Diff coverage measures only new or modified lines: "If you touch a line of code, that line should be covered" — a standard that is achievable on every PR regardless of how low the legacy total is. ^[from https://github.com/Bachmann1234/diff_cover (retrieved 2026-06-10)] Codecov implements this as the `codecov/patch` status, which "only measures lines adjusted in the pull request" and can fail a PR at 0% patch coverage even when project coverage is 72%. ^[from https://docs.codecov.com/docs/commit-status (retrieved 2026-06-10)] The legacy-codebase guidance is the same: "as you're adding new tests to a legacy codebase, a best practice is to add unit tests for any new code you write," enforced "during the review process, as code is committed and merged" via patch coverage. ^[from https://about.codecov.io/blog/how-to-incorporate-code-coverage-for-a-legacy-application/ (retrieved 2026-06-10)]

This is the policy that never freezes development: an absolute threshold forces whoever happens to touch the codebase next to pay down someone else's debt before merging; a patch threshold only prices the lines a PR itself adds.

**Applicability to Project Legends:** the `coverage` job already produces `coverage.filtered.info` on every PR (ci.yml:742-748). diff-cover consumes LCov natively — "Cobertura, Clover or JaCoCo XML format, or LCov format," listing "lcov (C/C++)" among supported generators — so one added step (`diff-cover coverage.filtered.info --compare-branch=origin/master --fail-under=80`) converts the lane to enforced diff coverage with no Codecov dependency. ^[from https://github.com/Bachmann1234/diff_cover (retrieved 2026-06-10)] Two C++-specific caveats: lcov path strings in the `.info` must exactly match the git-diff paths, and multi-line statements may be skipped because "coverage reports usually list code statements" while diffs list lines (the `--expand-coverage-report` workaround is XML-only). ^[from https://github.com/Bachmann1234/diff_cover (retrieved 2026-06-10)]

### 2. Ratchet the absolute floor instead of jumping to 80%

For the absolute number, the well-attested mechanism is a hard-coded floor stored in the repo that fails CI in both directions: "If the script counts too many instances, it raises an error ... If it counts too few, it also raises an error, this time congratulating you and prompting you to lower the expected number." ^[from https://qntm.org/ratchet (retrieved 2026-06-10)] The two-sided check is what makes it a ratchet — improvements get locked in promptly instead of leaving slack that later regressions can consume. The same report is candid about the failure modes: the ratchet "does nothing to actively encourage the removal" of debt, occasionally has to be manually loosened "due to extenuating circumstances," and only works where the team honors it, since the rules "are enforced by the same people, and encoded in the same repository, as the arena where the rules are applied." ^[from https://qntm.org/ratchet (retrieved 2026-06-10)]

Codecov packages the never-decrease semantics as `target: auto`: the project status compares against "the coverage from the base commit (pull request base or parent commit)," with `threshold: <number>` as explicit wiggle room to "allow the coverage to drop by <number>%" before failing. ^[from https://docs.codecov.com/docs/commit-status (retrieved 2026-06-10)]

> [!conflict]
> How aggressively to advance the ratchet is disputed. jest-ratchet auto-bumps the stored threshold on every 0.01% uptick (search-result summary; not fetched), and qntm plans automation that would "ratchet the expected counts downwards automatically." ^[from https://qntm.org/ratchet (retrieved 2026-06-10)] But Codecov's `target: auto` exists with a `threshold` slack parameter precisely because exact base-vs-head comparison fails PRs over measurement noise and unrelated-line drift. ^[from https://docs.codecov.com/docs/commit-status (retrieved 2026-06-10)] A commenter on the qntm thread describes a third variant — "checking the count in the current branch is no greater than the count in the merge target. Less chance for misuse" — which needs no stored number at all but also never congratulates/locks in progress. ^[from https://qntm.org/ratchet (retrieved 2026-06-10)] For gcov/lcov specifically, coverage of templates and inline functions is link-order sensitive, so a small slack (Codecov `threshold: 0.5` or a manually-bumped floor rather than auto-bump) is the safer reading.

**Applicability to Project Legends:** the repo-stored-floor pattern fits the existing toolchain: replace the echo at ci.yml:749 with `lcov --summary` extraction plus a comparison against a committed `coverage-floor.txt` (the release-validation block at ci.yml:907-921 already contains the exact `lcov --summary | grep -oP` + `bc -l` shell needed — it just runs in the wrong job, on one directory, behind a tag gate that has never fired). Start the floor at whatever `coverage.filtered.info` measures today, fail below it, and print-don't-fail above it until the team opts into two-sided ratcheting.

### 3. Per-module thresholds via Codecov components (or lcov --extract) against the module DAG

Codecov Components are "virtual filters ... fully defined in the codecov.yml" — unlike Flags they "do not have to be supplied at upload time," so a single merged lcov upload can drive separate per-directory status checks, each with its own `type: project|patch` and `target`. ^[from https://docs.codecov.com/docs/components (retrieved 2026-06-10)] This is exactly the "parts of your code that are not easily broken up into different uploads" case. ^[from https://docs.codecov.com/docs/components (retrieved 2026-06-10)] The same effect is available token-free in plain status config via `paths:` ("you can set project statuses filtering out specific components of the application, and get 3 unique statuses monitoring each component"). ^[from https://docs.codecov.com/docs/commit-status (retrieved 2026-06-10)] Without Codecov, lcov 2.x `genhtml --criteria-script` evaluates a callback per "source file or directory name" and returns non-zero when criteria fail, enabling per-directory thresholds locally. ^[from https://manpages.debian.org/unstable/lcov/genhtml.1.en.html (retrieved 2026-06-10)]

**Applicability to Project Legends:** the module set is already machine-enforced — `module-dag.yml` verifies include rules and the CMake dependency DAG over `src/app`, `src/legends`, `src/legends_ipc`, `src/legends_proxy`, `src/engine_host`, `src/pal`, `src/libs`. Those seven directories are the natural component boundaries: one codecov.yml `individual_components` entry per module (paths `src/legends/**` etc.), with differentiated targets — strictest on the trust-boundary modules (`src/legends_ipc`, `src/legends_proxy`), looser on `src/pal`. This directly fixes the gap the Test Coverage Audit flagged: the sole enforced threshold covers only `*/src/app/*` (ci.yml:912-917), "leaving src/legends/, src/legends_ipc/, src/legends_proxy/, src/engine_host/, and src/pal/ outside every enforced gate" ([[Test Coverage Audit (2026-06)]], test-cov-13). The lcov-native equivalent is a loop of `lcov --extract coverage.filtered.info "*/src/<module>/*"` + per-module floor file — the release-validation job already demonstrates the single-module version of this.

### 4. Exclude the vendored engine from policy totals; track it separately if at all

The legacy-codebase guidance is to map what is covered first and then "discover and prioritize sections of your code where tests will have the highest impact" rather than chase a global percentage. ^[from https://about.codecov.io/blog/how-to-incorporate-code-coverage-for-a-legacy-application/ (retrieved 2026-06-10)] A vendored ~DOSBox-X engine is the limiting case: its denominator dominates any whole-repo number, and no PR-level policy can move it.

**Applicability to Project Legends:** the lcov filter at ci.yml:744-747 removes `/usr/*`, `*/build/_deps/*`, `*/tests/*` but **not** `engine/`, so the published `coverage.filtered.info` mixes first-party `src/` coverage with the vendored engine tree (`C:\ProjectLegends\engine\` — own CMakeLists.txt, include/, src/, tests/). Any absolute threshold or `target: auto` ratchet computed on that file is dominated by engine code the team does not own. Three composable fixes: (a) add `'*/engine/*'` to the `lcov --remove` list so the policy artifact covers only `src/`; (b) if engine visibility is still wanted, make it a Codecov component (`component_id: engine`, paths `engine/**`) with an informational-only status, since components are pure path filters over the same upload ^[from https://docs.codecov.com/docs/components (retrieved 2026-06-10)]; (c) diff coverage (practice 1) is naturally robust here — PRs that don't touch `engine/` contribute no engine lines to the diff denominator — but excluding `engine/**` via diff-cover `--exclude` keeps engine-touching PRs from being held to first-party standards. ^[from https://github.com/Bachmann1234/diff_cover (retrieved 2026-06-10)]

### 5. Don't let enforcement depend on the Codecov token

The upload step runs only `if: env.CODECOV_TOKEN != ''` (ci.yml:759-764), so any policy delegated to Codecov status checks silently vanishes when the secret is absent — and Codecov's own `if_not_found` default is `success`: "the status will pass if there is no report for the head." ^[from https://docs.codecov.com/docs/commit-status (retrieved 2026-06-10)] Token-free alternatives exist in tools already installed in the job: lcov 2.x has native `--fail-under-lines` / `--fail-under-branches` flags and the `--criteria-script` hook that "will return a non-zero status and print a message if the criteria are not met" ^[from https://manpages.debian.org/unstable/lcov/genhtml.1.en.html (retrieved 2026-06-10)]; genhtml also computes differential coverage locally from a `--baseline-file` plus `--diff-file`, classifying every line into 12 categories including UNC ("Uncovered New Code: newly added code is not tested") and LBC ("Lost Baseline Coverage: unchanged code is no longer tested") — i.e., both the patch-coverage and the regression-detection signal, with no external service. ^[from https://manpages.debian.org/unstable/lcov/genhtml.1.en.html (retrieved 2026-06-10)]

**Applicability to Project Legends:** keep Codecov as the reporting/UI layer (conditional upload is fine for that), but put the *gate* in the workflow itself: diff-cover `--fail-under` or lcov `--fail-under-lines`/`--criteria-script` run unconditionally on `coverage.filtered.info`. The ci.yml:749 echo then becomes a real policy statement instead of an apology. One repo-side prerequisite: the `coverage` job must be a required status check on the protected branch for any in-job failure to bind — an enforced step in a non-required job is still report-only in effect (whether it is currently required is a branch-protection setting, not visible in ci.yml; see [[CI Run History (2026-06)]] for which jobs actually execute).

### 6. Stage the rollout: informational first, then enforce

Codecov's `informational: true` mode posts the status but "will pass no matter what the coverage is," explicitly intended "to expose codecov information to other developers in your pull request without necessarily gating PRs on that information." ^[from https://docs.codecov.com/docs/commit-status (retrieved 2026-06-10)] The ratchet experience report warns against the other failure mode — over-tightening: "it would be easy to abuse this technique to enforce unnecessarily strict 'standards' on a development team who really ought to be allowed some creative freedom." ^[from https://qntm.org/ratchet (retrieved 2026-06-10)] And before trusting any gate, "it's extremely important to verify that your tests can fail" — a gate that has never been observed red is untested code. ^[from https://about.codecov.io/blog/how-to-incorporate-code-coverage-for-a-legacy-application/ (retrieved 2026-06-10)]

**Applicability to Project Legends:** the 80%-on-`src/app` release-validation check (ci.yml:907-921) is the cautionary instance — a threshold that has never run is a gate that has never been verified to fail, and nobody knows today whether `src/app` actually clears 80%. Sequence: (1) one PR cycle with diff-cover/patch status posted informationally; (2) flip patch coverage to required at a modest target (diff-cover default comparisons use the `...` range, matching PR semantics); (3) add the absolute ratchet floor; (4) per-module component targets last. Also rehearse the release-validation job once via `workflow_dispatch` before the first real tag, so its first execution is not on the release path.

## Most applicable practices (ranked)

1. **Diff coverage gate on the existing lcov artifact** (practice 1 + 5): diff-cover `--fail-under` on `coverage.filtered.info`, token-free, replaces the ci.yml:749 echo.
2. **Engine exclusion from the policy denominator** (practice 4): add `'*/engine/*'` to the ci.yml:744-747 `lcov --remove`; prerequisite for every other number meaning anything.
3. **Per-module floors aligned to the module DAG** (practice 3): Codecov components or `lcov --extract` loops over `src/{legends,legends_ipc,legends_proxy,engine_host,pal,app}`, promoting the never-run `src/app`-only release check into per-PR per-module policy.

## Related

- [[Build & CI System (Project Legends)]] — the coverage job and release-validation under audit.
- [[Test Coverage Audit (2026-06)]] — finding test-cov-13 (report-only coverage; only `src/app` behind a never-run gate) motivates this research.
- [[CI Run History (2026-06)]] — empirics on which jobs actually run and which checks are required.
- [[Quality Gate Demotion (2026-06-08)]] — the surrounding pattern of weakening gates; ratcheting is the inverse mechanism.
