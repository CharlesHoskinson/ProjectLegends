---
type: source
aliases: ["Merge Queues Research", "Required Checks Research", "Merge Queue Best Practice (2026-06)"]
tags: [source, type/source, topic/ci, topic/research, topic/branch-protection]
created: 2026-06-10
updated: 2026-06-10
status: draft
title: Merge Queues & Required Checks (2026-06)
authors: [GitHub Docs, GitHub Engineering (Smythe & Gripper), Shopify Engineering (Jack Li), Adrian Colyer summarizing Ananthanarayanan et al. EuroSys'19 (Uber), Graydon Hoare]
url:
publisher: various (see raw extracts)
published: 2014–2026
accessed: 2026-06-10
source_type: research-synthesis
covers:
  - "[[Build & CI System (Project Legends)]]"
  - "[[CI Workflows (GitHub Actions)]]"
  - "[[Quality Gate Demotion (2026-06-08)]]"
---

# Merge Queues & Required Checks (2026-06)

## Summary

External research synthesis on GitHub merge queue mechanics, required-check selection, branch protection vs rulesets, and batching trade-offs, applied to the Project Legends repository. Six sources fetched 2026-06-10; raw passages in `raw/research/merge-queues-required-checks.md`. Uber's first-party blog post is dead (404 on both uber.com and eng.uber.com paths); the EuroSys'19 SubmitQueue paper is cited via Adrian Colyer's summary. The through-line of every source is Graydon Hoare's "not rocket science rule": automatically maintain a repository of code that always passes all the tests — test the *integrated* result before the merge advances the branch, never after. Project Legends currently does the opposite: per [[CI Run History (2026-06)]], the `CI` workflow fails 87% of runs on `master`, 233 of 397 runs are direct pushes, and no branch protection or ruleset is in effect.

## Practices

### P1. Enforce the not-rocket-science rule: master never advances to a failing commit

The rule: "automatically maintain a repository of code that always passes all the tests"; CI done in the common order — code accepted before testing, or tested in isolation and then merged — "leaves a potentially broken tree" and is used "only to learn (rapidly) when the tree was broken, not prevent it breaking in the first place." ^[from https://graydon2.dreamwidth.org/1597.html (retrieved 2026-06-10)] GitHub's merge queue is the productized form: it "ensures our main branch is never updated to a failing commit by enforcing branch protection rules." ^[from https://github.blog/engineering/engineering-principles/how-github-uses-merge-queue-to-ship-hundreds-of-changes-every-day/ (retrieved 2026-06-10)] Shopify's first rule of deploys: "Master must always be green (passing CI) ... If master is not green, our developers cannot merge, slowing all development." ^[from https://shopify.engineering/successfully-merging-work-1000-developers (retrieved 2026-06-10)]

**Applicability to Project Legends:** this is the central gap. 322 of 397 retained Actions runs are on `master` and 265 of them failed; 233 of 397 are `push` events, i.e. commits landing without any pre-merge gate ([[CI Run History (2026-06)]]). Any fix touches repository settings (a ruleset on `master` requiring PRs and required checks), not the workflow files alone — `.github/workflows/ci.yml` already runs on `pull_request` (lines 18–27), it just gates nothing.

### P2. Green-before-gate: required checks must be reliably passing before protection or a queue is switched on

Uber's mainline was "green only 52% of the time" before SubmitQueue; the system's value is conditional on builds that pass deterministically for good changes. ^[from https://blog.acolyer.org/2019/04/18/keeping-master-green-at-scale/ (retrieved 2026-06-10)] Shopify could only operate its queue because removal of failing PRs kept the pipeline moving — a queue over a permanently red suite stops all merging. ^[from https://shopify.engineering/successfully-merging-work-1000-developers (retrieved 2026-06-10)]

**Applicability to Project Legends:** with the `CI` workflow at 87.2% failure (6 successes in 164 runs, all post-[[Quality Gate Demotion (2026-06-08)]]) and the sanitizer and fuzz lanes failing every sampled execution ([[CI Run History (2026-06)]]), enabling required checks over the *current* job set would freeze the repository. Sequence: first stabilize or descope the lanes in `.github/workflows/ci.yml` (jobs `sanitizers`, `fuzz`), then make the stable subset required, then (optionally) add the queue. Protection is the last step of a green-up, not the first.

### P3. Use rulesets, not classic branch protection, as the enforcement mechanism

Rulesets layer (multiple rulesets aggregate, "the most restrictive version of the rule applies"), have enforcement statuses (Active/Disabled) so they can be staged without deletion, and are visible to anyone with read access, so contributors can see why a rule fired without admin rights. They coexist with and layer over any existing branch protection rules. ^[from https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/managing-rulesets/about-rulesets (retrieved 2026-06-10)] One mechanic still phrased in branch-protection terms: "Repository administrators can require a merge queue by enabling the branch protection setting 'Require merge queue' in the protection rules for the base branch," and "a merge queue cannot be enabled with branch protection rules that use wildcard characters (*) in the branch name pattern"; the docs elsewhere state queue and PR checks are "configured under branch protection rules or rulesets." ^[from https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/configuring-pull-request-merges/managing-a-merge-queue (retrieved 2026-06-10)]

**Applicability to Project Legends:** the repo evidently has neither rulesets nor branch protection (direct pushes to `master` dominate the run history). Create one Active ruleset targeting exactly `master` (no wildcard, which also keeps it merge-queue-compatible): require a pull request, require the P4 status checks, block force pushes. The read-visibility property matters for an audited public repo — reviewers can verify the gate without admin access.

### P4. Required-check selection: a small, deterministic, exact-name set

The queue/protection gate is "all required status checks"; the queue "will wait for required checks to be reported before it can proceed with merging," and a check that never reports causes the merge to fail (or time out per the "status check timeout" setting). ^[from https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/configuring-pull-request-merges/managing-a-merge-queue (retrieved 2026-06-10)] Graydon's caveat governs the size of the set: "your integration cycle time is bounded by your test cycle time," and where full test time is too long, projects define "an integration-test subset." ^[from https://graydon2.dreamwidth.org/1597.html (retrieved 2026-06-10)]

**Applicability to Project Legends:** candidate required set from `.github/workflows/ci.yml`, matching the lanes that already run per-PR and pass: `Linux (gcc)`, `Linux (clang)`, `Linux IPC (gcc)`, `Windows (MSVC)`, `C ABI Verification`. Required checks are matched by the *expanded* job name — the run history shows `Optional Linux SDL3 (${{ matrix.compiler }})` recorded under its unexpanded template name and never executing ([[CI Run History (2026-06)]]); a required check registered under a name that never reports blocks every merge. Path-filtered workflows (`sprint2-checks.yml` triggers only on `paths:` matching CMake files) must not be required as-is for the same reason: on PRs that don't touch those paths the check never reports. Keep the heavyweight lanes (sanitizers, fuzz, TLA+, coverage) out of the required set but on schedule — with an exit plan, unlike the silent [[Quality Gate Demotion (2026-06-08)]]. Wall-clock bound for the proposed set is the `Windows (MSVC)` job (median 960s ≈ 16 min), acceptable for a GoogleTest suite at thousands-of-tests scale.

### P5. Every workflow producing a required check must trigger on `merge_group`

"You must use the `merge_group` event to trigger your GitHub Actions workflow when a pull request is added to a merge queue. ... Otherwise, status checks will not be triggered when you add a pull request to a merge queue. The merge will fail as the required status check will not be reported. The `merge_group` event is separate from the `pull_request` and `push` events." Third-party CI instead watches pushes to branches prefixed `gh-readonly-queue/{base_branch}`. ^[from https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/configuring-pull-request-merges/managing-a-merge-queue (retrieved 2026-06-10)]

**Applicability to Project Legends:** no workflow in `.github/workflows/` (`ci.yml`, `pal-ci.yml`, `module-dag.yml`, `sprint2-checks.yml`) carries a `merge_group` trigger today. If a queue is adopted, add `merge_group:` to the `on:` block of `ci.yml` (lines 18–27) and audit every job-level `if:` that whitelists event names — e.g. `ci.yml` lines 334–337 and 483–486 enumerate `pull_request`/`push`/`schedule`/`workflow_dispatch` and would silently skip on `merge_group`, recreating the never-reporting-check deadlock at job granularity.

### P6. Queue mechanics: speculative groups, automatic eviction, no queue-jumping

GitHub's queue is FIFO; each entry gets a temporary branch containing the target branch plus all entries ahead of it; on a failing required check the offending PR is evicted and the branches behind it are rebuilt without it; eviction also occurs on CI timeout, user request, or unresolvable protection failure. Jumping to the top "will cause a full rebuild of all in-progress pull requests." ^[from https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/configuring-pull-request-merges/managing-a-merge-queue (retrieved 2026-06-10)] This is the productized version of Uber's insight that a strictly serial queue does not scale ("with a thousand changes per day ... the turnaround time of the last enqueued change will be over 20 days") and that the cure is speculative parallel builds over the queue prefix. ^[from https://blog.acolyer.org/2019/04/18/keeping-master-green-at-scale/ (retrieved 2026-06-10)] GitHub's design goal: "Those causing conflicts or build failures should not impact all other pull requests waiting to merge. The throughput of the overall system should be favored over fairness to an individual pull request." ^[from https://github.blog/engineering/engineering-principles/how-github-uses-merge-queue-to-ship-hundreds-of-changes-every-day/ (retrieved 2026-06-10)]

**Applicability to Project Legends:** nothing to build — the platform supplies all of this once "Require merge queue" is enabled on `master`. The relevant local fact is cost per speculation: each `merge_group` build re-runs the required lanes, and the vendored DOSBox-X engine is rebuilt cold every time because no workflow uses ccache/sccache ([[Build & CI System (Project Legends)]], CI-06). Compiler caching in `ci.yml` is a prerequisite for the queue being cheap.

### P7. Batching trade-offs: bounded small batches, bounded speculation depth

GitHub exposes the knobs directly: build concurrency (1–100 `merge_group` webhooks), min/max PRs merged together (1–100), and a wait-time timeout to merge below the minimum; max group size protects deploy blast radius, min group size amortizes a lengthy CI/deploy cycle. ^[from https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/configuring-pull-request-merges/managing-a-merge-queue (retrieved 2026-06-10)] Shopify's calibration at ~400 commits/day: "Larger batches result in higher theoretical throughput, but higher risk. In practice, the increased risk of larger batches impedes throughput by causing failures that are harder to isolate ... we went with a batch size of 8" with CI running on only 3 batches at a time to bound CI spend. ^[from https://shopify.engineering/successfully-merging-work-1000-developers (retrieved 2026-06-10)] GitHub's old train system showed the failure mode of oversized batches: 15-PR trains that "frequently derailed," costing developers 8+ hour waits. ^[from https://github.blog/engineering/engineering-principles/how-github-uses-merge-queue-to-ship-hundreds-of-changes-every-day/ (retrieved 2026-06-10)]

**Applicability to Project Legends:** PR volume is low (56 `pull_request` events in ~5 months of run history — [[CI Run History (2026-06)]]), so batching for throughput is unnecessary: minimum group 1, maximum small (≤5), short wait time, build concurrency 2–3. The binding constraint is the ~3h serial compute per full cycle and the 16-min Windows lane, not queue depth.

### P8. Flake policy: distinguish flaky from deterministic failures; don't tune for flake you shouldn't have

GitHub's "Only merge non-failing pull requests" setting, when disabled, lets a group merge if only its head entry (the combined changes) passes — "useful if you have intermittent test failures, but don't want false negatives to hold up the queue." ^[from https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/configuring-pull-request-merges/managing-a-merge-queue (retrieved 2026-06-10)] Shopify formalized tolerance: evict a PR only after N successive failures, because "legitimate failures will propagate to all later CI runs, but flaky tests will not"; at an assumed 25% flake rate, tolerance 3 cuts false eviction to 0.39%. ^[from https://shopify.engineering/successfully-merging-work-1000-developers (retrieved 2026-06-10)]

> [!conflict]
> The sources disagree on tolerating flake at the gate. Graydon's rule is absolute — the repository "always passes all the tests," no tolerance ^[from https://graydon2.dreamwidth.org/1597.html (retrieved 2026-06-10)] — while GitHub's docs and Shopify both build explicit flake accommodation into the queue ^[from https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/configuring-pull-request-merges/managing-a-merge-queue (retrieved 2026-06-10)] ^[from https://shopify.engineering/successfully-merging-work-1000-developers (retrieved 2026-06-10)]. The reconciliation: flake tolerance is a coping mechanism for a suite that still contains flaky tests — Shopify presents the threshold as resilience to the suite's current state, not a recommended steady state.

**Applicability to Project Legends:** the dominant failures are deterministic, not flaky — sanitizer and fuzz lanes failed 6 of 6 sampled executions over known engine data races ([[CI Run History (2026-06)]], [[Build & CI System (Project Legends)]]). Keep "Only merge non-failing pull requests" *enabled* and fix the red lanes; loosening the gate for deterministic failures just re-derives the [[Quality Gate Demotion (2026-06-08)]] with extra steps.

### P9. Emergency bypass must be explicit, narrow, and audited

Shopify blocks direct merges to master via branch protection "programmatically as part of the merge queue onboarding process," then provides a separate `/shipit --emergency` path that "skips any checks ... reserved for emergencies only and gives us auditability into the cases where this gets used." ^[from https://shopify.engineering/successfully-merging-work-1000-developers (retrieved 2026-06-10)] Rulesets carry this natively: named bypass actors (roles, teams, or GitHub Apps) per ruleset. ^[from https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/managing-rulesets/about-rulesets (retrieved 2026-06-10)]

**Applicability to Project Legends:** a single-maintainer repo will be tempted to grant the admin role blanket bypass — that reproduces today's direct-push regime with a green checkmark. Grant bypass to the repository-admin role but treat its use as an incident: each bypass push to `master` should be visible in the ruleset audit trail rather than indistinguishable from normal flow as it is now.

### P10. Whether Project Legends needs a queue at all

GitHub positions the queue for busy branches: "particularly useful on branches that have a relatively high number of pull requests merging each day from many different users," and notes it "provides the same benefits as the Require branches to be up to date before merging branch protection" without the manual update-and-wait loop. ^[from https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/configuring-pull-request-merges/managing-a-merge-queue (retrieved 2026-06-10)] The serial-queue scaling argument (Uber) only bites at hundreds-to-thousands of changes per day. ^[from https://blog.acolyer.org/2019/04/18/keeping-master-green-at-scale/ (retrieved 2026-06-10)]

> [!conflict]
> Scale-driven sources (GitHub blog, Shopify, Uber) motivate merge queues by concurrency volume that Project Legends does not have; Graydon's argument is volume-independent (stale PR test results against a moved master are unsound at any scale ^[from https://graydon2.dreamwidth.org/1597.html (retrieved 2026-06-10)]). Both ends agree on the invariant, not the machinery.

**Applicability to Project Legends:** at current volume the full invariant is achievable without a queue: ruleset on `master` requiring PRs + the P4 check set + "require branches to be up to date before merging." That forces re-validation against current `master` before every merge — the not-rocket-science guarantee with zero new workflow plumbing (`merge_group` triggers in `ci.yml` etc. become necessary only if the queue is later adopted, e.g. once multiple agents/contributors land PRs concurrently). Recommended sequencing: P2 (green-up) → P3+P4 (ruleset + required checks + up-to-date) → P5–P7 (queue) only when concurrent-PR contention is actually observed.

## Covers

- [[Build & CI System (Project Legends)]] — external best practice baseline against which the subsystem's missing enforcement (no protection, no ruleset, direct pushes, red required-candidate lanes, no compiler cache) is measured.
- [[CI Workflows (GitHub Actions)]] — concrete workflow-file deltas implied: `merge_group` trigger and event-whitelist `if:` audits in `ci.yml`; path-filter hazard in `sprint2-checks.yml`; matrix-name hazard for required-check registration.
- [[Quality Gate Demotion (2026-06-08)]] — P4 and P8 give the principled version of what the demotion did ad hoc: heavyweight lanes may leave the blocking set only with a schedule plus exit plan, and the blocking set must then actually block via a ruleset.
