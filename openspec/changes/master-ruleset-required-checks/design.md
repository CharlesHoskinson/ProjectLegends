## Context

No ruleset and no branch protection exist on `master` — verified server-side: `gh api repos/{owner}/{repo}/rules/branches/master` → `[]`, branch-protection endpoint → 404 (audit-wiki/wiki/syntheses/Recommendation Review (2026-06).md, G-2). 233 of 397 retained runs are direct pushes; the `CI` workflow's verdict constrains nothing (CI-THESIS.md §Current state). The five candidate required checks are existing unconditional `ci.yml` job names: `Linux (gcc)`, `Linux (clang)` (matrix expansion of `.github/workflows/ci.yml:37`), `Linux IPC (gcc)` (`:96`), `Windows (MSVC)` (`:190`), `C ABI Verification` (`:407`). The ruleset itself is a server-side GitHub setting; nothing in the repo can enforce it directly, so the repo carries its declared configuration and the command that applies it.

## Goals / Non-Goals

**Goals:**
- An Active ruleset on `master`: PRs required, the five exact-name checks required, branches up to date before merge, force pushes and deletions blocked.
- A repo-tracked source of truth: `docs/ci/master-ruleset.json` (the exact API payload) plus `docs/ci/merge-policy.md` (the human policy).
- Verification procedure via `gh api` reads, runnable by any reader with `gh` auth.
- Explicit sequencing gate on R1 (`ci-stabilize-mandatory-lanes`).

**Non-Goals:**
- Merge queue. Deferred: PR volume is low (56 PR events in ~5 months), require-up-to-date already delivers the never-merge-red invariant at this volume, and no workflow declares a `merge_group` trigger — enabling a queue today would deadlock on never-reporting checks (Merge Queues & Required Checks (2026-06).md, P5/P10; Recommendation Review G-4).
- Extending the required set beyond the five. Script/DAG gates are path-filtered and would pend forever on non-matching PRs; they become requirable only after R6 (`requirable-path-gates`).
- Workflow-file changes. The five checks already run on every PR.

## Decisions

**D1 — Ruleset, not classic branch protection.** Rulesets layer, carry an enforcement status (can be staged Disabled, flipped Active), and are visible to anyone with read access — reviewers of an audited public repo can verify the gate without admin rights. Classic protection has none of these properties (Merge Queues & Required Checks (2026-06).md, P3). Alternative rejected: classic branch protection — GitHub's own docs route new configuration through rulesets.

**D2 — Exact `master` ref, no wildcard.** Condition targets `refs/heads/master` literally. Wildcard patterns block later merge-queue adoption and widen the blast radius for no benefit (P3).

**D3 — Required checks by expanded job name.** Required checks match the *expanded* name; run history shows `Optional Linux SDL3 (${{ matrix.compiler }})` recorded under its template name and never executing — a required check registered under a never-reporting name blocks every merge (P4). Hence the set is the five names above, byte-exact, and the policy doc carries the maintenance rule: any change renaming `ci.yml` jobs (R8) updates `docs/ci/master-ruleset.json` and re-applies the ruleset in the same change (CI-THESIS.md R2/R8).

**D4 — `strict_required_status_checks_policy: true` (require branches up to date).** This is the queue-substitute: every merge re-validates against current `master`, giving the not-rocket-science invariant with zero new workflow plumbing (P10). Cost — manual update-and-wait on each stale PR — is acceptable at current PR volume.

**D5 — JSON payload committed, applied by `gh api`.** `docs/ci/master-ruleset.json` is the literal request body for `POST /repos/{owner}/{repo}/rulesets`; the apply and verify commands are documented beside it. This makes the server-side setting reviewable in PRs and diffable against live state. Alternative rejected: settings-as-code apps (Probot/Terraform) — new infrastructure for one ruleset on a single-maintainer repo.

**D6 — Bypass: repository-admin role only, treated as an incident.** Granting blanket admin bypass would reproduce the direct-push regime with a green checkmark; the policy doc states each bypass must be deliberate and is visible in the ruleset audit trail (P9). No other bypass actors.

**D7 — Sequenced strictly after R1.** With the `CI` workflow at 87.2% failure pre-stabilization, requiring the checks now freezes merging (P2: "Protection is the last step of a green-up, not the first"). The apply task is gated on `ci-stabilize-mandatory-lanes` being archived and the five checks green on master's head.

## Risks / Trade-offs

- [Ruleset drifts from `docs/ci/master-ruleset.json` via UI edits] → policy doc declares the JSON canonical; verification step diffs live state (`gh api repos/{owner}/{repo}/rulesets`) against the file; any divergence is fixed by re-applying the file.
- [A required check stops reporting after a job rename lands without the name-sync rule] → every merge blocks; recovery is immediate (rename the check in the ruleset); the name-sync rule in `merge-policy.md` plus the R8 cross-reference make this a reviewed step, not a surprise.
- [R1 lanes regress after the ruleset is active] → merging freezes — by design; the fix is fixing the lane, not demoting the gate (no-demotion-without-exit rule, CI-THESIS.md R1).
- [Single maintainer locked out mid-incident] → admin bypass exists (D6); use is auditable rather than forbidden.
- [Up-to-date requirement adds re-run latency per stale PR] → accepted at current volume; revisit merge queue when concurrent-PR contention is observed (P10).

## Migration Plan

1. Land this change's documents (any time; no behavioral effect).
2. After R1 is archived and the five checks are green on `master` head: apply the ruleset with the documented `gh api` POST.
3. Verify with the documented `gh api` reads.
4. Rollback: set the ruleset's enforcement to `disabled` via `PUT /repos/{owner}/{repo}/rulesets/{id}` (staged, reversible) rather than deleting it.

## Open Questions

- None blocking. Whether `Linux (gcc)`/`Linux (clang)` survive as separate names after R8 consolidation is R8's question; the name-sync rule covers it.
