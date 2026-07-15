# Independent audit brief — Project Legends R1 master closeout

**For:** Codex (GPT-5.6 or later), independent senior security / correctness / CI auditor  
**Mode:** Adversarial. Do **not** trust agent claims, PR descriptions, or checked boxes without primary evidence.  
**Authority:** Prefer live GitHub Actions logs, `gh` API, and on-disk sources over narrative docs.  
**Write-only output:** Produce a review markdown under `docs/superpowers/reviews/`. Do **not** modify product code, workflows, tests, or issues unless the user separately authorizes fixes.

---

## 0. Mission

Verify whether **R1 (stabilize mandatory CI lanes)** is actually complete on **`master`**, including residual work claimed after PR #46 merge. Issue a **GO / NO-GO** merge-and-exit verdict for “R1 closed on master,” not a vibe check.

Prior independent audit (**FAIL / NO-GO**) at earlier PR tip `ba8cc8a` / run 29423831242 is **historical**. Re-evaluate current `master` from scratch; cite prior findings only when mapping residual status.

---

## 1. Pin the tree under audit

Before scoring anything:

1. `git fetch origin master`
2. Record:
   - `AUDITED_SHA=$(git rev-parse origin/master)`
   - `git log -15 --oneline origin/master`
3. Identify the latest **completed** GitHub Actions **CI** workflow run whose `head_sha` equals `AUDITED_SHA` (or note if CI is still in progress / missing).
4. If CI for `AUDITED_SHA` is incomplete, also evaluate the newest completed CI run on `master` and **state the SHA mismatch explicitly** in the executive summary (claims may be ahead of green CI).

**Agent-claimed tip (may lag; re-resolve):**

| Claim | Value |
|-------|--------|
| Branch | `master` (default; there is no `main`) |
| Claimed residual commit | `733bb96daf55f09a3337eb8cf4f45ea0d50a0f20` |
| Prior merge of PR #46 | `f39b3dab1c43a44f17c7d070e89b477bae9e1c91` |
| Prior fully green mandatory stack (pre-residual) | `98450e6` / run [29435150647](https://github.com/CharlesHoskinson/ProjectLegends/actions/runs/29435150647) |

---

## 2. Acceptance contract (what “R1 complete” means)

R1 is **complete** only if **all** of the following hold for one synchronized SHA (prefer `AUDITED_SHA`):

### 2.1 Mandatory lanes (hard gates)

| Gate | Job name (exact) | Pass criterion |
|------|------------------|----------------|
| ASan | `address Sanitizer` | `conclusion=success`; ctest not red |
| UBSan | `undefined Sanitizer` | `conclusion=success` |
| TSan | `thread Sanitizer` | `conclusion=success`; **no** `allow_failure` / `continue-on-error` on the job |
| Fuzz | `Fuzz Testing` | `conclusion=success` including smoke (all targets that CI invokes) |
| Windows | `Windows (MSVC)` | `conclusion=success` |
| MSan | — | **Absent** from matrix; #40 remains the re-entry tracker |

Also verify baseline still green or not regressed without explanation:

- `Linux (gcc)`, `Linux (clang)`, `C ABI Verification` (if present on the run)

### 2.2 Dependency scan (R1 residual / 4.3)

On **push to master**, `schedule`, or `workflow_dispatch`:

| Check | Pass criterion |
|-------|----------------|
| Job runs | `Dependency Scan` is **not** skipped solely because event is `push` to master |
| Pin integrity | osv-scanner binary SHA-256 matches workflow pin; not `releases/latest` |
| Production SBOM | Scans `docs/ci/vendored-sbom.cdx.json`; non-empty (≥4 components) |
| Generator honesty | `python3 scripts/generate_vendored_sbom.py --check` passes in CI or locally |
| Seed fail-closed | Step scanning `docs/ci/seed-known-vuln.cdx.json` **exits non-zero** (job still overall success because the step expects failure) |
| Baseline | fluidsynth CVEs either fixed **or** ignored only via issue-linked `osv-scanner.toml` (#43) |

### 2.3 TSan hygiene

| Check | Pass criterion |
|-------|----------------|
| Suppressions file | `tsan-suppressions.txt` either empty of race entries **or** every entry has issue URL + fix-and-remove criterion |
| #38 claim | If agent claims removal of `race:g_active_instance`: confirm symbol is still `std::atomic` and TSan green **without** that line |
| #39 claim | If agent claims seqlock fix: review `crash_breadcrumb.{h,cpp}`; confirm suppressions for `CrashBreadcrumb` are gone; TSan green |

### 2.4 Documentation honesty (F010)

| Check | Pass criterion |
|-------|----------------|
| OpenSpec tasks | `openspec/changes/ci-stabilize-mandatory-lanes/tasks.md` checkboxes match **live** evidence; no “checked but pending” lies |
| Residual tracker | `docs/ci/r1-residual-closeout.md` does not claim closed issues that are still open |
| CI-THESIS | R1 status paragraph matches reality (green SHA / residuals) |

### 2.5 Explicit non-requirements (do not fail R1 solely for these)

- Branch protection / required checks on master (R2) — out of R1 scope unless broken by R1.
- Full automated SBOM of every file under `engine/src/libs/**` — #42 may remain partially open if pin-based generator exists and is enforced.
- Actual fluidsynth **source upgrade** in-tree — #43 may remain open if ignores are honest and issue-linked.
- MSan re-enable — only fail if MSan was re-added without meeting `docs/ci/msan-reentry.md`.

---

## 3. Claimed work inventory (agent assertions to stress-test)

Treat every row as **alleged**. Confirm or refute with evidence.

### 3.1 Merged R1 PR

- PR [#46](https://github.com/CharlesHoskinson/ProjectLegends/pull/46) merged to `master`.
- Mandatory sanitizers + fuzz + Windows green on `98450e6` (run 29435150647).

### 3.2 Closed issues (verify state + close comments)

| Issue | Alleged resolution |
|-------|-------------------|
| #45 | WRONG_THREAD skips under TSan complete |
| #47 | ASan dual-stdlib + move leak fixed |
| #48 | Windows IPC HandshakeAck lane green |
| #38 | Dead `g_active_instance` suppression removed |
| #39 | CrashBreadcrumb seqlock; suppressions removed |

### 3.3 Still open (must remain open or be justified)

| Issue | Alleged status |
|-------|----------------|
| #40 | Parked; `docs/ci/msan-reentry.md` |
| #42 | Generator partial; full vendored tree SBOM still open |
| #43 | fluidsynth CVEs baselined until vendored upgrade |
| #44 | Scoped `/wd4875` + gsl-lite **v1.1.0** pin; full removal pending Windows proof |

### 3.4 Code / CI deltas to re-read

| Path | Why |
|------|-----|
| `.github/workflows/ci.yml` | sanitizers g++-13; fuzz clang-19; no llvm.sh; dep-scan triggers; seed step |
| `tsan-suppressions.txt` | empty race list claim |
| `src/app/crash_breadcrumb.{h,cpp}` | seqlock correctness |
| `engine/src/misc/dosbox_context.cpp` | move ownership (ASan C3) |
| `CMakeLists.txt` | `legends_gsl_msvc_options` scoping |
| `cmake/dependencies.cmake` | gsl-lite tag |
| `docs/ci/vendored-sbom.cdx.json` | component set vs generator |
| `scripts/generate_vendored_sbom.py` | pin parse + `--check` |
| `docs/ci/seed-known-vuln.cdx.json` | known-vuln fixture |
| `osv-scanner.toml` | issue-linked ignores only |
| `openspec/changes/ci-stabilize-mandatory-lanes/tasks.md` | honesty |

---

## 4. Mandatory evidence procedures (E-suite)

Run or query each. Mark **PASS / FAIL / BLOCKED** with URLs or log excerpts.

| ID | Procedure |
|----|-----------|
| **E1** | `git rev-parse origin/master`; list last 15 commits. |
| **E2** | Latest CI run for that SHA: `gh run list --branch master --workflow CI --limit 5`. Capture run id, conclusion, headSha. |
| **E3** | For that run, job conclusions for: address, undefined, thread, Fuzz Testing, Windows (MSVC), Dependency Scan, Linux (gcc), Linux (clang). Use `gh api .../jobs`. |
| **E4** | Download / API-log **thread Sanitizer**: confirm configure C++23 PASS, build success, ctest success; search for `WARNING: ThreadSanitizer` / `SUMMARY: ThreadSanitizer`. Note whether suppressions file is empty of `race:` lines. |
| **E5** | Log **address Sanitizer**: confirm not dual-stdlib cascade; no mass `alloc-dealloc-mismatch`. Note any remaining failed tests. |
| **E6** | Log **Fuzz Testing**: configure with clang-19; all smoke targets complete; `corpus/config` exists; no missing directory errors. |
| **E7** | Log **Dependency Scan** (must run on master push): pin verify, `--check` SBOM, production scan exit 0 with config, seed step non-zero expected. |
| **E8** | Static: `rg "race:" tsan-suppressions.txt` — empty of active race lines (comments OK). |
| **E9** | Static: `g_active_instance` is `std::atomic` in `legends_embed_api.cpp`. |
| **E10** | Static review of CrashBreadcrumb seqlock (writer CAS, reader retry, no bare fence-only design). Flag remaining races if any. |
| **E11** | Static: MSVC `/wd4875` not on global `legends_compile_options`; only `legends_gsl_msvc_options` consumers. |
| **E12** | `python3 scripts/generate_vendored_sbom.py --check` (local or CI log). |
| **E13** | Issue API: `gh issue view` for #38,#39,#40,#42,#43,#44,#45,#47,#48 — state matches residual table. |
| **E14** | OpenSpec tasks.md: every `[x]` has a green job URL or honest residual note; flag overclaims. |
| **E15** (optional) | Local WSL: configure/build headless unit tests for `CrashBreadcrumb` if toolchain present; else BLOCKED. |

---

## 5. Adversarial probes (must attempt)

1. **Empty suppressions + green TSan:** Is TSan still green after #38/#39 removal on `AUDITED_SHA`? If CI not finished, mark residual as **UNPROVEN** and NO-GO for “TSan residuals closed.”
2. **Seed step false green:** Could the seed step pass with `|| true` or `continue-on-error`? Prove it cannot.
3. **SBOM theater:** Could production scan “succeed” with zero packages? Prove component count assertion and generator check prevent it.
4. **llvm.sh / latest binary:** Confirm no `curl | bash` llvm install; osv-scanner not fetched from `releases/latest`.
5. **Task honesty:** Find any checked task whose verification is still false on `AUDITED_SHA`.
6. **#43 honesty:** If SBOM lists fluidsynth version, does it match runtime vendored risk narrative? Flag version theater if pin ≠ vendored tree.
7. **Seqlock soundness:** Concurrent writers to same slot after wrap; torn reads; ABA — is design adequate for TSan’s model?

---

## 6. Scoring rubric

Score each dimension **1–5** with one evidence sentence:

| Dimension | 5 means |
|-----------|---------|
| Security | Scanner pin + digest; no mute; baselines issue-linked; no known silent CVE hide without issue |
| Correctness | All mandatory lanes green on audited SHA; no known test muting |
| Maintainability | Suppressions empty or hygienic; warning disables scoped; generators keep SBOM honest |
| Documentation honesty | Tasks/issues/CI-THESIS match live CI |
| CI/CD integrity | Fail-closed lanes; dep-scan exercised on master; seed proof present |
| Process/governance | Demotion rule intact; issue exits respected; no allow_failure restored |

---

## 7. Finding severity guide

Reuse prior taxonomy:

- **Critical** — RCE / secret leak / CI can merge red without visibility  
- **High** — Mandatory lane red or structurally unable to fail honestly  
- **Medium** — Residual incomplete, docs lie, hygiene gap, supply-chain soft  
- **Low** — Style / over-broad suppress with tracked exit  
- **Informational** — Positive control confirmation  

For each finding include: severity, category, location, evidence (URL or path:line), impact, recommendation, residual risk, status.

Map prior findings **F001–F012** to **Resolved / Partial / Open / Superseded** with SHA evidence.

---

## 8. Required deliverable

Write:

`docs/superpowers/reviews/YYYY-MM-DD-codex-r1-master-closeout-audit.md`

Structure:

1. **Header table** — date, auditor model, `AUDITED_SHA`, CI run URL(s), PR #46 status  
2. **Executive summary** — **PASS/FAIL**, **GO/NO-GO**, 5–8 bullets, finding counts  
3. **Dimension scorecard** (table)  
4. **Scope and method** — tools, runs, what was not done  
5. **Mandatory gate matrix** — each gate PASS/FAIL + job URL  
6. **Residual matrix** — #38–#44 + 4.3  
7. **OpenSpec honesty** — task checkboxes vs evidence  
8. **Findings** — F-new or F001-remap  
9. **E-suite results** — E1–E15  
10. **Verdict** — explicit:

```text
R1 MASTER CLOSEOUT: GO | NO-GO
Mandatory lanes: PASS | FAIL
Residual TSan empty suppressions: PROVEN | UNPROVEN | FAIL
Dependency scan + seed proof: PASS | FAIL | SKIPPED
Overall: ...
```

11. **What would flip NO-GO → GO** (ordered, concrete)

---

## 9. Hard rules

1. **Never** mark GO if any of ASan / UBSan / TSan / Fuzz / Windows is red or missing on the synchronized audited SHA.  
2. **Never** mark residual #38/#39 “closed and proven” if TSan has not completed success on a SHA that contains those commits.  
3. Prefer primary logs over agent chat summaries.  
4. If blocked (no `gh`, no network), say **BLOCKED** and still score static review separately.  
5. Do not “fix” product code in this audit pass unless the user explicitly requests remediation after the report.  
6. Cite URLs as full `https://github.com/CharlesHoskinson/ProjectLegends/...` links.

---

## 10. Quick start commands

```bash
cd /path/to/ProjectLegends
git fetch origin master
export AUDITED_SHA=$(git rev-parse origin/master)
echo "AUDITED_SHA=$AUDITED_SHA"
git log -15 --oneline origin/master

gh run list --branch master --workflow CI --limit 8 \
  --json databaseId,headSha,conclusion,status,url,createdAt

# Replace RUN with the matching completed run id
RUN=<id>
gh api "repos/CharlesHoskinson/ProjectLegends/actions/runs/${RUN}/jobs" \
  --jq '.jobs[] | {name, conclusion, html_url}'

# Suppressions
rg -n "^(race|deadlock|mutex|thread):" tsan-suppressions.txt || true

# SBOM honesty
python3 scripts/generate_vendored_sbom.py --check

# Issues
for n in 38 39 40 42 43 44 45 47 48; do
  gh issue view $n --json number,state,title --jq '"#\(.number) [\(.state)] \(.title)"'
done
```

---

## 11. Context the agent may try to sell you (distrust until proven)

- “Mandatory lanes green on `98450e6`” — true for that SHA; **re-prove on `AUDITED_SHA`**.  
- “TSan suppressions empty and still green” — only true after CI succeeds post-seqlock.  
- “Dependency scan on master” — only true if job not skipped and seed step behaves.  
- “R1 fully closed” — false if #40/#42/#43/#44 remain and any mandatory lane is red.  

---

**End of brief.** Produce the review file only; default to **NO-GO** when evidence is incomplete.
