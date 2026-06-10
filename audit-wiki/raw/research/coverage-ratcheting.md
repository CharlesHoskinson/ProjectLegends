# Research notes: Coverage Policy Ratcheting

Topic: moving a report-only coverage lane to an enforced one without freezing development — ratchets, per-target thresholds, diff/patch coverage.
All sources fetched 2026-06-10 via scrapling (Fetcher.get, stealthy headers). All returned HTTP 200.

---

## Source 1 — Codecov: Status Checks

- URL: https://docs.codecov.com/docs/commit-status
- Retrieved: 2026-06-10

Relevant passages:

> "Status Checks — Useful for blocking Pull Requests that don't meet a particular coverage threshold."

Project status (absolute coverage, with auto-ratchet semantics):

> "The codecov/project status measures overall project coverage and compares it against the base of the pull request or parent commit."

> "target: auto | <number> — Choose a minimum coverage ratio that the commit must meet to be considered a success. auto will use the coverage from the base commit (pull request base or parent commit) coverage to compare against. This is the default. <number> you can specify a target of an exact coverage number such as 75% or 100%."

> "threshold: <number> — Allow the coverage to drop by <number>%, and posting a success status."

Patch status (diff coverage):

> "The codecov/patch status only measures lines adjusted in the pull request or single commit, if the commit is not in a pull request. This status provides an indication on how well the pull request is tested."

Worked example in the docs: a PR adding an untested branch gets `codecov/patch` of 0% even though "the project coverage is 72% ... this patch status will only measure lines added"; adding tests in subsequent commits moves the patch status to 50% then 100%.

Soft-launch / informational mode:

> "informational — Use Codecov in informational mode. Default is false. If true is specified the resulting status will pass no matter what the coverage is or what other settings are specified. Informational mode is great to use if you want to expose codecov information to other developers in your pull request without necessarily gating PRs on that information."

Per-path statuses (project splitting):

> "paths — Similar to flags, an array of paths and/or regular expressions can be provided and the status will report the combined coverage for the files that match the path name / regular expression."

> Example: "you can set project statuses filtering out specific components of the application, and get 3 unique statuses monitoring each component." (example yaml declares `users:` and `products:` statuses with distinct `paths:` lists; another example declares `tests:` with `target: 100%` and `app:` with `paths: "!tests/"`)

Missing-upload behavior (relevant to token-conditional uploads):

> "if_not_found — Settings are 'success' and 'failure' the default is 'success'. failure: the status will fail if there is no report for the head. success: the status will pass if there is no report for the head. Use this on commits / PRs where you won't be uploading coverage but still want codecov status checks to pass."

> "if_ci_failed ... error: Will set the status to success only if the CI is successful"

Changes status (coverage regressions outside the diff):

> "Codecov will detect changes in coverage that are NOT included in the commit/pull diff, and report these changes as a commit status."

---

## Source 2 — Codecov: Components

- URL: https://docs.codecov.com/docs/components
- Retrieved: 2026-06-10

Relevant passages:

> "Components allow you to isolate and categorize coverage data from your project with virtual filters. It is similar to Flags, but there is no direct relationship between Components and the reports you upload. The most important differentiator between Components and Flags is that Components do not have to be supplied at upload time, they are fully defined in the codecov.yml."

> "Components are particularly useful to create custom statuses and get coverage information from parts of your code that are not easily broken up into different uploads, or span multiple flag groups."

> "Currently you can get component information in the PR comment and also have component-based statuses."

Example yaml (single upload, per-module statuses by path):

```yaml
component_management:
  default_rules:
    statuses:
      - type: project
        target: auto
        branches:
          - "!main"
  individual_components:
    - component_id: module_emotions
      name: emotions
      paths:
        - emotions/**
    - component_id: module_core
      name: core
      paths:
        - core/**
      statuses:
        - type: project
          target: auto
        - type: patch
```

Rationale vs flags for a single merged upload:

> "having individual statuses for the emotions or the fruits modules becomes complicated using flags as you would need to supply one upload per flag ... We can achieve the same effect using components by defining path filters we're interested in in our codecov.yaml."

> "Should I Use Flags or Components? If you have a new project, the correct answer is likely Components."

Component statuses accept the same status definitions as flag management ("These statuses are the same as for flag_management / Except they don't accept 'flags'"), i.e. per-component `type: project|patch`, `target`, etc.

---

## Source 3 — diff-cover (Bachmann1234/diff_cover)

- URL: https://github.com/Bachmann1234/diff_cover
- Retrieved: 2026-06-10

Relevant passages:

> "Diff coverage is the percentage of new or modified lines that are covered by tests. This provides a clear and achievable standard for code review: If you touch a line of code, that line should be covered. Code coverage is every developer's responsibility!"

> "The diff-cover command line tool compares an XML coverage report with the output of git diff. It then reports coverage information for lines in the diff."

Input formats — lcov is supported natively (no Cobertura conversion needed):

> "Currently, diff-cover requires that: You are using git for version control. Your test runner generates coverage reports in Cobertura, Clover or JaCoCo XML format, or LCov format." — listing "lcov (C/C++)" among supported generators.

Enforcement:

> "Fail Under — To have diff-cover and diff-quality return a non zero status code if the report quality/coverage percentage is below a certain threshold specify the fail-under parameter: `diff-cover coverage.xml --fail-under=80` ... The above will return a non zero status if the coverage or quality score was below 80%."

Compare-branch / diff-file mechanics (what a PR job needs):

> "By default, diff-cover compares the current branch to origin/main. To specify a different compare branch: `diff-cover coverage.xml --compare-branch=origin/release`"

> "You may provide a file containing the output of git diff to diff-cover instead of using a branch name. ... `diff-cover coverage.xml --diff-file=diff.txt`"

> "When comparing branches, diff-cover and diff-quality use the `...` git diff range notation by default (changes on the current branch since it diverged from the compare branch)."

Path hygiene and exclusions:

> "Explicit exclusion of paths is possible for both diff-cover and diff-quality ... `diff-cover coverage.xml --exclude setup.py`" (fnmatch patterns, multiple values)

C/C++ caveat (multi-line statements):

> "diff-cover relies on the comparison of diff reports and coverage reports, and does not report lines that appear in one and not in the other. While diff reports list all lines that changed, coverage reports usually list code statements. As a result, a change in a multi-line statement may not be analyzed by diff-cover. As a workaround, you can use the argument --expand-coverage-report ... This argument is only available for XML coverage reports."

Also supports `diff-quality --violations=clang` (clang listed among supported quality checkers), TOML config files, `--show-uncovered`, HTML/JSON/Markdown reports.

---

## Source 4 — qntm, "Ratchets in software development"

- URL: https://qntm.org/ratchet
- Retrieved: 2026-06-10
- Published 2021-11-21; experience report from a production codebase.

Relevant passages:

> "What we have is a ratchet, a script which runs at source code linting time and counts all of these 'pattern' instances across the codebase. If the script counts too many instances, it raises an error, explaining why we don't want more of that 'pattern'. If it counts too few, it also raises an error, this time congratulating you and prompting you to lower the expected number."

> "This script is intentionally extremely simple. The expected numbers are hard-coded in the script itself."

> "One important observation is that this technique does nothing to actively encourage the removal of these old 'patterns'. Those remaining 67 or so calls ... have been kind of lingering."

> "Sometimes, due to extenuating circumstances, we have had to manually raise the count again. This is something we try to avoid, though."

> "Meanwhile, an equal number of people said that they already do something almost exactly like this, or applied a similar technique to the domains of code coverage or performance."

Pitfall noted by the author:

> "Another pitfall which I've spotted is that it would be easy to abuse this technique to enforce unnecessarily strict 'standards' on a development team who really ought to be allowed some creative freedom."

Discussion thread (same page) — alternative mechanisms:

> Tim McCormack: "Diff linting is more complex and fragile. We used to use it at work, and switched to amnesty linting: Every existing instance was given a line-end comment saying 'this is OK for now', and after that any unannotated instance was considered a lint failure."

> J: "I've had something similar in a project for a long time but it works by checking the count in the current branch is no greater than the count in the merge target. Less chance for misuse, also for the rare person who really does get to skip CI to break it for everyone else."

> tim: "It's a clever idea, but it depends on people following the rules — which are enforced by the same people, and encoded in the same repository, as the arena where the rules are applied. ... If an automated test failed, he'd disable it, or modify it to allow his crazy code."

---

## Source 5 — lcov/genhtml manual (Debian manpages, lcov 2.x)

- URL: https://manpages.debian.org/unstable/lcov/genhtml.1.en.html
- Retrieved: 2026-06-10

Relevant passages:

Synopsis lists native threshold flags:

> `[--fail-under-branches percentage]` `[--fail-under-lines percentage]`

(The page's full text was truncated at fetch; the option semantics are confirmed in the "Additional considerations" section and the lcovrc equivalents: lcov/genhtml/geninfo "will generate all the normal result files and messages, but will return a non-zero exit code" when the configured line-coverage threshold is not met.)

Custom acceptance criteria (per-file / per-directory gates):

> "If the --criteria-script option is used, genhtml will use the referenced script to determine whether your coverage criteria have been met - and will return a non-zero status and print a message if the criteria are not met."

> criteria-script callback: "($status, $array) = $callback_obj->check_criteria($obj_name, $type, $json); where $obj_name is the source file or directory name ... $array is a reference to a possibly empty list of strings which will be reported by genhtml. The strings are expected to explain why the coverage criteria failed. See example implementations $LCOV_HOME/share/lcov/support-scripts/criteria.pm."

Differential coverage — native lcov diff coverage against a baseline:

> "Differential coverage comparison against baseline coverage data ... The basic concepts of differential coverage and date/owner binning are described in the paper found at https://arxiv.org/abs/2008.07947"

> "To create a differential coverage report, genhtml requires 1. one or more baseline-files specified via --baseline-file, and 2. a patch file in unified format specified using --diff-file."

12-category classification, the two enforcement-relevant ones:

> "UNC — Uncovered New Code (+ => 0): newly added code is not tested."
> "LBC — Lost Baseline Coverage (1 => 0): unchanged code is no longer tested."

(plus UIC/UBC/GBC/GIC/GNC/CBC/EUB/ECB/DUB/DCB; a criteria-script can compute e.g. "(GNC + GIC + CBC) / (GNC + GIC + CBC + UNC + UIC + UBC)" per directory.)

Path-match caveat:

> "Note that all source code files have to be present and readable at the exact file system location they were compiled, and all path references in the input data '.info' and 'diff' files must match exactly (i.e., exact string match)."

---

## Source 6 — Codecov blog: "How to Incorporate Code Coverage for a Legacy Application"

- URL: https://about.codecov.io/blog/how-to-incorporate-code-coverage-for-a-legacy-application/
- Retrieved: 2026-06-10
- John Gramila, 2021-01-29.

Relevant passages:

> "The first step toward testing your legacy application is to find out what's already being tested ... Mapping existing code coverage is the first step to systematizing and expanding a testing regimen."

> "Increasing your code coverage percentage is a great overall goal, but when you're just starting out, it's time prohibitive to test everything. You'll have to discover and prioritize sections of your code where tests will have the highest impact."

> "as you're adding new tests to a legacy codebase, a best practice is to add unit tests for any new code you write."

> "A great spot to add a check for code coverage is during the review process, as code is committed and merged. Codecov's Patch Coverage feature can specify the percentage of code converted by tests required for a successful commit."

> "When adding tests to a legacy application, it's extremely important to verify that your tests can fail. ... This leaves your tests critically untested."

> "Tests that don't get run aren't helping anyone, and if your test suite drifts out of sync with your codebase, you'll often modify behavior, then have to modify a test to make it pass, bitterly twisting the purpose of testing."

---

## Sources considered and dropped

- https://www.dustyburwell.com/2019/05/29/ratchets — overlaps qntm/search summary ("by setting code coverage as a CI and deploy blocking target ... you can then add tests to key locations and incrementally raise your target, such as from 50% to 60%"); not fetched separately, six-source budget spent on primary docs.
- https://github.com/markis/jest-ratchet — JS-only tool; mechanism (auto-bump coverageThreshold on every uptick) noted from search results, cited only in the conflict callout of the synthesis page.
- SonarSource community thread on ratcheting quality gates — forum feature request, not authoritative documentation.
