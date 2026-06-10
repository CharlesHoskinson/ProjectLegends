# Research notes: Test Impact Analysis & Selection

Retrieved 2026-06-10 via scrapling (Fetcher.get, stealthy headers). Raw passages only; synthesis lives at `wiki/sources/Test Impact Analysis & Selection (2026-06).md`.

---

## Source 1 — Microsoft Learn: "Speed up testing by using Test Impact Analysis (TIA)"

- URL: https://learn.microsoft.com/en-us/azure/devops/pipelines/test/test-impact-analysis?view=azure-devops
- Retrieved: 2026-06-10 (HTTP 200; page last updated 2025-10-27)
- Publisher: Microsoft (Azure DevOps documentation)

Relevant passages:

> "as the code base grows and matures, its regression test suite tends to grow as well - to the extent that running a full regression test might require hours. This testing slows down the frequency of integrations, and ultimately defeats the purpose of continuous integration."

> "TIA performs incremental validation by automatic test selection. It automatically selects only the subset of tests required to validate the code being committed."

> "Test Impact Analysis has: **A robust test selection mechanism**. It includes existing impacted tests, previously failing tests, and newly added tests. **Safe fallback**. For commits and scenarios that TIA can't understand, it falls back to running all tests. TIA is currently scoped to only managed code, and single machine topology. So, for example, if the code commit contains changes to HTML or CSS files, it can't reason about them and falls back to running all tests. **Configurable overrides**. You can run all tests at a configured periodicity."

> "TIA is **not** supported for the following scenarios: Multi-machine topology (where the test is exercising an app deployed to a different machine); Data driven tests; Test Adapter-specific parallel test execution; .NET Core; UWP"

> "Through the VSTest task UI. TIA can be conditioned to run all tests at a configured periodicity. Setting this option is recommended, and is the means to regulate test selection."

> "you can disable it for a specific build by setting the variable `DisableTestImpactAnalysis` to `true`. This override forces TIA to run all tests for that build."

> "When TIA opens a commit and sees an unknown file type, it falls back to running all tests. While this action is good from a safety perspective, tuning this behavior might be useful in some cases. For example: Set the `TIA_IncludePathFilters` variable to specific paths to include only these paths in a repository for which you want TIA to apply. … Set the `TIA_IncludePathFilters` variable to specify file types that don't influence the outcome of tests and for which changes should be ignored. For example, to ignore changes to .csproj files set the variable to the value: `!\*\*\\\*.csproj`."

> "To evaluate whether TIA is selecting the appropriate tests: Manually validate the selection. … Run TIA selected tests and then all tests in sequence. In a build pipeline, use two test tasks - one that runs only impacted Tests (T1) and one that runs all tests (T2). If T1 passes, check that T2 passes as well. If there was a failing test in T1, check that T2 reports the same set of failures."

> "TIA uses dependency maps of the following form. `TestMethod1 / dependency1 / dependency2 …` TIA can generate a dependency map for managed code execution. Where such dependencies reside in .cs and .vb files, TIA can automatically watch for commits into such files and then run tests that had these source files in their list of dependencies. You can extend the scope of TIA by explicitly providing the dependencies map as an XML file. For example, you might want to support code in other languages such as JavaScript or C++, or support the scenario where tests and product code are running on different machines. The mapping can even be approximate, and the set of tests you want to run can be specified in terms of a test case filter"

> ".runsettings sample: `<ImpactLevel>file</ImpactLevel>` — file level data collection" (TIA tracks dynamic dependencies at file granularity)

Caveats noted in the doc: with VS2015, TIA forces serial test execution and disables code-coverage collection.

---

## Source 2 — Meta Engineering: "Predictive test selection: A more efficient way to ensure reliability of code changes"

- URL: https://engineering.fb.com/2018/11/21/developer-tools/predictive-test-selection/
- Retrieved: 2026-06-10 (HTTP 200; posted 2018-11-21; authors Machalica, Samylkin, Porth, Chandra; companion paper arXiv:1810.05286, published at ICSE-SEIP 2019)

Relevant passages:

> "This predictive test selection system has been deployed at Facebook for more than a year, enabling us to catch more than 99.9 percent of all regressions before they are visible to other engineers in the trunk code, while running just a third of all tests that transitively depend on modified code."

On build-dependency-based selection (the conventional baseline):

> "A common approach to regression testing is to use information extracted from build metadata to determine which tests to run on a particular code change. By analyzing build dependencies between units of code, one can determine all tests that transitively depend on sources modified in that code change."

> "This approach has a significant shortcoming: It ends up saying 'yes, this test is impacted' more often than is actually necessary. On average, it would cause as many as a quarter of all available tests to be exercised for each change made to our mobile codebase. … in our monolithic codebase, end products depend on many reusable components, which use a small set of low-level libraries. In practice, many transitive dependencies are not, in fact, relevant for regression testing. For example, when there is a change to one of our low-level libraries, it would be inefficient to rerun all tests on every project that uses that library."

> "The research community has developed other approaches to regression test selection, such as those based on static change-impact analysis. These techniques, however, are impractical in our use case because of the size of our codebase and the number of different programming languages in use."

On the predictive model:

> "we created a predictive model that estimates the probability of each test failing for a newly proposed code change. … we built it by using a large data set containing results of tests on historical code changes and then applying standard machine learning techniques. … the system uses a variant of a standard machine learning algorithm — a gradient-boosted decision-tree model."

> "In production, we require our model to predict more than 95 percent of test outcomes correctly and to catch at least one failing test for more than 99.9 percent of problematic changes."

> "Because of the constantly evolving structure of the codebase, our test selection strategy must adapt to continue to satisfy these strict correctness requirements. This becomes straightforward with our system, however, because we can regularly retrain the model using test results from recently submitted code changes."

On flakiness:

> "the system needs to address the problem of test flakiness, where test outcomes change from pass to fail when the code under test hasn't actually changed. … if we train a model without identifying flaky test failures, the model may not learn to predict test outcomes consistently. … To mitigate the impact of flakiness on the learned test selection model, we aggressively retry failed tests when collecting training data. This approach allows us to distinguish tests that failed consistently (indicating a true regression) from those that exhibited flaky, nonreproducible failures."

---

## Source 3 — Google Research: "Taming Google-Scale Continuous Testing" (Memon, Gao, Nguyen, Dhanda, Nickell, Siemborski, Micco; ICSE-SEIP 2017)

- URL: https://research.google/pubs/taming-google-scale-continuous-testing/
- Retrieved: 2026-06-10 (HTTP 200; abstract page; full paper at https://research.google.com/pubs/archive/45861.pdf, DOI 10.1109/ICSE-SEIP.2017.16)

Abstract (full, from the publication page):

> "Growth in Google's code size and feature churn rate has seen increased reliance on continuous integration (CI) and testing to maintain quality. Even with enormous resources dedicated to testing, we are unable to regression test each code change individually, resulting in increased lag time between code check-ins and test result feedback to developers. We report results of a project that aims to reduce this time by: (1) controlling test workload without compromising quality, and (2) distilling test results data to inform developers, while they write code, of the impact of their latest changes on quality. We model, empirically understand, and leverage the correlations that exist between our code, test cases, developers, programming languages, and code-change and test-execution frequencies, to improve our CI and development processes. Our findings show: very few of our tests ever fail, but those that do are generally 'closer' to the code they test; certain frequently modified code and certain users/tools cause more breakages; and code recently modified by multiple developers (more than 3) breaks more often."

(The findings sentence is the empirical basis for risk-based selection: dependency distance, change frequency, and number of recent authors are failure predictors.)

---

## Source 4 — Google Testing Blog: "Flaky Tests at Google and How We Mitigate Them" (John Micco)

- URL: https://testing.googleblog.com/2016/05/flaky-tests-at-google-and-how-we.html
- Retrieved: 2026-06-10 (HTTP 200; posted 2016-05-27)

Relevant passages:

> "across our entire corpus of tests, we see a continual rate of about 1.5% of all test runs reporting a 'flaky' result. We define a 'flaky' test result as a test that exhibits both a passing and a failing result with the same code."

> "Almost 16% of our tests have some level of flakiness associated with them!"

> "When doing post-submit testing, our Continuous Integration (CI) system identifies when a passing test transitions to failing, so that we can investigate the code submission that caused the failure. What we find in practice is that about 84% of the transitions we observe from pass to fail involve a flaky test! This causes extra repetitive work to determine whether a new failure is a flaky result or a legitimate failure. It is quite common to ignore legitimate failures in flaky tests due to the high number of false-positives."

> "We have several mitigation strategies for flaky tests during presubmit testing, including the ability to re-run only failing tests, and an option to re-run tests automatically when they fail. We even have a way to denote a test as flaky - causing it to report a failure only if it fails 3 times in a row. This reduces false positives, but encourages developers to ignore flakiness in their own tests"

> "A tool that monitors the flakiness of tests and if the flakiness is too high, it automatically quarantines the test. Quarantining removes the test from the critical path and files a bug for developers to reduce the flakiness. This prevents it from becoming a problem for developers, but could easily mask a real race condition or some other bug in the code being tested."

---

## Source 5 — CMake/CTest manual (ctest(1), CMake 4.x documentation)

- URL: https://cmake.org/cmake/help/latest/manual/ctest.1.html
- Retrieved: 2026-06-10 (HTTP 200)

Relevant passages (test-selection options):

> "`-L <regex>, --label-regex <regex>` — Run tests with labels matching regular expression … This option tells CTest to run only the tests whose labels match the given regular expression. When more than one `-L` option is given, a test will only be run if each regular expression matches at least one of the test's labels (i.e. the multiple `-L` labels form an AND relationship)."

> "`-LE <regex>, --label-exclude <regex>` — Exclude tests with labels matching regular expression."

> "`-R <regex>, --tests-regex <regex>` — Run tests matching regular expression. … `-E <regex>, --exclude-regex <regex>` — Exclude tests matching regular expression."

> "`--tests-from-file <filename>` — Added in version 3.29. Run tests listed in the given file. … The file must contain one exact test name per line. Lines that do not exactly match any test names are ignored. This option can be combined with the other options like `-R`, `-E`, `-L` or `-LE`." (Symmetric `--exclude-from-file` also added in 3.29.)

> "`-FA <regex>, --fixture-exclude-any <regex>` — Exclude fixtures matching `<regex>` from automatically adding any tests to the test set. If a test in the set of tests to be executed requires a particular fixture, that fixture's setup and cleanup tests would normally be added to the test set automatically. This option prevents adding setup or cleanup tests for fixtures matching the `<regex>`."

(I.e., the default fixture behavior is the important one: when CTest runs a *subset* of tests, FIXTURES_SETUP/FIXTURES_CLEANUP tests for required fixtures are added automatically, so label- or name-based subsets stay self-consistent.)

> "`--print-labels` — Print all available test labels."

Label-matching semantics section:

> "Tests may have labels attached to them. Tests may be included or excluded from a test run by filtering on the labels. Each individual filter is a regular expression applied to the labels attached to a test. … If a test has no labels attached to it, then `-L` will never include that test, and `-LE` will never exclude that test."

> "Because the matching works with regular expressions, take note that running CTest with `-L es` will match all five tests." (Labels match by regex substring; anchor label regexes to avoid accidental over-selection.)

---

## Source 6 — bazel-contrib/target-determinator README

- URL: https://github.com/bazel-contrib/target-determinator (fetched as https://raw.githubusercontent.com/bazel-contrib/target-determinator/main/README.md)
- Retrieved: 2026-06-10 (HTTP 200)

Relevant passages:

> "Target determinator is a binary (and Go API) used to determine which Bazel targets changed between two git commits. … This binary lists targets to stdout, one-per-line, which were affected between `<before>` and the currently checked-out revision."

> "`driver` is a binary which implements a simple CI pipeline; it runs the same logic as `target-determinator`, then tests all identified targets." (Flag `-manual-test-mode` — "How to handle affected tests tagged manual. Possible values: run|skip (default 'skip')".)

> "`-before-query-error-behavior` — How to behave if the 'before' revision query fails. Accepted values: fatal, ignore-and-build-all (default 'ignore-and-build-all')." (Default failure mode is fall back to building/testing everything, not skipping.)

> "`-ignore-file value` — Files to ignore for git operations, relative to the working-directory. These files shan't affect the Bazel graph."

> "Target Determinator caches the results of Bazel cquery invocations across runs. On a cache hit, the expensive cquery and hashing work for a given commit is skipped entirely. The cache key is derived from: the target-determinator binary itself (SHA-256 hash); the Bazel version; the git tree SHA of the queried commit; the target pattern; CLI options that may affect cquery results …"

> "*Not* included in the cache key: User and system bazelrc files …; The host machine (hardware, OS). … Environment variables, whether they are used by Bazel or not."

> "With caching, however, the 'before' result may have been computed in an earlier pipeline run, under the environment variables that were in effect *at that time*. If an environment variable affected Bazel's query output (e.g. because it is referenced by `--workspace_status`, `--action_env`, `--test_env`, or a repo rule), the cached result reflects the old environment, while the 'after' result reflects the new one. The two results are then compared under different conditions, which may produce spurious differences."

---

## Source 7 — Gligoric, Eloussi, Marinov: "Practical Regression Test Selection with Dynamic File Dependencies" (Ekstazi), ISSTA 2015

- URL: https://users.ece.utexas.edu/~gligoric/papers/GligoricETAL15Ekstazi.pdf
- Retrieved: 2026-06-10 (HTTP 200, PDF; DOI 10.1145/2771783.2771784)

Relevant passages:

> "A traditional RTS technique takes four inputs—two software revisions (new and old), test suite at the new revision, and dependency information from the test runs on the old revision—and produces, as output, a subset of the test suite for the new revision. The subset includes the tests that can be affected by the changes … RTS is safe if it guarantees that the subset of selected tests includes all tests whose behavior may be affected by the changes."

> "Google observed that their regression-testing system, TAP, has had a linear increase in both the number of software changes and the average test-suite execution time, leading to a quadratic increase in the total test-suite-execution time."

> "While RTS was proposed over three decades ago, it has not been widely adopted in practice, except for the substantial success of the Google TAP system. Unfortunately, TAP performs RTS only across projects (e.g., YouTube depends on the Guava project, so all YouTube tests are run if anything in Guava changes) and provides no benefit *within a project*."

> "Ekstazi computes for each test entity (a test method or a test class) what files it depends on; the files can be either executable code (e.g., .class files in Java) or external resources (e.g., configuration files). A test need not be run in the new revision if none of its dependent files changed. While we provide no formal proof that Ekstazi is safe, its safety follows directly from the proven safety for RTS based on class dependencies and partial builds based on file dependencies."

> "We refer to the granularity of test entities as *selection granularity* — this is the level at which tests are tracked and selected … and we refer to the granularity of dependent elements as *dependency granularity* — this is the level at which changes are determined."

> "At a glance, it seems that Ekstazi cannot be better than the traditional techniques, because Ekstazi never selects fewer tests. However, our goal is to optimize the *end-to-end* time for RTS. Although Ekstazi selects some more tests and thus has a longer execution phase, its use of much coarser dependencies shortens both the analysis and collection. As a result, Ekstazi has a much lower end-to-end time."

> "Safely using methods as the dependency granularity is expensive. An RTS technique that just intersects methods that are in the set of dependencies with the changes … is unsafe, i.e., it could fail to select some test that is affected by the changes. For example, the new revision could add a method m in class D (that overrides C.m); a naive intersection would not select any test, but the outcome of t2 could change: the execution of this test on the old revision does depend on the existence (or absence) of D.m, although the test could not execute that (non-existent) method."

> "when tests depend not only on the code under test but also on external files, collecting only the classes is not safe, and hence Ekstazi uses files as dependencies."

> "A typical RTS technique has three phases: the analysis (A) phase selects what tests to run in the current revision, the execution (E) phase runs the selected tests, and the collection (C) phase collects information for the next revision. Ekstazi collects dependencies at the level of files. For each test entity, Ekstazi saves … the names and checksums of the files that the entity uses during execution." (Checksums are "smart": e.g., debug info is ignored when comparing .class files.)

> Evaluation: "615 revisions of 32 open-source projects (totaling almost 5M LOC) … Ekstazi reduced the end-to-end testing time 32% on average, and 54% for longer-running test suites, compared to executing all tests. Ekstazi also has lower end-to-end time than the existing techniques, despite the fact that it selects more tests."

---

## Sources considered and dropped

- Elbaum, Rothermel, Penix, "Techniques for Improving Regression Testing in Continuous Integration Development Environments" (FSE 2014, DOI 10.1145/2635868.2635910) — paywalled at dl.acm.org; not fetched, so not cited beyond noting its existence (it introduces time-window-based selection/prioritization for CI when full dependency analysis is too slow).
- Microsoft DevBlogs "Accelerated Continuous Testing with Test Impact Analysis" parts 1–4 — superseded by the consolidated Microsoft Learn page (Source 1), which carries the same mechanism description.
