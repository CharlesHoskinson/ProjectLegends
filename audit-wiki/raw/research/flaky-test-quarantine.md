# Research notes: Flaky-Test Detection & Quarantine

Topic: detecting flaky tests without historical rerun data, quarantine workflows, ownership and exit criteria, in a C++23/GoogleTest/CTest/GitHub Actions context.
All sources fetched 2026-06-10 via scrapling (Fetcher.get, stealthy headers). All returned HTTP 200.

---

## Source 1 — Google Testing Blog: Flaky Tests at Google and How We Mitigate Them (John Micco, 2016)

- URL: https://testing.googleblog.com/2016/05/flaky-tests-at-google-and-how-we.html
- Retrieved: 2026-06-10

Relevant passages:

> "We define a 'flaky' test result as a test that exhibits both a passing and a failing result with the same code."

> "across our entire corpus of tests, we see a continual rate of about 1.5% of all test runs reporting a 'flaky' result ... Almost 16% of our tests have some level of flakiness associated with them!"

> "What we find in practice is that about 84% of the transitions we observe from pass to fail involve a flaky test!"

On retry-based mitigation and its cost:

> "We have several mitigation strategies for flaky tests during presubmit testing, including the ability to re-run only failing tests, and an option to re-run tests automatically when they fail. We even have a way to denote a test as flaky - causing it to report a failure only if it fails 3 times in a row. This reduces false positives, but encourages developers to ignore flakiness in their own tests unless their tests start failing 3 times in a row, which is hardly a perfect solution."

> "Imagine a 15 minute integration test marked as flaky that is broken by my code submission. The breakage will not be discovered until 3 executions of the test complete, or 45 minutes, after which it will need to be determined if the test is broken (and needs to be fixed) or if the test just flaked three times in a row."

The quarantine mechanism, with its bug-filing and its risk:

> "A tool that monitors the flakiness of tests and if the flakiness is too high, it automatically quarantines the test. Quarantining removes the test from the critical path and files a bug for developers to reduce the flakiness. This prevents it from becoming a problem for developers, but could easily mask a real race condition or some other bug in the code being tested."

From Micco's comment replies (same page):

> "From the testing system point of view a test that fails reliably is far better than a test that is flaky! A persistently failing test is giving a clear signal about what to do - even it means fixing the test."

Commenter (Wayne Roseberry, Microsoft) on consistency-rate gating, quoted as practitioner corroboration:

> "we execute reliability runs of all of the CI tests (we try for hundreds of executions ...) per build to generate consistency rates. Using those numbers, we push product teams to move all tests that fall below a certain consistency level out of the CI tests. We keep them in the reliability suite for sake of coverage and issue discovery, but do not use them to gate submission into the main code branch."

---

## Source 2 — Google Testing Blog: Where do our flaky tests come from? (Jeff Listfield, 2017)

- URL: https://testing.googleblog.com/2017/04/where-do-our-flaky-tests-come-from.html
- Retrieved: 2026-06-10

Relevant passages:

> "Flaky tests are tests that exhibit both a passing and a failing result with the same code. Given this, a test failure may or may not mean that there's a new problem. And trying to recreate the failure, by rerunning the test with the same version of code, may or may not result in a passing test. We start viewing these tests as unreliable and eventually they lose their value. If the root cause is nondeterminism in the production code, ignoring the test means ignoring a production bug."

> "Google has around 4.2 million tests that run on our continuous integration system. Of these, around 63 thousand have a flaky run over the course of a week."

Size predicts flakiness:

> "Overwhelmingly, the larger the test (as measured by binary size, RAM use, or number of libraries built), the more likely it is to be flaky."

> "Over the course of a week, 0.5% of our small tests were flaky, 1.6% of our medium tests were flaky, and 14% of our large tests were flaky."

> Correlation r² with flakiness: binary size 0.82, RAM used 0.76.

Tool choice (WebDriver, Android emulator) correlates with flakiness, but: "correlation is not causation ... Size is more predictive than tool."

---

## Source 3 — Slack Engineering: Handling Flaky Tests at Scale: Auto Detection & Suppression (Arpita Patel, 2022)

- URL: https://slack.engineering/handling-flaky-tests-at-scale-auto-detection-suppression/
- Retrieved: 2026-06-10

Definitions:

> "A failing test is a test that fails consistently across multiple reruns. A flaky test is a test that eventually passes across reruns if the test reruns multiple times."

Scale of the problem before automation: main branch pass rate ~20%; "57% failed due to test job failures consisting of flaky and failing automated tests". Manual triage cost: "each test failure takes about 28 minutes to manually triage." After automation: "we were able to drop test job failures from 57% to less than 5%."

First approach (suppress *results* by flakiness threshold against last-N history) was rolled back. Drawbacks:

> "Failing tests were leaking into the main branch." (a brand-new broken test had no history, was classified flaky, filtered from results)

> "Simply filtering out flaky test results is not the best approach as we are just hiding test failures from impacting the overall main build stability. This approach makes flaky test investigation difficult since there is not enough information on when the test state changed."

> "Instead of handling test failure detection and suppression at both the PR and the main branch level, it is better to suppress tests only on the main branch."

Second approach (suppress *execution*):

> "we decided to go with suppressing execution of flaky tests instead of suppressing results of flaky tests. A single failure will result in the test being disabled (regardless of reruns) and each feature team will need to assign resources to investigate the true nature of test failure to fix it accordingly."

Pipeline parts: "Test Detection: Identify the test failure and differentiate between flaky tests and failing tests. Test Suppression: Create a Jira ticket, open a PR to suppress the test, auto-approve the PR, and then merge the PR. Slack Notifications: Notify the DevXp team when a PR is created and merged."

Requirements list includes: "Should not suppress backend/API failures, test crashes, or infra failures"; "Create test ownership mapping to map tests to respective feature teams"; "Assign a Jira ticket to the team that owns the test"; "Attach test result failure details to the Jira ticket for ease of investigation"; "Send weekly alerts to each team's channel to communicate a summary of suppressed tests."

Suppression is implemented as a source edit that renames the test and embeds the ticket: iOS example output `// https://jira.com/PROJ-123` + `func disabled_testShouldShowInvite()`; Android via `@Ignore('https://jira.com/PROJ-123')`.

Exit criteria / re-enable loop (phase 3):

> "Rerun suppressed tests regularly in quarantine to ensure that it doesn't affect the main branch builds. If they are no longer flaky then they can automatically be re-enabled and merged to the main branch."

Results: main branch stability 19.82% -> 96%; test job failure 56.76% -> 3.85%; 553 hours of triage time saved. Counter-signal from developers: "developers are having a bit of a hard time re-enabling tests since a test failure can be out of date, difficult to reproduce, or the feature has evolved."

---

## Source 4 — Spotify Engineering: Test Flakiness — Methods for identifying and dealing with flaky tests (Jason Palmer, 2019)

- URL: https://engineering.atspotify.com/2019/11/test-flakiness-methods-for-identifying-and-dealing-with-flaky-tests
- Retrieved: 2026-06-10

> "A flaky test is a test that both passes and fails periodically without any code changes. ... But the real cost of test flakiness is a lack of confidence in your tests. ... If you don't have confidence in your tests then you are in no better position than a team that has zero tests."

Causes highlighted: inconsistent assertion timing ("You should have predicates in place to poll the application state until it reaches a known good state where you can assert" — not wait statements), reliance on test order ("global state is the main culprit ... The solution is to entirely reset the state between each test run"), end-to-end tests ("end to end tests are flaky by nature. Write fewer of them. Instead of having 500 end to end tests for your organization, have 5.").

Visualization for separating flakiness from infrastructure failure (Odeneye):

> "If you see a scattering of orange dots this usually means test flakiness. If you see a solid column of failures this usually represents infrastructure problems such as network failures."

Visibility alone moves the metric:

> "By making this table available and doing nothing else this reduced test flakiness at Spotify from 6% to 4% in two months."

Verifying a fix (Flakybot): "an internal tool at Spotify to help engineers determine if their test(s) are flaky before merging code to master. An engineer can invoke Flakybot at any time in a pull request, and their tests will be exercised quickly and show a report. This gives a high level of confidence that flakiness problems have been fixed."

---

## Source 5 — GitHub Blog: Reducing flaky builds by 18x (Jordan Raine, 2020)

- URL: https://github.blog/engineering/engineering-principles/reducing-flaky-builds-by-18x/
- Retrieved: 2026-06-10

Outcome: "1 in 11 commits had at least one red build caused by a flaky test, or about 9 percent of commits ... after introducing a system to manage flaky tests, the percentage of commits with flaky builds dropped to less than half a percent, or 1 in 200 commits."

Philosophy:

> "our intent wasn't to fix every flaky test or to stop developers from introducing new flaky tests. Such goals, if not impossible, seemed impractical. ... Rather, we set out to manage the inevitability of flaky tests."

Skewed distribution justifies triage by impact:

> "about a quarter of our tests had failed flaky across three or more branches in the past two years. But ... most flaky tests failed fewer than ten times and only 0.4 percent of flaky tests failed 100 times or more. This made one thing clear: not every flaky failure should be investigated."

Two baseline detection approaches (since 2016):

> "Same code, different results. Once a build finishes, CI checks for other builds run against the same code using the root git tree hash. If another build had different results ... the test failure was marked as flaky. While this approach was accurate, it only worked if a build was retried."

> "Retry tests that fail. When a test failed, it was retried again later within the same build. This could be used on every build at minimal cost. If the test passed when rerun, it was marked as flaky. However, certain types of flaky tests couldn't be detected with this approach, such as a time-based flaky test."

> "Unfortunately, these approaches were only able to identify 25 percent of the flaky failures."

Improved three-scenario retry:

> "Retry in the same process. ... If the test passes under the same conditions, it is likely caused by randomness in the code or a race condition. Retry in the same process, shifted into the future. ... Retry on a different host. ... If the test passes under these conditions but fails in the other two retries, it is likely caused by test order-dependence or some other shared state. Using this approach, we are able to automatically identify 90 percent of flaky failures."

Containment: "After ensuring the test passes when run against the same code, it keeps the build green."

Impact scoring and ownership:

> "a flaky test is given an impact score based on how many times it has failed as well as how many branches, developers, and deploys were affected by it. ... Once the score exceeds a certain threshold, an issue is automatically opened and assigned to the people who most recently modified either the test files or associated code prior to the test becoming flaky."

> "the only person bothered by a flaky test is the person who wrote it."

---

## Source 6 — ctest(1) manual, CMake latest (Kitware)

- URL: https://cmake.org/cmake/help/latest/manual/ctest.1.html
- Retrieved: 2026-06-10

`--rerun-failed`:

> "Run only the tests that failed previously. This option tells CTest to perform only the tests that failed during its previous run."

`--repeat <mode>:<n>`:

> "Run tests repeatedly based on the given <mode> up to <n> times. The modes are:
> until-fail — Require each test to run <n> times without failing in order to pass. This is useful in finding sporadic failures in test cases.
> until-pass — Allow each test to run up to <n> times in order to pass. Repeats tests if they fail for any reason. This is useful in tolerating sporadic failures in test cases.
> after-timeout — Allow each test to run up to <n> times in order to pass. Repeats tests only if they timeout. This is useful in tolerating sporadic timeouts in test cases on busy machines."

> "--repeat-until-fail <n> — Equivalent to --repeat until-fail:<n>."

(Label selection `-L <regex>` / `-LE <regex>` documented in the same manual; tests carry LABELS properties set at add-time.)

---

## Source 7 — GoogleTest Advanced Topics (google/googletest docs/advanced.md, main branch)

- URL: https://raw.githubusercontent.com/google/googletest/main/docs/advanced.md (rendered at https://google.github.io/googletest/advanced.html)
- Retrieved: 2026-06-10

Temporarily Disabling Tests:

> "If you have a broken test that you cannot fix right away, you can add the DISABLED_ prefix to its name. This will exclude it from execution. This is better than commenting out the code or using #if 0, as disabled tests are still compiled (and thus won't rot)."

> "NOTE: This feature should only be used for temporary pain-relief. You still have to fix the disabled tests at a later date. As a reminder, GoogleTest will print a banner warning you if a test program contains any disabled tests."

> "TIP: You can easily count the number of disabled tests you have using grep. This number can be used as a metric for improving your test quality."

Running quarantined tests anyway:

> "To include disabled tests in test execution, just invoke the test program with the --gtest_also_run_disabled_tests flag or set the GTEST_ALSO_RUN_DISABLED_TESTS environment variable to a value other than 0. You can combine this with the --gtest_filter flag to further select which disabled tests to run."

Repeating:

> "The --gtest_repeat flag allows you to repeat all (or selected) test methods in a program many times. Hopefully, a flaky test will eventually fail and give you a chance to debug."

> "$ foo_test --gtest_repeat=1000 --gtest_break_on_failure — Repeat foo_test 1000 times, stopping at the first failure. This is especially useful when running under a debugger ..."

> "$ foo_test --gtest_repeat=1000 --gtest_filter=FooBar.* — Repeat the tests whose name matches the filter 1000 times."

> "If your test program contains global set-up/tear-down code, it will be repeated in each iteration as well, as the flakiness may be in it."

Shuffling (order-dependence detection):

> "You can specify the --gtest_shuffle flag (or set the GTEST_SHUFFLE environment variable to 1) to run the tests in a program in a random order. This helps to reveal bad dependencies between tests. ... The console output includes the random seed value, such that you can reproduce an order-related test failure later. To specify the random seed explicitly, use the --gtest_random_seed=SEED flag ... If you combine this with --gtest_repeat=N, GoogleTest will pick a different random seed and re-shuffle the tests in each iteration."

---

## Source 8 — Understanding and Detecting Flaky Builds in GitHub Actions (Ge & Zhang, Soochow University, arXiv 2026)

- URL: https://arxiv.org/html/2602.02307v1
- Retrieved: 2026-06-10

Large-scale empirical study of GitHub Actions rerun data: 1,960 open-source Java projects, 4.86M builds, 15.4M jobs.

Rerun identification from build metadata:

> "GitHub Actions records rerun information directly in the build metadata. In each build-level JSON file, the field run_attempt specifies the attempt number of the build. ... We treat all builds with a run_attempt value greater than 1 as rerun builds. For each rerun build, we collected all metadata and log files associated with every attempt to reconstruct the complete rerun sequence. A job is classified as a flaky job if it exhibits both success and failure across its attempts."

Headline numbers:

> "Of the 4,879,460 builds, 155,488 (3.2%) were rerun." (Of single-rerun builds, 102,878 were artifacts of the first-time-contributor approval mechanism and were excluded.)

> "Of the 52,610 rerun builds, 35,634 (67.73%) exhibited flaky behavior (i.e., flaky builds), affecting 1,005 (51.28%) of the 1,960 projects."

> "flaky tests constitute the most frequent failure category, accounting for 64.99% of flaky failures" (15 categories total; network issues and dependency resolution next most prevalent).

Reruns are an unreliable and expensive detector:

> "10,406 flaky builds required more than one rerun before exhibiting an outcome change, and ... extreme cases required up to 20 reruns."

> "rerunning builds is not always an effective or efficient strategy. In many cases, flaky behavior does not manifest through reruns or requires multiple reruns. Furthermore, rerun builds incur substantial waiting and computational times" (aggregate: ~339 years waiting time, ~31.6 years compute; rerun builds averaged 63x the waiting time of non-rerun builds).

Data-retention constraint relevant to any retrospective analysis:

> "GitHub Actions retains a project's build history for only three months by default."

---

## Sources considered and dropped

- Luo et al., "An Empirical Analysis of Flaky Tests" (FSE 2014) — canonical root-cause taxonomy (async wait, concurrency, test order dependency as top three) but available only as PDF; not fetched via the text pipeline. Its findings reach this file second-hand through Source 8's citations and Source 5's cause categories (chance/time/order), which agree.
