# Research notes: Continuous Fuzzing in CI

Topic: ClusterFuzzLite vs OSS-Fuzz vs in-repo libFuzzer jobs; corpus management in CI; crash triage flow — applied to a C++23 project with five libFuzzer targets, a regenerated-every-run seed corpus, 30s PR smoke / 60s nightly budgets, and save-state deserialization as the known attack surface.
All sources fetched 2026-06-10 via scrapling (Fetcher.get, stealthy headers). All returned HTTP 200.

---

## Source 1 — ClusterFuzzLite: Step 2, Running ClusterFuzzLite (modes & configuration)

- URL: https://google.github.io/clusterfuzzlite/running-clusterfuzzlite/
- Retrieved: 2026-06-10

Relevant passages:

On the two primary modes:

> "ClusterFuzzLite offers two primary modes of fuzzing: code change fuzzing and batch fuzzing. ClusterFuzzLite also offers two helper modes for running fuzzers that don't actually fuzz but provide useful functionality: prune and coverage."

Code change (PR) fuzzing duration and exit behavior:

> "Code change fuzzing is designed to be fast so that it integrates easily into your development workcycle: It defaults to fuzzing for 10 minutes, though this can be changed. It quits after finding a single crash, even if there are other fuzzers to run."

The corpus relationship between modes, and why code-change fuzzing alone misses pre-existing bugs:

> "running batch fuzzing will develop a corpus that can be used by code change fuzzing. (If no corpus is available from batch fuzzing, code change fuzzing will start from nothing or the provided seed corpus.) Furthermore, when you first use ClusterFuzzLite, code change fuzzing will not report the bugs that already exist in your codebase, while batch fuzzing will."

Batch fuzzing purpose and corpus persistence:

> "In batch fuzzing mode all fuzzers are run for a preset, longer, amount of time. Unlike in code change mode, batch fuzzing will not exit immediately upon discovering a bug. It will keep running other fuzzers until reaching the allotted fuzzing time."

> "By running for a longer amount of time, batch fuzzing serves two important purposes: It can find bugs that are missed or are not reported by code change fuzzing. Note that batch fuzzing reports all crashes, not just 'new' ones. It builds a corpus for each of your fuzz targets, leading to more code coverage and better bug discovery. This corpus will be used by Code coverage report generation, code change fuzzing, and later runs of batch fuzzing. The corpus is saved using your CI system's feature for storing files."

Corpus pruning:

> "Over time, redundant testcases will get introduced into your fuzzer's corpuses during batch fuzzing. Corpus pruning is a helper function that minimizes the corpuses by removing corpus files (testcases) that do not increase the fuzzer's code coverage."

> "Corpus pruning should be considered mandatory when you are using batch fuzzing but otherwise should not be used."

Coverage mode drives target selection on PRs:

> "The data from coverage reports is also used by code change fuzzing to determine which fuzzers are affected by a code change. If code change fuzzing can determine which fuzzers are affected, it will run only those fuzzers. Otherwise, it will run all of them."

Continuous builds = the regression-vs-new-bug baseline:

> "The continuous builds task enables code change fuzzing to identify whether the cause of a crash was introduced by the code change. With the continuous builds task, if the cause of the crash was pre-existing, the crash is not reported by code change fuzzing. If code change fuzzing is run without the continuous builds task, all crashes will be reported."

Configuration options:

> "fuzz-seconds: Instructs ClusterFuzzLite on how long to spend fuzzing, in seconds. The default is 600 seconds, which is an appropriate starting point for code change fuzzing. You should increase this number to spend more time batch fuzzing."

> "minimize-crashes: If true, reportable crashes will be minimized. The default value is false. Minimizing crashes reduces fuzzing time in batch fuzzing."

> "report-unreproducible-crashes: Whether to report unreproducible crashes. The default value is false. ClusterFuzzLite will always attempt to reproduce new crashes."

> "parallel-fuzzing: Whether to use all available CPU cores for fuzzing. The default value is false ... When set to true, ClusterFuzzLite runs multiple fuzzer processes in parallel with a shared corpus directory."

Sanitizer support (from the same docs set, landing page https://google.github.io/clusterfuzzlite/): "libFuzzer for coverage-guided testing, AddressSanitizer for finding memory safety issues, MemorySanitizer for finding use of uninitialized memory, UndefinedBehaviorSanitizer"; supported CI systems "GitHub Actions, GitLab, Google Cloud Build, Prow"; supported languages include C and C++.

---

## Source 2 — ClusterFuzzLite: GitHub Actions subguide

- URL: https://google.github.io/clusterfuzzlite/running-clusterfuzzlite/github-actions/
- Retrieved: 2026-06-10

Relevant passages:

Workflow layout — four files, one per mode:

> "For basic ClusterFuzzLite functionality, all you need is a single workflow file to enable fuzzing on your pull requests. `.github/workflows/cflite_pr.yml` (for PR fuzzing). To enable more features, we recommend having these additional files: `.github/workflows/cflite_build.yml` (for continuous builds), `.github/workflows/cflite_batch.yml` (for batch fuzzing), `.github/workflows/cflite_cron.yml` (for tasks done on a cron schedule: pruning and coverage)"

PR fuzzing default config uses `fuzz-seconds: 600`, `mode: 'code-change'`, `output-sarif: true`, with a sanitizer matrix defaulting to `address` and commented-out `undefined` / `memory` entries.

Batch fuzzing default: cron `'0 0/6 * * *'` ("Every 6th hour. Change this to whatever is suitable.") with `fuzz-seconds: 3600`, `mode: 'batch'`. Also: "NOTE: If batch fuzzing is running, you must also run corpus pruning."

Continuous builds:

> "The continuous build task causes a build to be triggered and uploaded as a GitHub Actions artifact whenever a new push is done to main/default branch. Continuous builds are used when a crash is found during PR fuzzing to determine whether the crash was newly introduced. If the crash is not novel, PR fuzzing will not report it. This means that there will be fewer unrelated failures when running code change fuzzing."

> "Disclaimer: If your builds are large they may exceed the free GitHub actions quotas. In this case it's recommended to not enable continuous builds."

Corpus pruning cron job: daily (`'0 0 * * *'`), `mode: 'prune'`, `fuzz-seconds: 600`.

Crash artifact download:

> "When the fuzzer crashes the input file that causes the crash is uploaded as an artifact."

Storage repo (the recommended corpus persistence mechanism on GitHub):

> "It's optional but recommended that you set up a separate git repo for storing corpora and coverage reports. The storage repo will make corpus management better in some scenarios and will allow you to view coverage reports on the web rather than downloading them as artifacts. An empty repository for this is sufficient. The corpus have to be uploaded in the repository under the folder `/corpus/<fuzz_target>/` for each fuzzer."

> "You'll need to set up a personal access token with write permissions to the storage repo and add it as a repository secret called PERSONAL_ACCESS_TOKEN. This is because the default GitHub auth token is not able to write to other repositories."

> "If a storage repo isn't specified, corpora and coverage reports will be uploaded as GitHub artifacts instead."

Affected-fuzzers selection requires the storage repo on the build step too:

> "If you would like PR fuzzing to run only the fuzzers affected by the current change, you'll need to add these same options to the 'Build Fuzzers' step above. The 'affected fuzzers' are determined by using coverage reports."

Private repos are supported:

> "In order for ClusterFuzzLite to use private repos, the GitHub token needs to be passed to the build and run steps."

---

## Source 3 — OSS-Fuzz: Continuous Integration (CIFuzz)

- URL: https://google.github.io/oss-fuzz/getting-started/continuous-integration/
- Retrieved: 2026-06-10

Relevant passages:

What CIFuzz is and who can use it:

> "OSS-Fuzz offers CIFuzz, a GitHub action/CI job that runs your fuzz targets on pull requests. ... Currently, CIFuzz primarily supports projects hosted on GitHub. Non-OSS-Fuzz users can use CIFuzz with additional features through ClusterFuzzLite."

Crash-reporting filter (the two-condition novelty test):

> "If CIFuzz finds a crash, it reports the crash only if both of following are true: The crash is reproducible (on the PR/commit build). The crash does not occur on older OSS-Fuzz builds. (If the crash does occur on older builds, then it was not introduced by the PR/commit being tested.)"

Corpus reuse gives regression testing for free:

> "CIFuzz uses 30 day old/public regressions and corpora from OSS-Fuzz. This makes fuzzing more effective and gives you regression testing for free."

Affected-target selection:

> "If your project supports OSS-Fuzz's code coverage, CIFuzz only runs the fuzzers affected by a pull request/commit. Otherwise it will divide up the allotted fuzzing time (10 minutes by default) among all fuzzers in the project."

PR fuzz duration guidance:

> "Set the value of fuzz-seconds. The longest time that the project maintainers are acceptable with should be used. This value should be at minimum 600 seconds and scale with project size."

> "fuzz-seconds: Determines how long CIFuzz spends fuzzing your project in seconds. The default is 600 seconds. The GitHub Actions max run time is 21600 seconds (6 hours)."

Crash artifact handling in the example workflow: an `Upload Crash` step (`actions/upload-artifact@v4`, `if: failure() && steps.build.outcome == 'success'`, `path: ./out/artifacts`) plus SARIF upload to code scanning (`github/codeql-action/upload-sarif@v2`).

Requirements: "Your project must be integrated with OSS-Fuzz. Your project is hosted on GitHub."

Trigger scoping: "You can make CIFuzz trigger only on certain branches or paths" (example restricts to `**.c`, `**.cc`, `**.cpp`, `**.cxx`, `**.h` on master/release branches).

---

## Source 4 — OSS-Fuzz: Accepting New Projects (eligibility) + Corpora (storage/backups)

- URL: https://google.github.io/oss-fuzz/getting-started/accepting-new-projects/
- URL: https://google.github.io/oss-fuzz/advanced-topics/corpora/
- Retrieved: 2026-06-10

Relevant passages:

Eligibility bar for hosted OSS-Fuzz:

> "To be accepted to OSS-Fuzz, an open-source project must have a significant user base and/or be critical to the global IT infrastructure."

Submission mechanics: PR adding `projects/<project_name>/project.yaml` with homepage, main_repo, language, and a `primary_contact` that "belongs to an established project committer (according to VCS logs)" and "is associated with a Google account."

Corpus storage for accepted projects (corpora.md):

> "The corpora for fuzz targets are stored on Google Cloud Storage."

> "The fuzzer statistics page for your project on ClusterFuzz contains a link to the Google Cloud console for your corpus under the corpus_size column."

Corpus download via `gsutil -m cp -r gs://<bucket_path> <local_directory>`.

> "We keep daily zipped backups of your corpora. These can be accessed from the corpus_backup column of the fuzzer statistics page."

---

## Source 5 — OSS-Fuzz: Ideal Integration (seed corpus, dictionary, regression testing)

- URL: https://google.github.io/oss-fuzz/advanced-topics/ideal-integration/
- Retrieved: 2026-06-10

Relevant passages:

Checklist for every fuzz target:

> "Every fuzz target: Is maintained by code owners in their RCS (Git, SVN, etc). Is built with the rest of the tests - no bit rot! Has a seed corpus with good code coverage. Has a dictionary, if applicable. Is continuously tested on the seed corpus with ASan/UBSan/MSan. Is fast and has no OOMs."

Seed corpus quality and version control:

> "The quality of the seed corpus has a huge impact on fuzzing efficiency; the higher the quality, the easier it is for the fuzzer to discover new code paths. The ideal corpus is a minimal set of inputs that provides maximal code coverage."

> "For better OSS-Fuzz integration, the seed corpus should be available in revision control (it can be the same as or different from the source code). It should be regularly extended with the inputs that (used to) trigger bugs and/or touch new parts of the code."

Dictionaries:

> "For some input types, a simple dictionary of tokens used by the input language can have a dramatic impact on fuzzing efficiency. For example, when fuzzing an XML parser, a dictionary of XML tokens is helpful."

Regression testing distinct from fuzzing:

> "Fuzz targets should be regularly tested (not necessarily fuzzed!) as a part of the project's regression testing process. One way to do so is to link the fuzz target with a simple standalone driver ... that runs the provided inputs, then use this driver with the seed corpus created in previous step. We recommend you use sanitizers during regression testing."

Performance:

> "Fuzz targets should perform well, because high memory usage and/or slow execution speed can slow the down the growth of coverage and finding of new bugs."

---

## Source 6 — LLVM: libFuzzer documentation

- URL: https://llvm.org/docs/LibFuzzer.html
- Retrieved: 2026-06-10

Relevant passages:

Corpus fundamentals:

> "Coverage-guided fuzzers like libFuzzer rely on a corpus of sample inputs for the code under test. This corpus should ideally be seeded with a varied collection of valid and invalid inputs ... If a mutation triggers execution of a previously-uncovered path in the code under test, then that mutation is saved to the corpus for future variations."

> "LibFuzzer will work without any initial seeds, but will be less efficient if the library under test accepts complex, structured inputs."

> "The corpus can also act as a sanity/regression check, to confirm that the fuzzing entrypoint still works and that all of the sample inputs run through the code under test without problems."

Corpus minimization with -merge:

> "If you have a large corpus (either generated by fuzzing or acquired by other means) you may want to minimize it while still preserving the full coverage. One way to do that is to use the -merge=1 flag: ./my_fuzzer -merge=1 NEW_CORPUS_DIR FULL_CORPUS_DIR. You may use the same flag to add more interesting items to an existing corpus. Only the inputs that trigger new coverage will be added to the first corpus."

New inputs are written back to the first corpus directory:

> "As the fuzzer discovers new interesting test cases (i.e. test cases that trigger coverage of new paths through the code under test), those test cases will be added to the corpus directory."

> "The fuzzer will read test inputs from each of these corpus directories, and any new test inputs that are generated will be written back to the first corpus directory."

Crash artifacts:

> "Any crashes or sanitizer failures will be reported as usual, stopping the fuzzing process, and the particular input that triggered the bug will be written to disk (typically as crash-<sha1>, leak-<sha1>, or timeout-<sha1>)."

> "-artifact_prefix: Provide a prefix to use when saving fuzzing artifacts (crash, timeout, or slow inputs) as $(artifact_prefix)file. Defaults to empty."

> "-exact_artifact_path: ... If non-empty, write the single artifact on failure (crash, timeout) as $(exact_artifact_path). This overrides -artifact_prefix and will not use checksum in the file name."

Regression mode (running files, not fuzzing):

> "If a list of files (rather than directories) are passed to the fuzzer program, then it will re-run those files as test inputs but will not perform any fuzzing. In this mode the fuzzer binary can be used as a regression test (e.g. on a continuous integration system) to check the target function and saved inputs still work."

Crash minimization:

> "-minimize_crash: If 1, minimizes the provided crash input. Use with -runs=N or -max_total_time=N to limit the number of attempts."

Resource-limit failure modes relevant to triage:

> "-timeout: Timeout in seconds, default 1200. If an input takes longer than this timeout, the process is treated as a failure case."

> "-rss_limit_mb: Memory usage limit in Mb, default 2048. ... If an input requires more than this amount of RSS memory to execute, the process is treated as a failure case."

> "-error_exitcode: Exit code (default 77) used if libFuzzer itself (not a sanitizer) reports a bug (leak, OOM, etc)."

Fork mode for crash-resistant batch runs:

> "Experimental mode -fork=N (where N is the number of parallel jobs) enables oom-, timeout-, and crash-resistant fuzzing with separate processes ... -ignore_crashes: ... If an OOM happens during fuzzing in one of the child processes, the reproducer is saved on disk, and fuzzing continues." (related flags -ignore_ooms, -ignore_timeouts, both true by default in fork mode)

Parallelism: "-jobs=N ... these jobs will be run across a set of worker processes, by default using half of the available CPU cores."
