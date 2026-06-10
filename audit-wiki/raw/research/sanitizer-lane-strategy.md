# Research capture: Sanitizer Lane Strategy

Topic: which sanitizers gate PRs vs nightly at major C++ shops; allow-failure discipline (suppressions, known-issues lists, exit criteria); MSan's instrumented-libc++ requirement; TSan strategies for legacy-global-heavy codebases.
All sources fetched with scrapling on 2026-06-10.

---

## Source 1: Clang MemorySanitizer documentation

- URL: https://clang.llvm.org/docs/MemorySanitizer.html
- Retrieved: 2026-06-10

Relevant passages:

> MemorySanitizer is a detector of uninitialized memory use. It consists of a compiler instrumentation module and a run-time library. Typical slowdown introduced by MemorySanitizer is 3x.

> ## Handling external code
>
> MemorySanitizer requires that all program code is instrumented. This also includes any libraries that the program depends on, even libc. Failing to achieve this may result in false reports. For the same reason you may need to replace all inline assembly code that writes to memory with a pure C/C++ code.
>
> Full MemorySanitizer instrumentation is very difficult to achieve. To make it easier, MemorySanitizer runtime library includes 70+ interceptors for the most common libc functions. They make it possible to run MemorySanitizer-instrumented programs linked with uninstrumented libc. For example, the authors were able to bootstrap MemorySanitizer-instrumented Clang compiler by linking it with self-built instrumented libc++ (as a replacement for libstdc++).

> ## Ignorelist
>
> MemorySanitizer supports `src` and `fun` entity types in Sanitizer special case list, that can be used to relax MemorySanitizer checks for certain source files and functions. All "Use of uninitialized value" warnings will be suppressed and all values loaded from memory will be considered fully initialized.

> ## Supported Platforms
> MemorySanitizer is supported on the following OS: Linux, NetBSD, FreeBSD.

> ## Limitations
> MemorySanitizer uses 2x more real memory than a native run, 3x with origin tracking. [...] Static linking is not supported.

> ## Current Status
> MemorySanitizer is known to work on large real-world programs (like Clang/LLVM itself) that can be recompiled from source, including all dependent libraries.

---

## Source 2: Firefox Source Docs — Thread Sanitizer

- URL: https://firefox-source-docs.mozilla.org/tools/sanitizer/tsan.html
- Retrieved: 2026-06-10

Relevant passages:

> Thread Sanitizer (TSan) is a fast data race detector for C/C++ and Rust programs. [...] Unlike other tools, it understands compiler-builtin atomics and synchronization and therefore provides very accurate results with no false positives (except if unsupported synchronization primitives like inline assembly or memory fences are used).

> The easiest way to get Firefox builds with Thread Sanitizer is to download a continuous integration TSan build of mozilla-central (updated at least daily).

> Note that unlike other sanitizers, TSan is currently only supported on Linux.

> ## Thread Sanitizer and Symbols
>
> Unlike Address Sanitizer, TSan requires in-process symbolizing to work properly in the first place, as any kind of runtime suppressions will otherwise not work. Hence, it is required that you have a copy of `llvm-symbolizer` either in your `PATH` or pointed to by the `TSAN_SYMBOLIZER_PATH` environment variable.

> ## Runtime Suppressions
>
> TSan has the ability to suppress race reports at runtime. This can be used to silence a race while a fix is developed as well as to permanently silence a (benign) race that cannot be fixed.
>
> Warning: Many races look benign but are indeed not. Please read the FAQ section carefully and think twice before attempting to suppress a race.
>
> The runtime Suppression list is directly baked into Firefox at compile-time and located at `build/sanitizers/TsanOptions.cpp`.
>
> Important: When adding a suppression, always make sure to include the bug number. If the suppression is supposed to be permanent, please add the string `permanent` in the same line as the bug number.
>
> Important: When adding a suppression for a data race, always make sure to include a stack frame from each of the two race stacks. Adding only one suppression for one stack can cause intermittent failures that are later on hard to track. One exception to this rule is when suppressing races on global variables. In that case, a single race entry with the name of the variable is sufficient.

> ## Known Sources of False Positives
>
> TSan has a number of things that can cause false positives, namely: The use of memory fences (e.g. Rust Arc); The use of inline assembly for synchronization; Uninstrumented code (e.g. external libraries) using compiler-builtins for synchronization; A lock order inversion involving only a single thread can cause a false positive deadlock report.
>
> If none of these four items are involved, you should never assume that TSan is reporting a false positive to you without consulting TSan peers.

> ## Why fix data races?
>
> Data races are undefined behavior and can cause crashes as well as correctness issues. [...] Since it is very hard to judge if a particular race could cause such a situation, we have decided to fix all data races wherever possible, since doing so is often cheaper than analyzing a race.

> ## My race is benign, can we ignore it?
>
> While it is possible to add a runtime suppression to ignore the race, we strongly encourage you to not do so, for two reasons: Each suppressed race decreases the overall performance of the TSan build, as the race has to be symbolized each time when it occurs. [...] Deciding if a race is truly benign is surprisingly hard. [...] Valid reasons to suppress a confirmed benign race include performance problems arising from fixing the race or cases where fixing the race would require an unreasonable amount of work.

---

## Source 3: Mozilla Hacks — "Eliminating Data Races in Firefox – A Technical Report" (2021-04-06, Holler/Beingessner/Wright)

- URL: https://hacks.mozilla.org/2021/04/eliminating-data-races-in-firefox-a-technical-report/
- Retrieved: 2026-06-10

Relevant passages:

> We successfully deployed ThreadSanitizer in the Firefox project to eliminate data races in our remaining C/C++ components. [...] We recommend that all multithreaded C/C++ projects adopt the ThreadSanitizer tool to enhance code quality.

> One important property of TSan is that, when properly deployed, the data race detection does not produce false positives. This is incredibly important for tool adoption, as developers quickly lose faith in tools that produce uncertain results.

> The most significant issue we faced was that it is really difficult to prove that data races are actually harmful at all [...] In particular, the term "benign" came up often. [...] While benign data races do exist, we found (in agreement with previous work on this subject) that data races are very easily misclassified as benign. [...] As a result, we decided that the ultimate goal should be a "no data races" policy that declares even benign data races as undesirable due to their risk of misclassification, the required time for investigation and the potential risk from future compilers (with better optimizations) or future platforms (e.g. ARM).

> This is where TSan's suppression list came in handy: We knew we had to stop the influx of new data races but at the same time get the tool usable without fixing all legacy issues. The suppression list (in particular the version compiled into Firefox) allowed us to temporarily ignore data races once we had them on file and ultimately bring up a TSan build of Firefox in CI that would automatically avoid further regressions. Of course, security bugs required specialized handling, but were usually easy to recognize (e.g. racing on non-thread safe pointers) and were fixed quickly without suppressions.

> To help us understand the impact of our work, we maintained an internal list of all the most serious races that TSan detected (ones that had side-effects or could cause crashes). This data helped convince developers that the tool was making their lives easier while also clearly justifying the work to management.

> We looked at all the bugs we found over a year and how they were classified. Of the 64 bugs we looked at, 34% were classified as "benign" and 22% were "impactful" (the rest hadn't been classified). [...] The trivial fixes were mostly turning non-atomic variables into atomics (20%), adding permanent suppressions for upstream issues that we couldn't address immediately (15%), or removing overly complicated code (20%). Only 45% of the benign fixes actually required some sort of more elaborate patch.

> Instrumenting all code in Firefox isn't currently possible because it needs to use shared system libraries like GTK and X11. Fortunately, TSan offers the "called_from_lib" feature that can be used in the suppression list to ignore any calls originating from those shared libraries.

> As for unsupported primitives, the only issue we ran into was the lack of support for fences. Most fences were the result of a standard atomic reference counting idiom which could be trivially replaced with an atomic load in TSan builds.

> [On a races-on-globals bug class] We also found several instances of components which were explicitly designed to be single-threaded accidentally being used by multiple threads [...] it was a race that had more harmful effects than just a crash, and it caught a larger logic error of something being used outside of its original design parameters.

> However, developers claimed on various occasions that a particular report must be a false positive. In all of these cases, it turned out that TSan was indeed right and the problem was just very subtle and hard to understand.

---

## Source 4: Chromium — ThreadSanitizer (TSan) v. 2

- URL: https://www.chromium.org/developers/testing/threadsanitizer-tsan-v2/
- Retrieved: 2026-06-10

Relevant passages:

> ThreadSanitizer v2 is only supported on Linux so far.

> Note: TSan builds with libc++ by default (the use_custom_libcxx=1 GYP flag). If your tests fail under TSan, make sure you're not relying on some unspecified libstdc++ behavior.

> ## Disabling tests
>
> Unlike Valgrind, ThreadSanitizer v2 doesn't support gtest filter files. Instead of adding a test name to a blocklist you should disable the test in the code under #if defined(THREAD_SANITIZER).

> ## Suppressing race reports
>
> The default ThreadSanitizer v2 suppressions reside in build/sanitizers/tsan_suppressions.cc and are automatically linked to every executable in Chromium. You can supply additional suppressions by adding `suppressions=/path/to/suppressions.txt` to `TSAN_OPTIONS`.

> Each suppression is a one line of the form "suppression_type:pattern". The most common suppression type is "race" [...] The pattern is matched against: function name/file name/module of each frame in the stack trace of each conflicting memory access; global variable name (if present).

> Good suppressions match a single race report (or a number of reports with a common root cause), but are unlikely to mask further races in other components. A suppression must be preceded by a comment (started with a "#") with a crbug link.

> Examples of good suppressions for the above race report:
> `race:v8/src/zone-inl.h` (suppresses other races in zone-inl.h as well); `race:v8::internal::Zone::allocation_size_` (you can also suppress globals).
>
> Examples of bad suppressions: `race:New` (same as "*New*", which will match a ton of other functions); `race:content_browsertests` (will suppress everything in content_browsertests); `race:base::MessageLoop::Run` (too generic).

> The possible suppression prefixes are: "race:" (for data races and use-after-free reports), "thread:" (for thread leaks), "mutex:", "signal:", "deadlock:" (for lock-order-inversion reports). You can also disable interceptors in a particular library using the "called_from_lib:libfoo.so" suppression prefix.

> ## Reproducing race reports in tests
>
> Suppressions from build/sanitizers/tsan_suppressions.cc (as well as those passed via TSAN_OPTIONS) are applied at program runtime. If the race report matches a line in the suppressions file, TSan does not print that report.
>
> Ignores from tools/memory/tsan_v2/ignores.txt are applied at compile time. If the function name matches a "fun:" line in the ignores file, TSan does not instrument that function, effectively ignoring all memory accesses (but not synchronization) in that function. If the source file name matches an "src:" line, every function in that file is ignored.

---

## Source 5: Chromium Docs — AddressSanitizer (ASan)

- URL: https://chromium.googlesource.com/chromium/src/+/HEAD/docs/asan.md
- Retrieved: 2026-06-10

Relevant passages:

> AddressSanitizer (ASan) is a fast memory error detector based on compiler instrumentation (LLVM). It is fully usable for Chrome OS, iOS simulator, Linux, Mac, and 64-bit Windows.

> ## Buildbots and trybots
>
> The Chromium Memory waterfall contains buildbots running Chromium tests under ASan on Linux (Linux ASan/LSan bots for the regular Linux build, Linux Chromium OS ASan for the chromeos=1 build running on Linux), macOS, Chromium OS. Linux and Linux Chromium OS bots run with --no-sandbox, but there's an extra Linux bot that enables the sandbox (but disables LeakSanitizer).
>
> The trybots running Chromium tests on Linux and macOS are: linux_chromium_asan_rel_ng, mac_chromium_asan_rel_ng, linux_chromium_chromeos_asan_rel_ng (the chromeos=1 build running on a Linux machine).

> Building with ASan is easy. [...] Make sure to compile release builds.

> ASan's behavior can be changed by exporting the ASAN_OPTIONS env var. [...] Note that Chromium sets its own defaults for some options, so the default behavior may be different from that observed in other projects. See build/sanitizers/sanitizer_options.cc for more details.

Notes: ASan is the sanitizer Chromium wires into pre-commit trybots (`*_asan_rel_ng`), i.e. the PR-gating tier. The related search snippets from chromium.org confirm MSan bots live on the `chromium.memory.fyi` waterfall ("FYI" testers are considered less important, so failures there shouldn't close the tree), with optional MSan trybots `linux_chromium_msan_rel_ng` available for opt-in pre-commit use (source: https://www.chromium.org/developers/testing/memorysanitizer/ and the buildbot tour page; not fetched in full).

---

## Source 6: OSS-Fuzz — Setting up a new project (sanitizer selection)

- URL: https://google.github.io/oss-fuzz/getting-started/new-project-guide/
- Retrieved: 2026-06-10

Relevant passages:

> ## sanitizers (optional)
>
> The list of sanitizers to use. Possible values are: `address`, `memory` and `undefined`. If you don't specify a list, `sanitizers` uses a default list of supported sanitizers (currently "address" and "undefined").
>
> MemorySanitizer ("memory") is also supported and recommended, but is not enabled by default due to the likelihood of false positives from un-instrumented system dependencies. If you want to use "memory," please build all libraries your project needs using MemorySanitizer. This can be done by building them with the compiler flags provided during MemorySanitizer builds. Then, you can opt in by adding "memory" to your list of sanitizers.
>
> If your project does not build with a particular sanitizer configuration and you need some time to fix it, you can use `sanitizers` to override the defaults temporarily. For example, to disable the UndefinedBehaviourSanitizer build, just specify all supported sanitizers except "undefined".
>
> If you want to test a particular sanitizer to see what crashes it generates without filing them in the issue tracker, you can set an `experimental` flag. For example, if you want to test "memory", set `experimental: True` like this:
>
> ```yaml
> sanitizers:
>  - address
>  - memory:
>     experimental: True
>  - undefined
> ```

Notes: the OSS-Fuzz `experimental: True` flag is the closest thing in major-shop practice to a sanctioned "allow-failure" mode: the sanitizer runs and produces crashes, but they are not filed in the tracker — explicitly a temporary evaluation state, not a steady state.

---

## Sources considered and dropped

- https://clang.llvm.org/docs/ThreadSanitizer.html — overlaps Source 2/4 on suppression mechanics (`-fsanitize-ignorelist`, `TSAN_OPTIONS suppressions=`); dropped to stay within the source budget.
- https://www.chromium.org/developers/testing/memorysanitizer/ — confirms MSan-on-FYI-waterfall placement; key facts captured via search snippets in Source 5 notes rather than a full fetch.

---

## Source 7 (appended 2026-06-10): Chromium — MemorySanitizer (MSan)

- URL: https://www.chromium.org/developers/testing/memorysanitizer/
- Retrieved: 2026-06-10 (full fetch; supersedes the snippet-only note in "Sources considered and dropped" above, which is retained unaltered as the original record)

Relevant passages:

> MemorySanitizer (MSan) is a tool that detects use of uninitialized memory. MSan is supported on x86_64 Linux. [...] MSan in Chromium is unlikely to be usable on systems other than Ubuntu Precise/Trusty - please see the note on instrumented libraries below.

> MSan bots are running on chromium.memory.fyi, client.webrtc and chromium.webkit. There are also two LKGR builders for ClusterFuzz: no origins, chained origins (see below for explanation). [...] Trybots: linux_chromium_msan_rel_ng, linux_chromium_chromeos_msan_rel_ng.

> (In older versions of Chromium you also had to explicitly set "use_prebuilt_instrumented_libraries = true". This is now the default if is_msan is set and can no longer be overridden.)
>
> MSan requires using Instrumented system libraries. Note that instrumented libraries are supported on Ubuntu Precise/Trusty only.

> ## Suppressions
>
> MSan does not support suppressions. This is an intentional design choice. We have a blocklist file which is applied at compile time, and is used mainly to compensate for tool issues. Blocklist rules do not work the way suppression rules do - rather than suppressing reports with matching stack traces, they change the way MSan instrumentation is applied to the matched function.

> When you examine a stack trace in an MSan report, all third-party libraries you see in it (with the exception of libc and its components) should reside under out/Release/instrumented_libraries. If you see a DSO under a system-wide directory (e.g. /lib/), then the report is likely bogus and should be fixed by simply adding that DSO to the list of instrumented libraries.

Notes: this page confirms MSan bot placement on the chromium.memory.fyi waterfall with opt-in trybots, but does not itself state that FYI failures don't close the tree — that gloss is not part of this record.

---

## Source 8 (appended 2026-06-10): Firefox Source Docs — Thread Sanitizer, addendum

- URL: https://firefox-source-docs.mozilla.org/tools/sanitizer/tsan.html
- Retrieved: 2026-06-10 (refetch of Source 2's URL to capture passages omitted from the original extract; Source 2 is retained unaltered)

Relevant passages:

> A meta bug called tsan is maintained to keep track of all the bugs found with TSan.

> ## Intermittent Race Reports
>
> Unfortunately, the TSan algorithm does not guarantee, that a race is detected 100% of the time. Intermittent failures with TSan are (to a certain degree) to be expected and the races involved should be filed and fixed to solve the problem.
