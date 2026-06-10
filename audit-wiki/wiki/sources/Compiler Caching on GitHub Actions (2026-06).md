# Compiler Caching on GitHub Actions (2026-06)

External research synthesis: ccache/sccache best practice for the Project Legends CI matrix (gcc-13/clang-18 on ubuntu-latest, MSVC on windows-latest, AppleClang on macos-15; CMake + Ninja/MSVC/Xcode generators; vendored ~1M-line DOSBox-X engine rebuilt from scratch in every job). Raw capture: `raw/research/compiler-caching-actions.md`. All sources retrieved 2026-06-10.

Related: [[Build & CI Audit (2026-06)]], [[CI Run History (2026-06)]].

## Why this matters here

Every job in `.github/workflows/ci.yml` compiles the vendored engine from zero: `linux` (2-way compiler matrix), `linux-ipc`, `linux-sdl3` (2-way), `windows`, `windows-sdl3`, `macos`, `macos-sdl3`, `sanitizers` (4-way), `fuzz`, `coverage`, `packaging` (3-way), `release-validation`. None of them sets a compiler launcher; the only compilation caching anywhere is the `actions/cache` step for `build/_deps/sdl3-*` in the SDL3 and packaging jobs. The engine — the bulk of the serial compute — is recompiled on every run even when no engine source changed. Object-level compiler caching is the standard remedy: GitHub's cache mechanism, although designed for package-manager dependencies, "can be used to cache compilation artifacts" ^[from https://cristianadam.eu/20200113/speeding-up-c-plus-plus-github-actions-using-ccache/ (retrieved 2026-06-10)].

## Applicable practices

### 1. Add a compiler launcher to every compile job

CMake integration is two cache variables, identical for ccache and sccache: `-DCMAKE_C_COMPILER_LAUNCHER=<tool> -DCMAKE_CXX_COMPILER_LAUNCHER=<tool>` (CMake ≥3.4) ^[from https://github.com/mozilla/sccache/blob/main/README.md (retrieved 2026-06-10)]. This is generator-aware: the launcher works with Ninja and Makefiles; for the Visual Studio generator the launcher variables are not honored, which is one reason the `windows` job (default generator = Visual Studio) needs either a switch to `-G Ninja` or sccache-specific MSBuild wiring. The simplest turnkey path on Linux/macOS is `hendrikmuhs/ccache-action`, which installs ccache, persists `.ccache` via the Actions cache, and prints hit statistics in its post action ("Stats are provided as part of the post action, check the output to see if cache is effective") ^[from https://github.com/hendrikmuhs/ccache-action (retrieved 2026-06-10)].

**Applicability to Project Legends:** the `linux`, `linux-ipc`, `linux-sdl3`, `sanitizers`, `fuzz`, and `coverage` jobs in `.github/workflows/ci.yml` all configure with `-G Ninja` already — adding the launcher flags to their existing `cmake -B build` steps is mechanical. The `windows`/`windows-sdl3`/`packaging`(windows) jobs use the default Visual Studio generator and need `-G Ninja` (plus a `vcvars` step or `ilammy/msvc-dev-cmd`) before any launcher takes effect.

### 2. Use sccache for the MSVC jobs; force /Z7-style embedded debug info

sccache supports MSVC as a first-class compiler ("sccache supports gcc, clang, MSVC, rustc, NVCC, NVC++, hipcc...") and has a native GitHub Actions storage backend ^[from https://github.com/mozilla/sccache/blob/main/README.md (retrieved 2026-06-10)]. The MSVC blocker for any compiler cache is the default `/Zi` debug format (compiler writes a shared PDB; output is not a pure function of the translation unit). For CMake ≥3.25 the supported fix is `CMAKE_MSVC_DEBUG_INFORMATION_FORMAT=Embedded` plus `cmake_policy(SET CMP0141 NEW)` — i.e. `/Z7` ^[from https://github.com/mozilla/sccache/blob/main/README.md (retrieved 2026-06-10)].

The GHA backend is enabled with `SCCACHE_GHA_ENABLED=on` and authenticates via `ACTIONS_RESULTS_URL`/`ACTIONS_RUNTIME_TOKEN`; sccache then stores individual objects in the Actions cache service directly — no tarred cache directory, no manual key design. "In case sccache reaches the rate limit of the service, the build will continue, but the storage might not be performed." ^[from https://github.com/mozilla/sccache/blob/main/docs/GHA.md (retrieved 2026-06-10)] For robustness, `SCCACHE_IGNORE_SERVER_IO_ERROR=1` makes sccache fail over to the plain compiler instead of failing the build ^[from https://github.com/mozilla/sccache/blob/main/README.md (retrieved 2026-06-10)].

**Applicability to Project Legends:** the `windows` job builds `--config Release`; `windows-sdl3` and `packaging` likewise. Release with default flags carries no `/Zi`, so Release-config caching works without the debug-format change; the `/Z7` policy only becomes necessary if Debug/RelWithDebInfo MSVC jobs are added. Setting `CMAKE_MSVC_DEBUG_INFORMATION_FORMAT` unconditionally in the top-level CMakeLists (or in the CI configure step) future-proofs this.

### 3. sccache vs ccache on MSVC — current reality

ccache's official support matrix (ccache 4.13.6) now lists MSVC at level A — "Supported. Built and tested regularly and before new releases" — alongside GCC and Clang, with Windows native also level A ("regularly built with Mingw-w64 and tested on Windows 2025") ^[from https://ccache.dev/platform-compiler-language-support.html (retrieved 2026-06-10)].

> [!conflict]
> The widely used `hendrikmuhs/ccache-action` README still states "using Ccache on Windows probably works, but Sccache is recommended for stable Windows support" ^[from https://github.com/hendrikmuhs/ccache-action (retrieved 2026-06-10)], and the original 2020 write-up reported MSVC support only via a fork, Release-mode-only, with PDB and PCH unsupported ^[from https://cristianadam.eu/20200113/speeding-up-c-plus-plus-github-actions-using-ccache/ (retrieved 2026-06-10)]. ccache's own matrix contradicts that as of 4.x: MSVC is level A ^[from https://ccache.dev/platform-compiler-language-support.html (retrieved 2026-06-10)]. The common ground: both tools refuse to cache `/Zi`; embedded debug info (`/Z7`) is required either way. For this repo, sccache's native GHA backend (no tar upload of a monolithic cache dir, graceful rate-limit degradation) is the lower-friction choice on Windows; ccache via `ccache-action` is the lower-friction choice on Linux/macOS. Using sccache on all three platforms is also defensible for uniformity.

Note for C++23 work: sccache does not yet cache MSVC or GCC C++20 modules (`/interface`, `/ifcOutput`, `-fmodules-ts` bypass the cache); Clang named modules have partial support ^[from https://github.com/mozilla/sccache/blob/main/README.md (retrieved 2026-06-10)]. Project Legends does not currently use modules, so this is a watch item, not a blocker.

### 4. Cache key design (ccache-dir-over-actions/cache pattern)

For the ccache route, the canonical key pattern is: a per-configuration prefix plus an always-unique suffix (timestamp or `github.sha`), with `restore-keys` falling back to the prefix — "for every build the GitHub Actions cache key is unique. It will restore the latest tar file containing the `.ccache` folder for the current configuration, and at the end of the job it will store the updated `.ccache` folder in a new tar file" ^[from https://cristianadam.eu/20200113/speeding-up-c-plus-plus-github-actions-using-ccache/ (retrieved 2026-06-10)]. This works because Actions caches are immutable ("You cannot change the contents of an existing cache. Instead, you can create a new cache with a new key") and `restore-keys` partial matches return the most recently created cache ^[from https://docs.github.com/en/actions/reference/workflows-and-actions/dependency-caching (retrieved 2026-06-10)].

Separate caches per job/configuration: "If you have multiple jobs or targets (eg. Debug, Release) or multiple OS's, it makes sense to cache them separately" via an extra key component such as `${{ github.job }}-${{ matrix.os }}` ^[from https://github.com/hendrikmuhs/ccache-action (retrieved 2026-06-10)].

Branch scoping matters for the PR-heavy trigger set in this repo: caches created on a PR merge ref are only restorable by re-runs of that same PR, while every PR can read caches from its base branch and the default branch ^[from https://docs.github.com/en/actions/reference/workflows-and-actions/dependency-caching (retrieved 2026-06-10)]. Best practice follows: warm caches must be written by `push` runs on `master`/`develop` (which `.github/workflows/ci.yml` already triggers), so PRs inherit them.

**Applicability to Project Legends:** distinct cache identities are needed per compile job × matrix leg — at minimum `linux-gcc`, `linux-clang` (libc++ vs libstdc++ makes them disjoint anyway), `linux-ipc`, four `sanitizers` legs, `fuzz`, `coverage`, `windows`, `macos`. ccache hashes compiler+flags itself, so mixing them in one cache dir is correct-but-bloated; separate keys keep each entry small and LRU-friendly. The existing SDL3 keys (`sdl3-linux-${{ matrix.compiler }}-${{ hashFiles('cmake/dependencies.cmake') }}`) already follow the per-config + content-hash pattern and can stay as-is.

### 5. FetchContent interplay

`CMAKE_<LANG>_COMPILER_LAUNCHER` propagates to FetchContent sub-builds made via `FetchContent_MakeAvailable` (they are part of the same CMake build tree), so SDL3/gsl-lite/GoogleTest objects get cached by the same launcher with no extra wiring — this is the practical answer to the "FetchContent and Compiler launcher" question, and is why projects like IREE simply set the launcher globally ^[from https://github.com/mozilla/sccache/blob/main/README.md (retrieved 2026-06-10)]. Two repo-specific notes:

- `cmake/dependencies.cmake` pins all FetchContent tags (`LEGENDS_DEP_SDL3_TAG "release-3.2.8"` etc.), so dependency objects are perfectly stable across runs — ideal cache material. The existing `build/_deps/sdl3-*` source cache in the `linux-sdl3`/`windows-sdl3`/`macos-sdl3`/`packaging` jobs only avoids the git clone + configure; a compiler cache additionally avoids recompiling SDL3 and the engine.
- Compiler-cache keys need not hash `cmake/dependencies.cmake`: ccache/sccache hash the preprocessed input and compile line themselves, so a dependency bump naturally misses old entries and hits new ones. Content-hash keys remain right for the source-tree cache (`_deps`) only.

### 6. Size budget, eviction, and the 10 GB ceiling

GitHub's constraints, current as of the 2025-11 policy change: 10 GB per repository free; entries not accessed in 7 days are removed; at the size limit, least-recently-used entries are evicted; limits can now be raised beyond 10 GB (up to 10 TB) on a pay-as-you-go basis, with admin-configurable size-eviction and retention-days policies ^[from https://docs.github.com/en/actions/reference/workflows-and-actions/dependency-caching (retrieved 2026-06-10)] ^[from https://github.blog/changelog/2025-11-20-github-actions-cache-size-can-now-exceed-10-gb-per-repository/ (retrieved 2026-06-10)]. Exceeding the limit "may cause cache thrashing, where caches are created and deleted at a high frequency" ^[from https://docs.github.com/en/actions/reference/workflows-and-actions/dependency-caching (retrieved 2026-06-10)]. Rate limits exist but degrade gracefully under sccache's GHA backend ^[from https://github.com/mozilla/sccache/blob/main/docs/GHA.md (retrieved 2026-06-10)].

Counter-practice: cap each ccache dir well below the worst case — the reference setup uses `CCACHE_MAXSIZE` of 400M (600M for MSVC) with compression enabled (`CCACHE_COMPRESS=true`, level 6) and `CCACHE_BASEDIR` set to the workspace so paths hash relatively ^[from https://cristianadam.eu/20200113/speeding-up-c-plus-plus-github-actions-using-ccache/ (retrieved 2026-06-10)]. sccache's equivalent for path stability is `SCCACHE_BASEDIRS` ("By default, absolute paths to files must match to get a cache hit") ^[from https://github.com/mozilla/sccache/blob/main/README.md (retrieved 2026-06-10)].

**Applicability to Project Legends:** roughly a dozen compile configurations sharing 10 GB argues for ~500M–800M `CCACHE_MAXSIZE` per configuration (compressed), which a 1M-line engine fits comfortably for single-config object sets; the existing SDL3 source caches and any future caches share the same 10 GB pool, so an over-large ccache tar would evict them. GitHub-hosted runner checkout paths are stable (`/home/runner/work/...`, `D:\a\...`), so basedir settings are belt-and-braces rather than critical here.

### 7. Expected hit rates and miss overhead

No source publishes a universal hit-rate number; ccache's own guidance is that performance "is quite hard to predict" and to measure before relying on it ^[from https://ccache.dev/performance.html (retrieved 2026-06-10)]. The mechanics that govern this repo's expectation:

- A direct-mode cache hit costs ~0.7% of the original compile (145x on the measured TU); a preprocessor-mode hit ~3.5% (28x); a miss adds typically 5%–20% overhead (1%–3% in depend mode) ^[from https://ccache.dev/performance.html (retrieved 2026-06-10)].
- Hit rate ≈ fraction of TUs whose preprocessed content and compile line are unchanged. For Project Legends, typical PRs touch `src/legends`/`tests` and not the vendored `engine/` tree, so the engine's TUs — the dominant compute — should hit at a very high rate once warmed from `master`/`develop` pushes; cold caches (first run, dependency-tag bump in `cmake/dependencies.cmake`, compiler upgrade, eviction after 7 idle days) pay the miss overhead on top of a full build.
- Statistics discipline: zero counters before the build (`ccache -z`) and print after (`ccache -s`), or read the ccache-action post-step / `sccache --show-stats`, and watch the hit rate in CI logs ^[from https://cristianadam.eu/20200113/speeding-up-c-plus-plus-github-actions-using-ccache/ (retrieved 2026-06-10)] ^[from https://github.com/hendrikmuhs/ccache-action (retrieved 2026-06-10)].

One structural caveat for the `coverage` job: gcov instrumentation (`--coverage -fprofile-arcs`) emits `.gcno` files and embeds paths; ccache handles gcov in recent versions but this is the leg most likely to disappoint — measure before trusting (per the general guidance to benchmark your own use case ^[from https://ccache.dev/performance.html (retrieved 2026-06-10)]).

## Bottom line for the repo

Adding launchers to the six Ninja-based Linux jobs is the cheap, high-yield move; converting the Windows jobs to Ninja + sccache is the second; both leave the existing `sdl3-*` source caches untouched. The 10 GB pool is the design constraint: per-configuration caches with explicit size caps, written from push builds on `master`/`develop`, read by PRs.
