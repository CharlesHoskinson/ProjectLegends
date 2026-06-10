# Research capture: Compiler Caching on GitHub Actions

Topic: ccache/sccache for C++ CI on GitHub Actions — MSVC+gcc+clang support, cache key design, FetchContent interplay, hit rates, GitHub cache limits.
All sources fetched with scrapling on 2026-06-10.

---

## Source 1: sccache GitHub Actions storage backend docs

- URL: https://github.com/mozilla/sccache/blob/main/docs/GHA.md (fetched via raw.githubusercontent.com)
- Retrieved: 2026-06-10

Relevant passages:

> To use the GitHub Actions cache, you need to set `SCCACHE_GHA_ENABLED` to `on` to enable it.
>
> By changing `SCCACHE_GHA_VERSION`, we can purge all the cache.
>
> This cache type will need tokens like `ACTIONS_RESULTS_URL` and `ACTIONS_RUNTIME_TOKEN` to work. You can set these environmental variables using the following step in a GitHub Actions workflow.
>
> ```yaml
> - name: Configure sccache
>   uses: actions/github-script@v7
>   with:
>     script: |
>       core.exportVariable('ACTIONS_RESULTS_URL', process.env.ACTIONS_RESULTS_URL || '');
>       core.exportVariable('ACTIONS_RUNTIME_TOKEN', process.env.ACTIONS_RUNTIME_TOKEN || '');
> ```
>
> ## Behavior
>
> In case sccache reaches the rate limit of the service, the build will continue, but the storage might not be performed.

Notes: sccache talks to the Actions cache service natively (per-object granularity) — no tar/restore of a cache directory, no explicit `actions/cache` key design needed for the object cache itself. The Mozilla-Actions/sccache-action marketplace action installs the binary and wires these variables.

---

## Source 2: sccache README (compiler support, MSVC + CMake specifics, caveats)

- URL: https://github.com/mozilla/sccache/blob/main/README.md (fetched via raw.githubusercontent.com)
- Retrieved: 2026-06-10

Relevant passages:

> sccache is a ccache-like compiler caching tool. It is used as a compiler wrapper and avoids compilation when possible, storing cached results either on local disk or in one of several cloud storage backends.

> sccache supports gcc, clang, MSVC, rustc, NVCC, NVC++, hipcc, and Wind River's diab compiler. Both gcc and msvc support Response Files.

> To use sccache with cmake, provide the following command line arguments to cmake 3.4 or newer:
>
> ```
> -DCMAKE_C_COMPILER_LAUNCHER=sccache
> -DCMAKE_CXX_COMPILER_LAUNCHER=sccache
> ```

> The process for using sccache with MSVC and cmake, depends on which version of cmake you're using. **For versions of cmake 3.24 and earlier**, to generate PDB files for debugging with MSVC, you can use the `/Z7` option. Alternatively, the `/Zi` option together with `/Fd` can work if `/Fd` names a different PDB file name for each object file created. Note that CMake sets `/Zi` by default, so if you use CMake, you can use `/Z7` by adding code like this in your CMakeLists.txt:
> [string(REPLACE "/Zi" "/Z7" ...) per build type]

> **For versions of cmake 3.25 and later**, to compile with MSVC, you have to use the new `CMAKE_MSVC_DEBUG_INFORMATION_FORMAT` option, meant to configure the `-Z7` flag. Additionally, you must set the cmake policy number 0141 to the NEW setting:
>
> ```cmake
> set(CMAKE_MSVC_DEBUG_INFORMATION_FORMAT "$<$<CONFIG:Debug,RelWithDebInfo>:Embedded>")
> cmake_policy(SET CMP0141 NEW)
> ```
>
> Alternatively, if configuring cmake with MSVC on the command line:
>
> ```
> cmake -DCMAKE_C_COMPILER_LAUNCHER=sccache -DCMAKE_CXX_COMPILER_LAUNCHER=sccache -DCMAKE_MSVC_DEBUG_INFORMATION_FORMAT=Embedded -DCMAKE_POLICY_CMP0141=NEW [...]
> ```

> By default, sccache will fail your build if it fails to successfully communicate with its associated server. To have sccache instead gracefully failover to the local compiler without stopping, set the environment variable `SCCACHE_IGNORE_SERVER_IO_ERROR=1`.

> ## Normalizing Paths with `SCCACHE_BASEDIRS`
> By default, sccache requires absolute paths to match for cache hits. To enable cache sharing across different build directories, you can set `SCCACHE_BASEDIRS` to strip a base directory from paths before hashing. [...] Path matching is **case-insensitive** on Windows and **case-sensitive** on other operating systems. [...] This is similar to ccache's `CCACHE_BASEDIR` and helps when: Building the same project from different directories; Sharing cache between CI jobs with different checkout paths [...]

> ## Known Caveats
> ### General
> * By default, absolute paths to files must match to get a cache hit. To work around this, use `SCCACHE_BASEDIRS` (see above) to normalize paths before hashing.
> ### C++20 Modules
> sccache has partial support for C++20 named modules when using **Clang**. [...] **GCC** and **MSVC** C++20 modules are not yet supported. Compilations using `-fmodules-ts` (GCC) or `/interface`, `/ifcOutput`, etc. (MSVC) will bypass the cache.

> In situations where several different compilation invocations should not reuse the cached results from each other, one can set `SCCACHE_C_CUSTOM_CACHE_BUSTER` to a unique value that'll be mixed into the hash.

---

## Source 3: hendrikmuhs/ccache-action README (de-facto standard ccache action)

- URL: https://github.com/hendrikmuhs/ccache-action (fetched via raw.githubusercontent.com README.md)
- Retrieved: 2026-06-10

Relevant passages:

> A Github action to speedup building using ccache/sccache for C/C++ projects. Works on Linux, macOS, and Windows.

> ```yaml
> - name: ccache
>   uses: hendrikmuhs/ccache-action@v1.2
> ```
> NB! This should always come after the `actions/checkout` step.

> In order to use ccache in your other steps, point the compiler to it, e.g. [...] `-D CMAKE_C_COMPILER_LAUNCHER=ccache -D CMAKE_CXX_COMPILER_LAUNCHER=ccache`

> Ccache/sccache gets installed by this action if it is not installed yet.

> ### Notes on Windows support
> Note that using Ccache on Windows probably works, but Sccache is recommended for stable Windows support.

> ### If you have multiple jobs
> If you have multiple jobs or targets (eg. `Debug`, `Release`) or multiple OS's, it makes sense to cache them separately. An additional cache key can be specified.
>
> ```yaml
> - name: ccache
>   uses: hendrikmuhs/ccache-action@v1.2
>   with:
>     key: ${{ github.job }}-${{ matrix.os }}  # Eg. "some_build-ubuntu-latest"
> ```

> ### Ccache statistics
> Stats are provided as part of the post action, check the output to see if cache is effective.

> ## How it works
> This action is based on https://cristianadam.eu/20200113/speeding-up-c-plus-plus-github-actions-using-ccache/
> In a nutshell, the `.ccache` folder is configured in the runner path and the folder is persisted and reloaded using `cache`.

---

## Source 4: Cristian Adam — "Speeding up C++ GitHub Actions using ccache" (2020-01-13)

- URL: https://cristianadam.eu/20200113/speeding-up-c-plus-plus-github-actions-using-ccache/
- Retrieved: 2026-06-10
- Note: the original engineering write-up the ccache-action is built on. Dated 2020 — its 2 GiB cache-limit figure is superseded by current GitHub docs (Source 5).

Relevant passages:

> Building a project on GitHub Actions means always a build from scratch, for any given change, big or small. This takes time and wastes resources unnecessarily.

> The total size of cached files per repository is 2 GiB. [2020 figure; now 10 GB — see Source 5]

> The following yaml file excerpt will enable ccache support for GitHub Actions:
> [timestamp step producing a unique key, then]
> ```
> - name: ccache cache files
>     uses: actions/cache@v1.1.0
>     with:
>     path: .ccache
>     key: ${{ matrix.config.name }}-ccache-${{ steps.ccache_cache_timestamp.outputs.timestamp }}
>     restore-keys: |
>         ${{ matrix.config.name }}-ccache-
> ```
> This makes sure that for every build the GitHub Actions cache key is unique. It will restore the latest tar file containing the `.ccache` folder for the current configuration, and at the end of the job it will store the updated `.ccache` folder in a new tar file.

> In the configure step one only needs to pass:
> `-D CMAKE_C_COMPILER_LAUNCHER=ccache -D CMAKE_CXX_COMPILER_LAUNCHER=ccache`

> Before building the project I am configuring ccache via environment variables like this:
> ```
> set(ENV{CCACHE_BASEDIR} "${ccache_basedir}")
> set(ENV{CCACHE_DIR} "${ccache_basedir}/.ccache")
> set(ENV{CCACHE_COMPRESS} "true")
> set(ENV{CCACHE_COMPRESSLEVEL} "6")
> set(ENV{CCACHE_MAXSIZE} "400M")
> if ("${{ matrix.config.cxx }}" STREQUAL "cl")
>     set(ENV{CCACHE_MAXSIZE} "600M")
> endif()
> ```
> This will ensure that the maximum size of the cache will be 400 MiB, will use compression, and the paths will always be relative to the build directory.

> ccache statistics are zeroed before starting the build (`ccache -z`), and displayed after the build (`ccache -s`).

> [On MSVC, circa 2020, using the author's fork:] At the moment I have only tested CMake with Ninja generator in Release mode [...] Debug mode is not supported since ccache should cache also the pdb files. Precompiled headers are not supported since ccache should know about them and store the pch files.

---

## Source 5: GitHub Docs — Dependency caching reference

- URL: https://docs.github.com/en/actions/reference/workflows-and-actions/dependency-caching
- Retrieved: 2026-06-10

Relevant passages:

> The `cache` action will attempt the following sequence when restoring a cache: First, it searches for an exact match to your provided `key`. If no exact match is found, it will search for partial matches of the `key`. If there is still no match found, and you've provided `restore-keys`, these keys will be checked sequentially for partial matches.

> You cannot change the contents of an existing cache. Instead, you can create a new cache with a new key.

> `restore-keys` allows you to specify a list of alternate restore keys to use when there is a cache miss on `key`. You can create multiple restore keys ordered from the most specific to least specific. [...] If there are multiple partial matches for a restore key, the action returns the most recently created cache.

> [Cache scoping] Workflow runs can restore caches created in either the current branch or the default branch (usually `main`). If a workflow run is triggered for a pull request, it can also restore caches created in the base branch [...] Workflow runs cannot restore caches created for child branches or sibling branches.

> When a cache is created by a workflow run triggered on a pull request, the cache is created for the merge ref (`refs/pull/.../merge`). Because of this, the cache will have a limited scope and can only be restored by re-runs of the pull request. It cannot be restored by the base branch or other pull requests targeting that base branch.

> ## Usage limits and eviction policy
> GitHub will remove any cache entries that have not been accessed in over 7 days. There is no limit on the number of caches you can store, but the total size of all caches in a repository is limited. By default, the limit is 10 GB per repository, but this limit can be increased by enterprise owners, organization owners, or repository administrators. Any usage beyond 10 GB is billed to your account. Once a repository has reached its maximum cache storage, the cache eviction policy will create space by deleting the caches in order of last access date, from oldest to most recent.

> If you exceed the limit, GitHub will save the new cache but will begin evicting caches until the total size is less than the repository limit. The cache eviction process may cause cache thrashing, where caches are created and deleted at a high frequency.

> You can create cache entries at a rate of up to 200 uploads per minute per repository, and download them at a rate of 1500 downloads per minute per repository. If you exceed this rate, subsequent cache upload or download attempts will fail until the relevant rate limit resets.

> Increasing cache size: Repositories owned by users can configure up to 10 TB per repository. [...] Increasing the limit beyond the default 10 GB will incur additional costs, if that storage is used. [...] If you have limits configured, and you exceed a budget, your cache will become read-only [...] Illustrative monthly costs: 50GB $2.80; 200GB $13.30; 1000GB $69.30.

---

## Source 6: ccache.dev — Supported platforms, compilers and languages

- URL: https://ccache.dev/platform-compiler-language-support.html
- Retrieved: 2026-06-10
- Context: official support matrix for the latest released ccache, currently 4.13.6.

Relevant passages:

> This page collects information on platforms (operating systems), compilers and source code languages that are supported by the latest released ccache version, currently 4.13.6.

> Support levels: A — Supported. Built and tested regularly and before new releases. High attention to bug reports. B — Partially supported. [...] C — Not officially supported.

> Run-time support (i.e., using ccache) — Platforms:
> A — Linux (regularly tested on Ubuntu 22.04 and 24.04)
> A — macOS (regularly tested on macOS 14)
> A — Windows native (regularly built with Mingw-w64 and tested on Windows 2025)
> B — Windows with MSYS2

> Run-time support — Compilers:
> A — GCC
> A — Clang
> A — MSVC (Microsoft Visual C++)
> A — NVCC
> B — clang-cl (MSVC compatibility for Clang)

Notes: MSVC is now level A in ccache's official matrix. This supersedes older community guidance (Source 3) that recommended sccache for stable Windows support. Caveat from ccache manual/issue tracker (not on this page): MSVC `/Zi` remains uncacheable — `/Z7` (embedded debug info) is required, same constraint as sccache.

---

## Source 7: ccache.dev — Performance (hit/miss economics)

- URL: https://ccache.dev/performance.html
- Retrieved: 2026-06-10

Relevant passages:

> The performance of ccache depends on a lot of factors, which makes it quite hard to predict the improvement for a given use case.

> It should also be noted that if the expected hit rate is low, there may be a net performance loss when using ccache because of the overhead of cache misses (typically 5%-20%, but just 1%-3% with depend mode enabled).

> [Measured on ccache.c, -g -O2:] cache hit in direct mode 0.0048 s vs 0.6988 s without ccache (145x); preprocessor-mode hit 0.0247 s (28x); first-time (miss) overhead ~4% over plain compile.

> As can be seen above, cache hits in the direct mode are about 5 times faster than in the preprocessor mode. [...] The overhead of cache misses can also be seen, but it's smaller for the depend mode.

> [Preprocessor-heavy file:] difference between direct and preprocessor mode hits is about a factor 6 [...] The depend mode really shines here since it avoids making costly preprocessor calls.

> So to sum it up: it is probably wise to perform some measurements with and without ccache for your typical use case before enabling it!

---

## Sources found but not fetched

- GitHub changelog 2025-11-20 "GitHub Actions cache size can now exceed 10 GB per repository" (https://github.blog/changelog/2025-11-20-github-actions-cache-size-can-now-exceed-10-gb-per-repository/) — fetched successfully and consistent with Source 5; folded into Source 5's limits discussion. Key extra detail: two new admin policies (cache size eviction limit in GB, cache retention limit in days); defaults remain 10 GB / 7-day retention at no cost; LRU eviction; budgets can make cache read-only.
- ccache issue #1040 (Support for MSVC's /Zi) — not fetched as a page; the /Zi-uncacheable, /Z7-required constraint is documented in both sccache README (Source 2) and ccache release notes/manual.
