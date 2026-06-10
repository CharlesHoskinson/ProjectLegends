# Research notes: Local Preflight Design

Topic: mirroring CI's mandatory tier cheaply on developer machines — a `preflight` entry point, hook vs script vs both, Windows specifics. Context: C++23/CMake/Ninja+MSVC, Windows and Linux developers, CI mandatory tier = 4 build/test configurations + 9 Python check scripts + include rules + C ABI check; no preflight script exists today; pre-commit hook runs one check and is undocumented opt-in; no Makefile or task runner at root.

All sources fetched 2026-06-10 via scrapling (Fetcher.get, stealthy headers). All returned HTTP 200.

---

## Source 1 — CMake: cmake-presets(7) manual

- URL: https://cmake.org/cmake/help/latest/manual/cmake-presets.7.html
- Retrieved: 2026-06-10

Purpose of presets (Introduction):

> "One problem that CMake users often face is sharing settings with other people for common ways to configure a project. This may be done to support CI builds, or for users who frequently use the same build. CMake supports two main files, CMakePresets.json and CMakeUserPresets.json, that allow users to specify common configure options and share them with others."

Project file vs per-developer file:

> "CMakePresets.json is meant to specify project-wide build details, while CMakeUserPresets.json is meant for developers to specify their own local build details. CMakePresets.json may be checked into a version control system, and CMakeUserPresets.json should NOT be checked in."

Workflow presets:

> "Workflow presets may be used in schema version 6 or above."

> "name — A required string representing the machine-friendly name of the preset. This identifier is used in the cmake --workflow --preset option."

> "steps — A required array of objects describing the steps of the workflow. The first step must be a configure preset, and all subsequent steps must be non-configure presets whose configurePreset field matches the starting configure preset."

> "type — A required string. The first step must be configure. Subsequent steps must be either build, test, or package."

Versions section:

> "6 — Added in version 3.25. Package Presets were added. Workflow Presets were added."

Per-platform enable/disable (Condition):

> "The condition field of a preset, allowed in preset files specifying version 3 or above, is used to determine whether or not the preset is enabled. For example, this can be used to disable a preset on platforms other than Windows."

Condition types include `const`, `equals`/`notEquals`, `inList`/`notInList`, `matches`/`notMatches`, `anyOf`/`allOf`, `not`; `equals` lhs/rhs support macro expansion (e.g. `${hostSystemName}`).

Note (observed limitation, from the steps/type spec above): workflow steps can only be configure/build/test/package presets — a workflow preset cannot invoke arbitrary commands, so lint scripts and ABI checks cannot be steps.

---

## Source 2 — pre-commit.com (framework docs)

- URL: https://pre-commit.com/
- Retrieved: 2026-06-10

What it is:

> "Git hook scripts are useful for identifying simple issues before submission to code review. We run our hooks on every commit to automatically point out issues in code such as missing semicolons, trailing whitespace, and debug statements."

> "It is a multi-language package manager for pre-commit hooks. You specify a list of hooks you want and pre-commit manages the installation and execution of any hook written in any language before every commit."

Install flow (per-clone, must be run by each developer):

> "run pre-commit install to set up the git hook scripts ... pre-commit installed at .git/hooks/pre-commit — now pre-commit will run automatically on git commit!"

Changed-files default vs full runs:

> "it's usually a good idea to run the hooks against all of the files when adding new hooks (usually pre-commit will only run on the changed files during git hooks)" — `pre-commit run --all-files`

Stages / tiering:

> "If stages is not set in either of those places the default value will be pulled from the top-level default_stages option (which defaults to all stages)."

> "The manual stage (via stages: [manual]) is a special stage which will not be automatically triggered by any git hook — this is useful if you want to add a tool which is not automatically run, but is run on demand using pre-commit run --hook-stage manual [hookid]."

> "a reasonable setting for a linter or code formatter would be stages: [pre-commit, pre-merge-commit, pre-push, manual]."

> "To install pre-commit for particular git hooks, pass --hook-type to pre-commit install. This can be specified multiple times such as: $ pre-commit install --hook-type pre-commit --hook-type pre-push"

> "one can specify a default set of git hook types to be installed for by setting the top-level default_install_hook_types. For example: default_install_hook_types: [pre-commit, pre-push, commit-msg]"

Supported git hooks: commit-msg, post-checkout, post-commit, post-merge, post-rewrite, pre-commit, pre-merge-commit, pre-push, pre-rebase, prepare-commit-msg.

Repository-local hooks (the fit for in-repo check scripts):

> "Repository-local hooks are useful when: The scripts are tightly coupled to the repository and it makes sense to distribute the hook scripts with the repository. Hooks require state that is only present in a built artifact of your repository ... You can configure repository-local hooks by specifying the repo as the sentinel local."

> "A local hook must define id, name, language, entry, and files / types."

Same tool in CI (hook/CI parity):

> "pre-commit can also be used as a tool for continuous integration. For instance, adding pre-commit run --all-files as a CI step will ensure everything stays in tip-top shape. To check only files which have changed, which may be faster, use something like pre-commit run --from-ref origin/HEAD --to-ref HEAD"

Windows cache location (appveyor example): `cache: '%USERPROFILE%\.cache\pre-commit'`; default store is `~/.cache/pre-commit`, overridable via `PRE_COMMIT_HOME`.

---

## Source 3 — Lefthook (lefthook.dev docs + project README)

- URLs: https://lefthook.dev/ and https://raw.githubusercontent.com/evilmartians/lefthook/master/README.md
- Retrieved: 2026-06-10

What it is / how it wires hooks:

> "Lefthook is a Git hooks manager. It is Fast, Powerful, Simple." (lefthook.dev)

> "You configure lefthook.yml, run lefthook install. Lefthook installs the configured hooks into .git/hooks/. Hook is a simple script that calls lefthook run {hook-name} when executed." (lefthook.dev)

> "Fast. It is written in Go. Can run commands in parallel. ... Simple. It is single dependency-free binary which can work in any environment." (README)

Windows-relevant installation:

> "You can also install lefthook via Homebrew, winget, yum, apt, apk, scoop" (lefthook.dev)

Parallelism and file templating:

> "Parallel execution — Gives you more speed. `pre-push: parallel: true`" (README)

> Jobs take `run:` commands with `{staged_files}` / `{all_files}` placeholders and `glob:` / `exclude:` filters; a custom file list is possible: `files: git diff --name-only HEAD @{push}`. (README examples)

Hooks runnable directly as commands (script/hook duality):

> "Direct control — If you want to run hooks group directly. `$ lefthook run pre-commit`" (README)

> "Your own tasks — If you want to run specific group of commands directly." (README; example defines a `fixer:` group invoked with `lefthook run fixer` — arbitrary named task groups, not only git hook names)

Per-developer overrides without forking the config:

> "Local config — If you are a frontend/backend developer and want to skip unnecessary commands or override something ... `# lefthook-local.yml` `pre-push: exclude_tags: [frontend] jobs: - name: audit packages skip: true`" (README)

Config options seen in docs nav include `assert_lefthook_installed`, `no_auto_install`, `lefthook validate`, `lefthook check-install`, and a `CI` env variable. (lefthook.dev navigation)

---

## Source 4 — just Programmer's Manual

- URLs: https://just.systems/man/en/introduction.html, https://just.systems/man/en/settings.html, https://just.systems/man/en/configuring-the-shell.html
- Retrieved: 2026-06-10

What it is:

> "just is a handy way to save and run project-specific commands." (introduction)

> "just is a command runner, not a build system, so it avoids much of make's complexity and idiosyncrasies. No need for .PHONY recipes!" (introduction)

Cross-platform support and the Windows sh caveat:

> "Linux, macOS, Windows, and other reasonable unixes are supported with no additional dependencies. (Although if your system doesn't have an sh, you'll need to choose a different shell.)" (introduction)

> "just uses sh on Windows by default. To use a different shell on Windows, use windows-shell: `set windows-shell := ["powershell.exe", "-NoLogo", "-Command"]`" (settings, "Windows Shell")

> "set windows-powershell uses the legacy powershell.exe binary, and is no longer recommended." (settings)

Per-platform shell split:

> "Since set windows-shell has higher precedence than set shell, you can use set windows-shell to pick a shell on Windows, and set shell to pick a shell for all other platforms." (configuring-the-shell)

Shell-config precedence (configuring-the-shell): `--shell`/`--shell-arg` CLI options > `set windows-shell` > `set windows-powershell` (deprecated) > `set shell`.

Other relevant settings (settings table): `working-directory`, `dotenv-load`, recipes "can be written in arbitrary languages, like Python or Node.js" via shebangs (introduction), and `just` "can be invoked from any subdirectory" (introduction).

---

## Source 5 — NixCI blog: "CI should fail on your machine first"

- URL: https://blog.nix-ci.com/post/2026-03-09_ci-should-fail-on-your-machine-first
- Retrieved: 2026-06-10 (post dated 2026-03-09)

Definition:

> "Local-first CI means designing your checks to run on your machine first, and then running the same checks remotely. For example: make a script like ./ci.sh and run it both locally and remotely."

Keep the remote run:

> "It is essential that we also still run CI remotely because developers can forget to run it locally first. Indeed, if developers would never make mistakes, we wouldn't use any CI in the first place."

Divergence is the failure mode:

> "It is important that the local checks are the same as the remote checks."

> "However, in practice developers will notice sooner or later that they can ignore what CI does locally because CI will pass remotely anyway. At that point local-first CI becomes extra overhead without any benefit."

Speed and flow:

> "developers tend to have much more powerful machines than their CI workers. For example, GitHub Actions' runners currently offer only 4 vCPUs and 16 GB RAM, considerably less than a typical developer machine."

> "We know that developers tend to switch context instead of waiting for CI to finish remotely. The threshold for how fast your CI has to be to avoid context switching is extremely fast, so just about no CI system is fast enough to avoid it."

Reproducibility:

> "When remote CI 'just' runs ./ci.sh, you can run the same thing locally and often see the same failure locally. You can then fix it locally until ./ci.sh passes, and only then push."

What goes wrong with a naive shared script (verbatim list):

> "Different dependency versions: CI uses gcc 14, which accepts a flag that your local gcc 15 doesn't. Missing dependencies: CI has jq pre-installed but you don't. Different operating systems: CI runs on Linux but you develop on macOS, and sed -i behaves differently. Implicit build state: CI starts clean and builds fine. Your local build fails because of stale object files from a previous build. Dirty working tree: CI checks out a clean tree. You have a local .env file that causes the tests to fail. Different shell environment: CI runs bash, but you run zsh locally. Secrets and credentials: CI has a secret token injected. You don't have it locally."

(The post's proposed fix for the divergence list is Nix — "I usually recommend running nix flake check instead of ./ci.sh"; vendor-specific, noted but not load-bearing here.)

Vendor lock-in:

> "When your CI is a command that runs the same way locally and remotely, the CI provider becomes interchangeable. Your build definition lives in your project, not in your provider's configuration format."

---

## Source 6 — GitHub: Scripts to Rule Them All

- URL: https://github.com/github/scripts-to-rule-them-all (README fetched via raw.githubusercontent.com, master)
- Retrieved: 2026-06-10

The normalization idea:

> "If your scripts are normalized by name across all of your projects, your contributors only need to know the pattern, not a deep knowledge of the application. This means they can jump into a project and make contributions without first learning how to bootstrap the project or how to get its tests to run."

Composability:

> "Each of these scripts is responsible for a unit of work. This way they can be called from other scripts."

Fail-fast ordering inside the test entry point:

> "Linting (i.e. rubocop, jshint, pmd, etc.) can also be considered a form of testing. These tend to run faster than tests, so put them towards the beginning of a script/test so it fails faster if there's a linting problem."

CI calls the same script developers call:

> "script/cibuild is used for your continuous integration server. This script is typically only called from your CI server. You should set up any specific things for your environment here before your tests are run. Your test are run simply by calling script/test."

> "script/test should be called from script/cibuild, so it should handle setting up the application appropriately based on the environment."

Also defines `script/bootstrap` ("used solely for fulfilling dependencies of the project") and `script/setup`/`script/update` for clone-time and post-pull state.
