# Research capture: Vendored & License-Isolated Dependency CI

Topic: building/testing a vendored GPL-2.0 engine separately from MIT framework code; license firewalls in CI (process-separation requirements, symbol/link-graph checks, SPDX header lint, REUSE compliance jobs); SBOM generation placement; per-artifact license manifests.
All sources fetched with scrapling on 2026-06-10.

---

## Source 1: GNU GPL FAQ (Free Software Foundation)

- URL: https://www.gnu.org/licenses/gpl-faq.html
- Retrieved: 2026-06-10

Relevant passages:

### #MereAggregation — separate programs vs one program

> An "aggregate" consists of a number of separate programs, distributed together on the same CD-ROM or other media. The GPL permits you to create and distribute an aggregate, even when the licenses of the other software are nonfree or GPL-incompatible. The only condition is that you cannot release the aggregate under a license that prohibits users from exercising rights that each program's individual license would grant them.
>
> Where's the line between two separate programs, and one program with two parts? This is a legal question, which ultimately judges will decide. We believe that a proper criterion depends both on the mechanism of communication (exec, pipes, rpc, function calls within a shared address space, etc.) and the semantics of the communication (what kinds of information are interchanged).
>
> If the modules are included in the same executable file, they are definitely combined in one program. If modules are designed to run linked together in a shared address space, that almost surely means combining them into one program.
>
> By contrast, pipes, sockets and command-line arguments are communication mechanisms normally used between two separate programs. So when they are used for communication, the modules normally are separate programs. But if the semantics of the communication are intimate enough, exchanging complex internal data structures, that too could be a basis to consider the two parts as combined into a larger program.

### #GPLPlugins — fork/exec, intimate communication, shared memory

> It depends on how the main program invokes its plug-ins. If the main program uses fork and exec to invoke plug-ins, and they establish intimate communication by sharing complex data structures, or shipping complex data structures back and forth, that can make them one single combined program. A main program that uses simple fork and exec to invoke plug-ins and does not establish intimate communication between them results in the plug-ins being a separate program.
>
> If the main program dynamically links plug-ins, and they make function calls to each other and share data structures, we believe they form a single combined program, which must be treated as an extension of both the main program and the plug-ins. [...]
>
> Using shared memory to communicate with complex data structures is pretty much equivalent to dynamic linking.

### #NFUseGPLPlugins — nonfree program loading a GPL plug-in

> If they form a single combined program then the main program must be released under the GPL or a GPL-compatible free software license, and the terms of the GPL must be followed when the main program is distributed for use with these plug-ins. However, if they are separate works then the license of the plug-in makes no requirements about the main program.

### #GPLInProprietarySystem — arms-length communication and form

> You cannot incorporate GPL-covered software in a proprietary system. [...] However, in many cases you can distribute the GPL-covered software alongside your proprietary system. To do this validly, you must make sure that the free and nonfree programs communicate at arms length, that they are not combined in a way that would make them effectively a single program.
>
> The difference between this and "incorporating" the GPL-covered software is partly a matter of substance and partly form. The substantive part is this: if the two programs are combined so that they become effectively two parts of one program, then you can't treat them as two separate programs. So the GPL has to cover the whole thing.
>
> If the two programs remain well separated, like the compiler and the kernel, or like an editor and a shell, then you can treat them as two separate programs—but you have to do it properly. The issue is simply one of form: how you describe what you are doing. [...] Because we want to make sure the users clearly understand the free status of the GPL-covered software in the collection.
>
> If people were to distribute GPL-covered software calling it "part of" a system that users know is partly proprietary, users might be uncertain of their rights regarding the GPL-covered software. But if they know that what they have received is a free program plus another program, side by side, their rights will be clear.

---

## Source 2: REUSE Specification, Version 3.3 (FSFE)

- URL: https://reuse.software/spec-3.3/
- Retrieved: 2026-06-10
- Spec date: 2024-11-14. Implements RFC 2119 requirement levels.

Relevant passages:

> The goal of the specification is to have comprehensive, unambiguous, human- and machine-readable copyright and licensing information for each individual file in a project. Ideally this information is embedded into every file, so that the information is preserved when the file is copied and reused by third parties.

License Files:

> A Project MUST include a License File for every license under which Covered Files are licensed.
>
> Each License File MUST be placed in the `LICENSES/` directory in the root of the Project. The name of the License File MUST be the SPDX License Identifier of the license followed by an appropriate file extension (example: `LICENSES/GPL-3.0-or-later.txt`).
>
> A Project MUST NOT include License Files for licenses under which none of the files in the Project are licensed.
>
> You MAY include `COPYING` or `LICENSE` files in your project for compliance with other standards, conventions, or tools. [...] These files are ignored by the REUSE Tool.

Licensing Information per file:

> Each Covered File MUST have Licensing Information associated with it. You can associate Licensing Information with a file in the following ways: Comment headers / REUSE.toml / DEP5 (deprecated). [...] Comment headers are the RECOMMENDED method.
>
> The comment header MUST contain one or more Copyright Notices and one or more `SPDX-License-Identifier` tag-value pairs. [...] The `SPDX-License-Identifier` tag MUST be followed by a valid SPDX License Expression describing the licensing of the file.

REUSE.toml for bulk/vendored directories:

> Licensing Information MAY be associated with a file through a `REUSE.toml` file [...]. The intended use case of this method is large directories where including a comment header in each file (or in `.license` companion files) is impossible or undesirable.
>
> A `REUSE.toml` file MAY be located in any directory, and can cover files that are within its directory or deeper. You MAY have multiple `REUSE.toml` files in different directories.

Precedence (`precedence` key per `[[annotations]]` table): `closest` (default — in-file info wins, TOML is fallback), `aggregate` (TOML info always associated, plus closest), `override` (TOML wins, in-file info ignored).

Covered-file exceptions include: License Files in `LICENSES/`; `COPYING`/`LICENSE`/`LICENCE` files; VCS files and VCS-ignored files; submodules and Meson subprojects ("Each submodule and Meson subproject is understood as a separate Project"); `.reuse/`; symlinks and zero-byte files; SPDX documents (example: `sbom.spdx.json`).

---

## Source 3: REUSE — Help for developers (CI/CD integration)

- URL: https://reuse.software/dev/
- Retrieved: 2026-06-10

Relevant passages:

> The REUSE tool assists with achieving and confirming REUSE compliance. It downloads the full license texts, adds copyright and license information to file headers, and contains a linter to identify problems. Eventually, you can generate a software bill of materials.

Pre-commit hook:

> You can automatically run `reuse lint` on every commit as a pre-commit hook for Git. [...] Now, every time you commit, `reuse lint` is run in the background, and will prevent your commit from going through if there was an error.

CI/CD:

> REUSE can be easily integrated into your existing CI/CD processes to continuously test your repository and its changes for REUSE compliance. The FSFE offers a Docker image which can be used in numerous CI solutions.

GitHub Actions snippet (`.github/workflows/reuse.yaml`):

```yaml
name: REUSE compliance check
on: [push, pull_request]
jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v5
      - name: REUSE Compliance Check
        uses: fsfe/reuse-action@v6
```

Equivalent snippets given for GitLab CI (`image: fsfe/reuse:latest`, `script: - reuse lint`), Drone/Woodpecker, Forgejo Actions, Travis. REUSE API offers a live compliance badge + JSON status for READMEs.

---

## Source 4: OSS Review Toolkit (ORT) docs — Introduction + License Handling guide

- URLs: https://oss-review-toolkit.org/ort/docs/intro and https://oss-review-toolkit.org/ort/docs/guides/license-handling
- Retrieved: 2026-06-10

Relevant passages (Introduction):

> The OSS Review Toolkit (ORT) is a FOSS policy automation and orchestration toolkit [...]. You can use it to: Generate CycloneDX, SPDX SBOMs, or custom FOSS attribution documentation for your software project; Automate your FOSS policy using risk-based Policy as Code to do licensing, security vulnerability, InnerSource and engineering standards checks for your software project and its dependencies [...]
>
> ORT can be used as a library (for programmatic use), via a command line interface (for scripted use), or via its CI integrations.

Pipeline tools:

> Analyzer - determines the dependencies of projects and their metadata, abstracting which package managers or build systems are actually being used.
> Scanner - uses configured source code scanners to detect license / copyright findings, abstracting the type of scanner.
> Evaluator - evaluates custom policy rules along with custom license classifications against the data gathered in preceding stages and returns a list of policy violations, e.g. to flag license findings.
> Reporter - presents results in various formats such as visual reports, Open Source notices or Bill-Of-Materials (BOMs) to easily identify dependencies, licenses, copyrights or policy rule violations.

Relevant passages (License Handling guide):

> [Declared license] is the license the author of the package claims or intends the package to be licensed under; the license that is "visible from the outside". [...] There are so-called "envelope cases" where the license visible from the outside (on the envelope) does not match what is inside the envelope (i.e. in the source code). For example, a package might have declared itself to be licensed under the MIT license, but in the source code a file might contain a BSD-3-Clause license header.
>
> Detected licenses are those licenses that are detected via an ORT scanner implementation by looking at the contents of all source code files belonging to a package, in particular at the contents of license files or copyright headers in source code files. Detected licenses complement the picture created by declared license by revealing envelope cases where the declared and detected licenses do not match.
>
> The concluded license is manually created via a curation. In cases where the union of declared and detected licenses is wrong [...] the concluded license can be used to set which licenses actually match reality. [...] The effective license finally is the one that takes effect for the package, taking into account any project-specific context like making a license choice in case of dual-licensing. This is the license that should primarily be used in ORT's evaluator rules.
>
> Curating licenses via a concluded license is somewhat of a "sledgehammer" method as it overrides any declared and detected licenses. [...] There is a risk that a newer package version introduces new licenses, which would go unnoticed with a concluded license that blindly overrides everything. That is why in such scenarios, a license finding curation as part of a package configuration is the better option [...] new / changed licenses will not go unnoticed.

---

## Source 5: Generating SBOMs with SPDX at Microsoft (Engineering@Microsoft blog, Adrian Diglio, 2021-10-13)

- URL: https://devblogs.microsoft.com/engineering-at-microsoft/generating-software-bills-of-materials-sboms-with-spdx-at-microsoft/
- Retrieved: 2026-06-10

Relevant passages:

> [Microsoft chose to] use Software Package Data Exchange (SPDX) for all SBOMs we generate [...] output JSON files in the ISO/IEC 5962:2021 standard SPDX 2.2.1 format.

NTIA minimum fields mapped to SPDX 2.2.1: Supplier Name → Package Supplier; Component Name → Package Name; Version → Package Version; Other Unique Identifiers → Package SPDX Identifier; Dependency Relationship → Relationship; Author of SBOM Data → Creator; Timestamp → Created.

> While supplier name, package version, package checksum, and relationship fields are optional in SPDX, we are making them mandatory for Microsoft products.

Rollout / placement:

> Design tooling to automate SBOM generation at build time. Produce SBOMs for all official builds. [...] Leverage existing CI/CD capabilities to intelligently inject our SBOM generation tool into build pipelines, aspiring to have SBOM generation "on by default."

Per-artifact manifest placement:

> Our tool also automates digitally signing each SBOM to protect its integrity and then creates a new folder at the root of the build drop called _manifest; this is where the SPDX JSON file is stored.

Build provenance + release validation:

> At the start of a build, the build service creates a session token that includes claims describing the build (e.g., source code commit ID, build ID, the repository URL) [...] The build service creates a catalog file with a signature that attests that the hash of the SBOM came from the build described by the claims in the sessions token.
>
> One key scenario that we've added is the ability to validate the hashes of all files listed in the SBOM against the hashes of the build drop itself and validate that the digital signature on the SBOM is the trusted signature from Microsoft. If our SBOM validation tool detects a hash mismatch or incorrect signature, our SBOM validation tool will block the deployment. This ensures that nothing was tampered with between build and release.

---

## Source 6: SPDX — Handling License Info (Linux Foundation / SPDX project)

- URL: https://spdx.dev/learn/handling-license-info/
- Retrieved: 2026-06-10

Relevant passages:

> Use SPDX short-form identifiers to communicate license information in a simple, efficient, portable and machine-readable manner. [...] Needs only one new comment line per file.
>
> SPDX IDs are human-readable and machine-readable. Gathering license information across your project files can start to become as easy as running grep.
>
> SPDX IDs make code reuse easier. If your project only has license info in a top-level LICENSE.txt file, it can be harder for others to reuse your code. Downstream recipients may not know what license applies when a file leaves your repo. An SPDX ID is located within each source code or documentation file, and follows that file into downstream projects, making license compliance easier.
>
> SPDX IDs can be adopted gradually. You can start adding SPDX IDs to new files without changing anything already present in your codebase.

License expressions:

> If 2 or more licenses apply to a file, use an SPDX license expression. It is a composite expression constructed using parentheses, AND / OR operators, and the WITH operator for license exceptions.
>
> Saying "this file is MPL/MIT" is ambiguous [...]. Saying `MPL-2.0 AND MIT` or `MPL-2.0 OR MIT` specifies precisely whether the licensee must comply with both licenses, or either license, when redistributing the file.

GNU license suffixes:

> For GNU licenses, do not use just the bare license ID, such as "GPL-2.0". Instead, always use either the suffix "-only" or the suffix "-or-later" with GNU licenses.
>
> `// SPDX-License-Identifier: GPL-2.0-only` — The file is under the GNU General Public License version 2.0. [...] `// SPDX-License-Identifier: GPL-2.0-or-later` — allows recipients to use the file under the GPL v2.0, or any later version of the GPL published by the FSF.

Adopters cited: Linux kernel, Zephyr, U-Boot, Hyperledger; the FSFE REUSE initiative recommends SPDX short-form identifiers per source file.
