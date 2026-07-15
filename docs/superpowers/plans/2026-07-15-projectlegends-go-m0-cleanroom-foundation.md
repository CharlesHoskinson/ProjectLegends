# ProjectLegends Go M0 Clean-Room Foundation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Establish the enforceable three-repository clean-room boundary, admit the Apache-2.0 policy set, prove contaminated artifacts fail closed, and bootstrap the independent Go repository with provenance and quality gates.

**Architecture:** A sponsor-administered private reference repository may publish only through a protected exchange repository. The exchange produces deterministic, content-addressed policy releases. A separately staffed implementation repository consumes one release digest, independently implements its checks in Go, and never mounts or contacts a denied reference source.

**Tech Stack:** GitHub organization teams and repository rulesets; Git signed commits and tags; Go 1.25.12 minimum with Go 1.26.5 primary toolchain; Go standard library; JSON Schema 2020-12 as an interchange contract; GitHub Actions pinned by commit SHA; SHA-256 content addressing.

<!--
SPDX-License-Identifier: Apache-2.0
Copyright 2026 Charles Hoskinson and Contributors
-->

## Global Constraints

- This file is a candidate planning artifact in the legacy repository. No implementation worker may execute this copy. A specification custodian must first scan, review, and admit a byte-identical copy through the exchange process.
- Create and work in three distinct clones. Never add exchange or Go implementation source beneath `C:\ProjectLegends`.
- Use the exact GitHub organization `ProjectLegendsCleanroom` and repositories `projectlegends-reference`, `projectlegends-exchange`, and `projectlegends-go`. The sponsor must reserve the organization before any module is published.
- The public Go module path is fixed once as `github.com/ProjectLegendsCleanroom/projectlegends-go`. The exchange tooling module is `github.com/ProjectLegendsCleanroom/projectlegends-exchange`.
- A human or agent identity may not belong to both the `reference` and `implementation` teams. Sessions, credentials, working directories, caches, issue access, and agent context are role-scoped as well.
- The current public legacy repository remains a denied source. The private reference mirror is the controlled oracle workspace; making a mirror private does not erase prior public availability, so implementation contributors require explicit non-exposure review and attestation.
- Exchange and implementation files are Apache-2.0 unless a manifest records an approved generated fact or sponsor-owned fixture. Source, workflow, script, Markdown specification, and policy files carry an Apache-2.0 SPDX marker in their language-appropriate comment syntax.
- Download no DOS package, firmware, game media, emulator binary, model weight, or model runtime during M0. Only metadata, policies, hashes, schemas, and synthetic negative fixtures enter either repository.
- Go production and checking packages use only the standard library in M0. A tool downloaded by CI must be pinned, checksummed by the Go checksum database or an admitted artifact digest, and recorded in `tools/tools.lock.json`.
- The M0 race job may use the Go toolchain's required race-instrumentation build mode; release artifacts remain free of cgo. Before M1, admit a quality-policy correction that distinguishes race instrumentation from the blanket `CGO_ENABLED=0` product-build rule, because the Go race detector cannot run under that blanket setting.
- CI sets `GOFLAGS=-mod=readonly` and `GOWORK=off`. Protected Go modules contain no `replace` directive; preflight rejects one before any build or test command.
- Every decoder is closed: unknown fields, duplicate JSON object keys, trailing JSON values, unknown schema versions, invalid UTF-8, missing provenance, and empty mandatory selections fail.
- Check commands emit `plgo.check-result/1` JSON, print the selected item count, and use exit code 0 for `pass` or an explicitly allowed `not-applicable`, 1 for a policy rejection, and 2 for an operational failure.
- No workflow uses retries, `continue-on-error`, floating action tags, unpinned containers, report-only vulnerability exits, or shell constructs that erase a failing status.
- All commits on protected branches are signed. Each task ends with a signed, role-appropriate commit after its listed verification succeeds.
- Stop immediately and follow the taint procedure if a denied source, source-derived identifier inventory, raw oracle output, or contaminated agent context appears in an exchange or implementation workspace.

## Scope and Requirement IDs

| ID | M0 outcome |
|---|---|
| `PLGO-CR-M0-001` | Three repositories and role-scoped access groups exist |
| `PLGO-CR-M0-002` | Reference and implementation identities are disjoint |
| `PLGO-CR-M0-003` | Exchange and implementation licensing is Apache-2.0 with enforced SPDX policy |
| `PLGO-CR-M0-004` | Every admitted artifact has closed, digest-bound provenance |
| `PLGO-CR-M0-005` | The admission pipeline rejects a deliberately contaminated artifact |
| `PLGO-CR-M0-006` | Contributor non-exposure attestations and signed commits are mandatory |
| `PLGO-CR-M0-007` | Corpus classification and acquisition policies are admitted without binaries |
| `PLGO-CR-M0-008` | AI evaluator isolation and disclosure policies are admitted without weights |
| `PLGO-CR-M0-009` | The implementation pins one immutable exchange release digest |
| `PLGO-CR-M0-010` | Local and CI preflight fail on missing, empty, stale, or malformed evidence |
| `PLGO-CR-M0-011` | Taint response freezes merges and preserves incident history |
| `PLGO-CR-M0-012` | Sponsor and legal/provenance reviewer sign the operating protocol and M0 evidence |

M1 emulator packages, conformance programs, DOS downloads, prepared images, deterministic game replays, `plgo-ai/1`, and local-model execution are outside this plan.

## Target Repository Map

The dedicated organization is an enforcement requirement, not branding: the legacy remote is currently owned by a GitHub `User`, while M0 requires closed teams and repository-specific role grants that personal repositories cannot provide.

### `projectlegends-reference`

This private mirror contains the legacy reference material and reference-only experiment tooling. M0 changes only host settings and `CLEANROOM-REFERENCE.md`; no file from this repository is copied directly into the Go repository.

### `projectlegends-exchange`

~~~text
projectlegends-exchange/
  .github/
    CODEOWNERS
    ISSUE_TEMPLATE/implementation-question.yml
    pull_request_template.md
    workflows/admission.yml
  cmd/
    admissioncheck/main.go
    exchangerelease/main.go
  governance/
    repositories.json
    roles.json
    signoffs/legal-provenance.json
    signoffs/sponsor.json
  internal/
    admission/check.go
    admission/check_test.go
    admission/decode.go
    admission/decode_test.go
    admission/filesystem.go
    admission/scanner.go
    admission/testdata/contaminated.hex
    release/archive.go
    release/archive_test.go
  manifests/
    evidence/
    plans/
    policies/
    requirements/
    schemas/
    specs/
  evidence/m0/
    m0-acceptance.json
    legal-provenance-signoff.json
    sponsor-signoff.json
  policies/
    artifact-admission.md
    contributor-disclosure.md
    corpus-acquisition.md
    corpus-classification.md
    evaluator-disclosure.md
    forbidden-patterns.json
    operating-protocol.md
    taint-response.md
  plans/2026-07-15-projectlegends-go-m0-cleanroom-foundation.md
  requirements/m0.json
  schemas/
    admission-report.schema.json
    artifact-manifest.schema.json
    check-result.schema.json
    contributor-attestation.schema.json
    release.schema.json
    repository-map.schema.json
    role-registry.schema.json
    signoff.schema.json
  specs/
    2026-07-15-projectlegends-go-cleanroom-program-design.md
    2026-07-15-projectlegends-go-conformance-vectors.md
    2026-07-15-projectlegends-go-dos-corpus-and-reference-agent.md
    2026-07-15-projectlegends-go-headless-nucleus-contract.md
    2026-07-15-projectlegends-go-quality-gates.md
  tools/tools.lock.json
  .gitattributes
  .gitignore
  CONTRIBUTING.md
  LICENSE
  NOTICE
  README.md
  SECURITY.md
  go.mod
~~~

`cmd/exchangerelease` writes `dist/projectlegends-exchange-m0-foundation-2026-07-15.1.tar.gz`; `dist/` is ignored and never committed. The archive contains only `LICENSE`, `NOTICE`, generated `release.json`, generated `admission-report.json`, generated `SHA256SUMS`, and the admitted `governance`, `manifests`, `plans`, `policies`, `requirements`, `schemas`, and `specs` trees. Tool source, later M0 evidence, and GitHub workflow files are not implementation inputs.

### `projectlegends-go`

~~~text
projectlegends-go/
  .cleanroom/
    contributors/implementation-bootstrap.json
    exchange.lock.json
    milestone.json
  .github/
    CODEOWNERS
    pull_request_template.md
    workflows/pr.yml
  cmd/
    coveragegate/main.go
    preflight/main.go
    provenancecheck/main.go
  internal/
    checkresult/result.go
    coveragegate/gate.go
    coveragegate/gate_test.go
    preflight/run.go
    preflight/run_test.go
    provenance/check.go
    provenance/check_test.go
    provenance/decode.go
    provenance/decode_test.go
  policy/forbidden-patterns.json
  tools/tools.lock.json
  .gitattributes
  .gitignore
  CONTRIBUTING.md
  LICENSE
  NOTICE
  README.md
  SECURITY.md
  go.mod
  go.sum
~~~

## Stable M0 Interfaces

The exchange and implementation repositories independently implement these wire shapes; they do not share a Go package.

~~~go
type CheckResult struct {
	Schema   string    `json:"schema"`
	Check    string    `json:"check"`
	Selected int       `json:"selected"`
	Result   string    `json:"result"`
	Reason   string    `json:"reason,omitempty"`
	Findings []Finding `json:"findings"`
}

type Finding struct {
	Code    string `json:"code"`
	Path    string `json:"path,omitempty"`
	Message string `json:"message"`
}
~~~

`Schema` is always `plgo.check-result/1`. `Result` is exactly `pass`, `fail`, or `not-applicable`. A result with `Selected == 0` is valid only when the M0 registry contains an exact `(check, milestone, reason)` entry; all other zero selections fail with `PLGO-GATE-001`.

Admission findings use stable codes:

| Code | Meaning |
|---|---|
| `PLGO-ADM-001` | malformed or unknown schema |
| `PLGO-ADM-002` | unknown or duplicate JSON field |
| `PLGO-ADM-003` | manifest absent or not one-to-one with its artifact |
| `PLGO-ADM-004` | byte length or SHA-256 mismatch |
| `PLGO-ADM-005` | author or reviewer identity not authorized |
| `PLGO-ADM-006` | disposition is not `admitted` |
| `PLGO-ADM-007` | illegal or non-canonical path |
| `PLGO-ADM-008` | symlink, hard-link declaration, or special file |
| `PLGO-ADM-009` | file exceeds the 64 MiB limit |
| `PLGO-ADM-010` | archive, encrypted, or compressed artifact |
| `PLGO-ADM-011` | executable, submodule, or Git LFS pointer |
| `PLGO-ADM-012` | license, NOTICE, or SPDX violation |
| `PLGO-ADM-013` | host or reference source-path leakage |
| `PLGO-ADM-014` | forbidden content match |
| `PLGO-ADM-015` | mandatory selection is empty |

---

### Task 1: Establish the Host and Identity Boundary

**Execution role:** Sponsor repository administrator, in a host-admin session that is never reused by an implementation worker.

**Requirements:** `PLGO-CR-M0-001`, `PLGO-CR-M0-002`

**Files:**

- Create: private repositories listed in the target map
- Create later in exchange: `governance/repositories.json`
- Create later in exchange: `governance/roles.json`
- Create in reference: `CLEANROOM-REFERENCE.md`

- [ ] **Step 1: Record the initial failing topology probe**

Run before creating anything:

~~~powershell
$ErrorActionPreference = 'Stop'
$org = 'ProjectLegendsCleanroom'
$repos = 'projectlegends-reference','projectlegends-exchange','projectlegends-go'
$missing = 0
foreach ($repo in $repos) {
  gh repo view "$org/$repo" --json nameWithOwner 2>$null
  if ($LASTEXITCODE -ne 0) { $missing++ }
}
if ($missing -ne 3) { throw "Expected three absent repositories, observed $missing" }
~~~

Expected: the probe succeeds only because all three repositories are absent. If any name already exists, stop and have the sponsor determine ownership before continuing.

- [ ] **Step 2: Create the organization, repositories, and closed teams**

Create the GitHub organization `ProjectLegendsCleanroom` under sponsor control. Require two-factor authentication and prevent repository creation by ordinary members. Then run:

~~~powershell
$org = 'ProjectLegendsCleanroom'
gh repo create "$org/projectlegends-reference" --private --disable-issues --disable-wiki
gh repo create "$org/projectlegends-exchange" --private --disable-wiki
gh repo create "$org/projectlegends-go" --private --disable-wiki

$teams = 'sponsors','reference','specification-custodians','implementation','independent-verifiers','legal-provenance'
foreach ($team in $teams) {
  gh api --method POST "/orgs/$org/teams" -f "name=$team" -f 'privacy=closed'
}
~~~

The sponsor adds reviewed identities directly to the appropriate team. No synthetic identity or shared service account satisfies this step.

- [ ] **Step 3: Set repository access**

Use GitHub repository permissions as follows:

| Repository | Admin | Maintain/write | Read |
|---|---|---|---|
| reference | sponsors | reference | legal-provenance |
| exchange | sponsors | specification-custodians, legal-provenance | implementation, independent-verifiers |
| go | sponsors | implementation | independent-verifiers, legal-provenance |

The `reference` team receives no access to `projectlegends-go`; the `implementation` team receives no access to `projectlegends-reference`. Disable forks on all private repositories.

- [ ] **Step 4: Mirror the legacy reference only from the reference-admin session**

Mirror the sponsor-designated legacy remote into `projectlegends-reference`. Do not disclose the mirror source or clone path in implementation evidence. Add `CLEANROOM-REFERENCE.md` stating that raw outputs remain reference-side and publication occurs only through exchange admission.

- [ ] **Step 5: Prove disjoint membership and repository visibility**

~~~powershell
$org = 'ProjectLegendsCleanroom'
$reference = @(gh api "/orgs/$org/teams/reference/members" --paginate --jq '.[].login')
$implementation = @(gh api "/orgs/$org/teams/implementation/members" --paginate --jq '.[].login')
$overlap = @($reference | Where-Object { $implementation -contains $_ })
if ($overlap.Count -ne 0) { throw "Reference/implementation overlap detected" }

foreach ($repo in 'projectlegends-reference','projectlegends-exchange','projectlegends-go') {
  $visibility = gh repo view "$org/$repo" --json visibility --jq '.visibility'
  if ($visibility -ne 'PRIVATE') { throw "$repo is not private" }
}
~~~

Expected: zero overlapping logins and all three repositories report `PRIVATE`.

- [ ] **Step 6: Capture sanitized host evidence**

Record repository node IDs, visibility, ruleset IDs, team slugs, member-key fingerprints, and the zero-overlap result. Do not record personal email, denied clone URLs, or access tokens. Give this evidence bundle to the specification custodian for Task 2.

### Task 2: Bootstrap the Apache-2.0 Exchange Repository

**Execution role:** Specification custodian, in a fresh exchange-only clone.

**Requirements:** `PLGO-CR-M0-003`

**Files:**

- Create: `LICENSE`, `NOTICE`, `README.md`, `SECURITY.md`, `CONTRIBUTING.md`
- Create: `.gitattributes`, `.gitignore`, `go.mod`, `tools/tools.lock.json`
- Create: `governance/repositories.json`, `governance/roles.json`
- Create: `.github/CODEOWNERS`, `.github/pull_request_template.md`, `.github/ISSUE_TEMPLATE/implementation-question.yml`

- [ ] **Step 1: Initialize the repository and demonstrate the missing-license failure**

~~~powershell
git clone https://github.com/ProjectLegendsCleanroom/projectlegends-exchange.git
Set-Location projectlegends-exchange
git switch -c m0/exchange-bootstrap
if (Test-Path LICENSE) { throw 'LICENSE unexpectedly exists' }
~~~

Expected: `LICENSE` is absent.

- [ ] **Step 2: Add the canonical Apache license and NOTICE**

Download `https://www.apache.org/licenses/LICENSE-2.0.txt` as raw bytes. Require byte length `11358` and SHA-256 `cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30` before writing `LICENSE`.

Use this NOTICE text exactly:

~~~text
ProjectLegends Go Clean-Room Program
Copyright 2026 Charles Hoskinson and Contributors

This product is developed through the ProjectLegends clean-room program.
Third-party attributions, when admitted, are listed in exchange manifests.
~~~

- [ ] **Step 3: Add deterministic repository defaults**

`go.mod` is:

~~~go
module github.com/ProjectLegendsCleanroom/projectlegends-exchange

go 1.25.0

toolchain go1.26.5
~~~

`.gitattributes` enforces LF text and rejects accidental binary normalization:

~~~gitattributes
* text=auto eol=lf
*.bin -text
*.hex text eol=lf
~~~

`.gitignore` contains only:

~~~gitignore
/dist/
/coverage.out
~~~

`tools/tools.lock.json` begins as the closed object `{"schema":"plgo.tools/1","tools":[]}`.

- [ ] **Step 4: Add governance records from Task 1 evidence**

`governance/repositories.json` uses schema `plgo.repositories/1` and records the three exact repository names, visibility, allowed team slugs, denied team slugs, and host ruleset IDs. `governance/roles.json` uses schema `plgo.roles/1` and records key fingerprints, exactly one of `sponsor`, `reference`, `specification-custodian`, `implementation`, `independent-verifier`, `legal-provenance`, or `merge-service` per identity, validity windows, and status. Reject a registry in which any fingerprint has both `reference` and `implementation` roles. A `merge-service` key cannot author or review artifacts.

- [ ] **Step 5: Add ownership and question-channel controls**

`CODEOWNERS` requires `specification-custodians` plus `legal-provenance` for `policies/`, `schemas/`, `manifests/`, `governance/`, `requirements/`, and `specs/`. The implementation-question issue form accepts a requirement ID, externally observable question, motivating admitted artifact digest, and requested clarification. It explicitly rejects source, symbol, file-layout, or implementation advice.

- [ ] **Step 6: Verify and commit**

~~~powershell
$hash = (Get-FileHash LICENSE -Algorithm SHA256).Hash.ToLowerInvariant()
if ($hash -ne 'cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30') { throw 'LICENSE digest mismatch' }
git diff --check
git status --short
git add --all
git commit -S -m 'chore: bootstrap clean-room exchange'
~~~

Expected: only the listed bootstrap files are staged and the signed commit succeeds.

### Task 3: Define Closed Schemas and the Strict Decoder

**Execution role:** Specification custodian or exchange-tooling contributor with no implementation role.

**Requirements:** `PLGO-CR-M0-004`, `PLGO-CR-M0-010`

**Files:**

- Create: all files under `schemas/`
- Create: `internal/admission/decode.go`
- Create: `internal/admission/decode_test.go`

- [ ] **Step 1: Write failing decoder tests**

Tests must cover valid input plus unknown field, duplicate key, trailing value, invalid UTF-8, schema mismatch, malformed SHA-256, non-UTC timestamp, empty reviewer, unknown disposition, and a fingerprint assigned to both source teams.

Use this decoder contract:

~~~go
var (
	ErrSchema       = errors.New("schema violation")
	ErrDuplicateKey = errors.New("duplicate JSON key")
)

func DecodeArtifactManifest(data []byte) (ArtifactManifest, error)
func DecodeRoleRegistry(data []byte) (RoleRegistry, error)
func DecodeCheckResult(data []byte) (CheckResult, error)
~~~

The first red test is `TestDecodeArtifactManifestRejectsUnknownField`; it adds `"unexpected":true` to an otherwise valid manifest and requires `errors.Is(err, ErrSchema)`.

- [ ] **Step 2: Run the red tests**

~~~powershell
go test ./internal/admission -run 'TestDecode' -count=1
~~~

Expected: compilation fails because the decoder API does not exist.

- [ ] **Step 3: Implement duplicate-key detection before typed decoding**

Walk the JSON token stream recursively, maintaining a key set for each object. Then decode a second time with `DisallowUnknownFields` and require EOF:

~~~go
func decodeClosed[T any](data []byte, dst *T) error {
	if !utf8.Valid(data) {
		return fmt.Errorf("%w: invalid UTF-8", ErrSchema)
	}
	if err := rejectDuplicateKeys(data); err != nil {
		return err
	}
	dec := json.NewDecoder(bytes.NewReader(data))
	dec.DisallowUnknownFields()
	if err := dec.Decode(dst); err != nil {
		return fmt.Errorf("%w: %v", ErrSchema, err)
	}
	var extra any
	if err := dec.Decode(&extra); !errors.Is(err, io.EOF) {
		return fmt.Errorf("%w: trailing JSON value", ErrSchema)
	}
	return nil
}
~~~

After structural decoding, validate exact schema identifiers, enums, lowercase hexadecimal hashes, RFC 3339 UTC timestamps with second precision, role separation, required arrays, and cross-field rules.

- [ ] **Step 4: Define `plgo.artifact/1` without recursive manifests**

`artifact-manifest.schema.json` and the Go type require:

~~~go
type ArtifactManifest struct {
	Schema                   string       `json:"schema"`
	ArtifactID               string       `json:"artifact_id"`
	ArtifactType             string       `json:"artifact_type"`
	ArtifactSchemaVersion    int          `json:"artifact_schema_version"`
	ArtifactBytes            int64        `json:"artifact_bytes"`
	ArtifactSHA256           string       `json:"artifact_sha256"`
	License                  string       `json:"license"`
	AuthorRole               string       `json:"author_role"`
	Generation               Generation   `json:"generation"`
	Inputs                   []Input      `json:"inputs"`
	SourceExposure           string       `json:"source_exposure"`
	ContainsDeniedExpression bool         `json:"contains_denied_expression"`
	Review                   Review       `json:"review"`
	Supersedes               []string     `json:"supersedes"`
}

type Generation struct {
	Tool    string   `json:"tool"`
	Version string   `json:"version"`
	Command []string `json:"command"`
}

type Input struct {
	ID        string `json:"id"`
	Bytes     int64  `json:"bytes"`
	SHA256    string `json:"sha256"`
	Ownership string `json:"ownership"`
	License   string `json:"license"`
}

type Review struct {
	Custodian           string `json:"custodian"`
	ProvenanceReviewer  string `json:"provenance_reviewer"`
	Decision            string `json:"decision"`
	DecidedUTC          string `json:"decided_utc"`
}
~~~

Every JSON schema carries `$comment: "SPDX-License-Identifier: Apache-2.0"` and sets `additionalProperties` to `false` at every object level. Manifests are release control metadata and do not require manifests of their own; `SHA256SUMS` and the signed admission report cover them. The checker applies the same non-recursive release-control treatment to the role registry, repository map, signoff records, release manifest, and admission report.

- [ ] **Step 5: Run all schema tests and commit**

~~~powershell
go test ./internal/admission -count=1
git diff --check
git add schemas internal/admission
git commit -S -m 'feat: add closed admission schemas'
~~~

Expected: all decoder tests pass with no third-party module in `go.mod`.

### Task 4: Build the Fail-Closed Admission Checker

**Execution role:** Exchange-tooling contributor.

**Requirements:** `PLGO-CR-M0-004`, `PLGO-CR-M0-005`, `PLGO-CR-M0-010`

**Files:**

- Create: `internal/admission/check.go`, `filesystem.go`, `scanner.go`, `check_test.go`
- Create: `internal/admission/testdata/contaminated.hex`
- Create: `cmd/admissioncheck/main.go`
- Create: `policies/forbidden-patterns.json`

- [ ] **Step 1: Write negative tests before the checker**

Create table tests for every `PLGO-ADM-001` through `PLGO-ADM-015` code. Each test builds an isolated temporary Git repository, commits the candidate tree when Git metadata matters, invokes `admission.Check`, and asserts one exact finding code and path.

The contaminated fixture file contains this single hex line:

~~~text
68747470733a2f2f6769746875622e636f6d2f436861726c6573486f736b696e736f6e2f50726f6a6563744c6567656e6473
~~~

`TestContaminatedFixtureRejected` decodes the line into a temporary Markdown artifact. The repository never stores the decoded denied URL as fixture content.

- [ ] **Step 2: Run the red checker tests**

~~~powershell
go test ./internal/admission -run 'TestCheck|TestContaminated' -count=1
~~~

Expected: compilation fails because `admission.Check` is absent.

- [ ] **Step 3: Implement the checker API and deterministic output**

~~~go
type Options struct {
	Milestone       string
	AuthorizedRoles RoleRegistry
	Forbidden       ForbiddenPolicy
}

func Check(root string, opts Options) (CheckResult, error)
~~~

Walk with `os.Lstat`, sort normalized slash paths by byte order, and inspect both filesystem facts and `git ls-files --stage -z`. Reject symlinks, mode `160000`, mode `100755`, Git LFS pointer headers, files over 64 MiB, and archive or executable magic. Enforce lowercase ASCII letters, digits, hyphen, underscore, slash, and dot within admitted artifact namespaces. Repository support files may additionally use only the exact conventional names `LICENSE`, `NOTICE`, `README.md`, `SECURITY.md`, `CONTRIBUTING.md`, and `.github/CODEOWNERS`. The release builder separately permits root `SHA256SUMS`.

Match forbidden fixed strings and regular expressions from the reviewer-owned policy. Each pattern declares exact approved wording paths; for M0, denied remote wording may appear only in `policies/forbidden-patterns.json`, `policies/operating-protocol.md`, and `plans/2026-07-15-projectlegends-go-m0-cleanroom-foundation.md`. Source files cannot suppress a finding inline. Findings sort by `(code, path, message)`.

- [ ] **Step 4: Enforce one-to-one manifests and authorized review**

Every artifact below `evidence/`, `plans/`, `policies/`, `requirements/`, `schemas/`, and `specs/` has exactly one manifest below the parallel `manifests/` path. Verify bytes and SHA-256, `decision == "admitted"`, `contains_denied_expression == false`, and custodian/provenance-reviewer fingerprints active in `governance/roles.json`. Manifests, the role registry, repository map, and signoff records are release control metadata covered by the signed admission report rather than recursively manifested.

- [ ] **Step 5: Implement the CLI exit contract**

`go run ./cmd/admissioncheck -root . -milestone M0` writes one `plgo.check-result/1` object to stdout. Policy rejection exits 1; filesystem, Git, or parsing failure exits 2. A scan selecting zero artifacts returns `PLGO-ADM-015` and exits 1.

- [ ] **Step 6: Prove both green and contaminated paths**

~~~powershell
go test ./internal/admission -count=1
go test ./internal/admission -run TestContaminatedFixtureRejected -count=1
go run ./cmd/admissioncheck -root . -milestone M0
~~~

Expected: the dedicated negative test proves the contaminated candidate is rejected; the real repository command reports `result:"pass"` with a nonzero selection after Task 5 artifacts exist. Until Task 5, `PLGO-ADM-015` is the expected repository-level result.

- [ ] **Step 7: Commit the checker**

~~~powershell
git add cmd/admissioncheck internal/admission policies/forbidden-patterns.json
git commit -S -m 'feat: reject unadmitted exchange artifacts'
~~~

### Task 5: Admit the Operating, Corpus, and Evaluator Policies

**Execution role:** Specification custodian authors; legal/provenance reviewer approves. Neither role writes Go implementation code.

**Requirements:** `PLGO-CR-M0-003`, `PLGO-CR-M0-007`, `PLGO-CR-M0-008`, `PLGO-CR-M0-011`, `PLGO-CR-M0-012`

**Files:**

- Create: all `policies/*.md` files
- Create: `plans/2026-07-15-projectlegends-go-m0-cleanroom-foundation.md`
- Create: `requirements/m0.json`
- Create: five files under `specs/`
- Create: corresponding files under `manifests/plans/`, `manifests/policies/`, `manifests/requirements/`, `manifests/schemas/`, and `manifests/specs/`

- [ ] **Step 1: Copy only the approved candidate specification bytes**

Use candidate source commit `6255f0219b592e6ef6bb7fc77ee3e13f7abae882`. Export only the five 2026-07-15 Go clean-room specification files listed in the target map. Do not clone or mount the legacy repository in the exchange workspace; the sponsor transfers a checksummed candidate bundle to the custodian.

Transfer this M0 plan as a separately checksummed candidate after its legacy planning commit is protected. The custodian verifies that it contains only process, schema, test, and repository-bootstrap instructions, records its source commit and digest in `manifests/plans/`, and admits the byte-identical exchange copy before an implementation worker uses it.

- [ ] **Step 2: Write the seven policy documents with immutable requirement mappings**

Each policy begins with an Apache-2.0 SPDX comment, policy version 1, owner role, approval role, and the M0 requirement IDs it satisfies. Preserve these decisions exactly:

- `artifact-admission.md`: one-way publication, digest-bound manifests, authorized two-person review, fail-closed dispositions, and no raw oracle output.
- `contributor-disclosure.md`: role separation, prior-exposure statement, signed commits, validity windows, re-attestation after an incident, and removal on denied access.
- `corpus-classification.md`: Classes A through D; no “abandonware” category; public CI and redistribution decisions remain separate.
- `corpus-acquisition.md`: HTTPS allowlists, exact bytes and SHA-256, bounded redirects and extraction, explicit cache path, and no search or mirror substitution.
- `evaluator-disclosure.md`: black-box adapter only, egress off by default, no model reasoning retention, Class D local-only absent written approval, and reports cannot advise implementation structure.
- `operating-protocol.md`: roles, repository topology, allowed channels, question workflow, environment isolation, audit retention, and signoff conditions.
- `taint-response.md`: freeze, preserve, quarantine, identify exposure, obtain reviewer decision, recreate when required, audit, and never rewrite history to conceal the incident.

- [ ] **Step 3: Encode the requirement matrix**

`requirements/m0.json` is a closed `plgo.requirements/1` object containing all twelve IDs, normative source path, verification command, evidence owner, and status `required`. It contains no `complete` status before Task 10.

- [ ] **Step 4: Create and review manifests**

Generate one `plgo.artifact/1` manifest per policy, specification, schema, requirement file, and governance evidence artifact. For the five specifications, record candidate commit `6255f0219b592e6ef6bb7fc77ee3e13f7abae882` as an input identifier without publishing a denied clone URL. Record all generation commands and tool versions. The custodian and provenance reviewer use distinct active fingerprints.

- [ ] **Step 5: Run the admission checker and prove no payload entered**

~~~powershell
go run ./cmd/admissioncheck -root . -milestone M0
$forbiddenExtensions = '.zip','.7z','.rar','.gz','.exe','.com','.rom','.img','.iso','.gguf','.safetensors'
$payloads = Get-ChildItem -Recurse -File | Where-Object { $forbiddenExtensions -contains $_.Extension.ToLowerInvariant() }
if ($payloads.Count -ne 0) { throw 'M0 payload or archive found in exchange' }
~~~

Expected: admission reports a nonzero selected count and `pass`; the payload scan selects zero files.

- [ ] **Step 6: Commit the admitted policy set**

~~~powershell
git add governance manifests plans policies requirements schemas specs
git commit -S -m 'docs: admit clean-room foundation policies'
~~~

- [ ] **Step 7: Sign the operating protocol before release**

After the policy commit is protected, the sponsor and legal/provenance reviewer each create a `plgo.signoff/1` object under `governance/signoffs/`. Each object names its distinct role-key fingerprint, the exact operating-protocol SHA-256, decision `approved`, and an RFC 3339 UTC timestamp. Each signer adds only its signoff record and commits with the matching signing key. The admission checker verifies both identities against `governance/roles.json`.

### Task 6: Produce a Deterministic Exchange Release

**Execution role:** Exchange-tooling contributor builds; independent verifier reproduces.

**Requirements:** `PLGO-CR-M0-004`, `PLGO-CR-M0-009`

**Files:**

- Create: `internal/release/archive.go`, `archive_test.go`
- Create: `cmd/exchangerelease/main.go`
- Generated outside Git: `dist/projectlegends-exchange-m0-foundation-2026-07-15.1.tar.gz`

- [ ] **Step 1: Write a reproducibility test that fails first**

`TestArchiveReproducible` builds the same fixture twice with different source mtimes and directory enumeration orders. Require identical archive bytes and SHA-256. `TestArchiveContents` requires the allowlisted roots and rejects `.github`, `cmd`, `internal`, `go.mod`, `.git`, and `dist`.

- [ ] **Step 2: Run the red release tests**

~~~powershell
go test ./internal/release -count=1
~~~

Expected: compilation fails because the archive builder is absent.

- [ ] **Step 3: Implement canonical tar and gzip output**

Sort slash paths bytewise. Write directories as mode `0755`, regular files as `0644`, uid/gid zero, empty user/group names, and timestamp `2000-01-01T00:00:00Z`. Set gzip name and comment empty, modtime zero, and OS byte 255. Reject links and special files before writing.

Before archiving, run the admission checker and generate `admission-report.json` with schema `plgo.admission-report/1`, the protected source commit, role-registry digest, selected artifact count, sorted admitted artifact IDs and digests, check-result digest, and result `pass`. A finding or zero selected artifacts prevents archive creation. The report and release manifest are release control metadata and do not require recursive manifests.

The builder injects `release.json` after the protected source commit exists:

~~~json
{
  "schema": 1,
  "contract_version": 1,
  "release_id": "m0-foundation-2026-07-15.1",
  "created_utc": "2026-07-15T18:00:00Z",
  "previous_release_sha256": null,
  "case_count": 0,
  "program_count": 0,
  "minimum_runner_version": "0.1.0",
  "admission_commit": "0123456789abcdef0123456789abcdef01234567"
}
~~~

The example commit is test data only. At build time, `admission_commit` is the exact protected exchange commit supplied by `git rev-parse HEAD`. `SHA256SUMS` covers every regular release file except itself and is sorted by path. The archive is generated after that commit, avoiding a self-referential commit hash.

- [ ] **Step 4: Implement and run the release command**

~~~powershell
$commit = git rev-parse HEAD
go run ./cmd/exchangerelease -root . -milestone M0 -release-id m0-foundation-2026-07-15.1 -created-utc 2026-07-15T18:00:00Z -admission-commit $commit -output dist/projectlegends-exchange-m0-foundation-2026-07-15.1.tar.gz
Get-FileHash dist/projectlegends-exchange-m0-foundation-2026-07-15.1.tar.gz -Algorithm SHA256
~~~

Expected: the command first runs admission, emits a nonzero selected count, and prints one archive SHA-256.

- [ ] **Step 5: Reproduce on an independent builder**

The independent verifier checks out the same commit into a fresh environment, runs the exact command, and compares archive byte length and SHA-256. Any mismatch blocks release.

- [ ] **Step 6: Commit tooling, then publish the external release artifact**

~~~powershell
git add cmd/exchangerelease internal/release
git commit -S -m 'feat: build deterministic exchange releases'
~~~

Rebuild from the new protected commit, obtain the two matching digests, create a signed tag `exchange-m0-foundation-2026-07-15.1`, and attach the archive plus detached signatures. Do not commit `dist/`.

### Task 7: Bootstrap the Independent Go Repository and Provenance Gate

**Execution role:** Implementation contributor whose identity and environment passed the operating protocol. Start from a fresh implementation-only session.

**Requirements:** `PLGO-CR-M0-003`, `PLGO-CR-M0-006`, `PLGO-CR-M0-009`, `PLGO-CR-M0-010`

**Files:**

- Create: root license, documentation, module, and `.cleanroom/` files from the target map
- Create: `internal/checkresult/result.go`
- Create: `internal/provenance/check.go`, `decode.go`, and tests
- Create: `cmd/provenancecheck/main.go`
- Import: `policy/forbidden-patterns.json` from the pinned exchange release

- [ ] **Step 1: Verify the workspace has no reference remote or mount**

~~~powershell
git clone https://github.com/ProjectLegendsCleanroom/projectlegends-go.git
Set-Location projectlegends-go
git switch -c m0/provenance-bootstrap
$remotes = git remote -v
if ($remotes -match 'CharlesHoskinson/ProjectLegends|dosbox-x') { throw 'Denied remote detected' }
$deniedMounts = Get-ChildItem Env: | Where-Object { $_.Value -match 'CharlesHoskinson[\\/]+ProjectLegends(?:\.git)?|projectlegends-reference|dosbox-x' }
if ($deniedMounts.Count -ne 0) { throw 'Denied path leaked through environment' }
~~~

Expected: only the new implementation origin is present and no denied path is in the environment.

- [ ] **Step 2: Add Apache licensing, fixed module identity, and clean-room locks**

Use the same verified `LICENSE` bytes and NOTICE basis as Task 2. `go.mod` is:

~~~go
module github.com/ProjectLegendsCleanroom/projectlegends-go

go 1.25.0

toolchain go1.26.5
~~~

Keep an empty tracked `go.sum` until an admitted tool or module creates entries. `milestone.json` is `{"schema":"plgo.milestone/1","milestone":"M0","quality_policy":1}`.

`exchange.lock.json` is generated from the admitted archive and records schema `plgo.exchange-lock/1`, release ID, exact archive byte length and SHA-256, admission commit, detached-signature identities, and an `imports` array. The only M0 imported file is `policies/forbidden-patterns.json`, copied to `policy/forbidden-patterns.json` with exact byte length and SHA-256.

- [ ] **Step 3: Commit the first non-exposure attestation with the bootstrap code**

`.cleanroom/contributors/implementation-bootstrap.json` is a closed `plgo.contributor/1` record with the contributor signing-key fingerprint, role `implementation`, `reference_exposure:"none"`, denied-source acknowledgement, training and agent-context disclosure, validity window, and reviewer fingerprint. It contains no personal email. The first repository commit includes this record and is signed by the same key.

- [ ] **Step 4: Write failing provenance tests**

Tests create temporary Git repositories and require exact failures for:

- missing or malformed exchange lock;
- wrong archive or imported-file digest;
- unknown lock field;
- missing, expired, or wrong-role contributor attestation;
- unsigned commit or unauthorized signing fingerprint;
- altered LICENSE or NOTICE;
- missing SPDX header;
- denied import, remote, URL, path, or content;
- any `replace` directive or unexpected workspace file;
- generated file without admitted input and generator identity;
- zero tracked source/specification files.

Run:

~~~powershell
go test ./internal/provenance -count=1
~~~

Expected: compilation fails because the checker is absent.

- [ ] **Step 5: Independently implement the provenance checker**

Do not copy the exchange Go package. Implement the closed decoders again from the admitted schemas. Use this API:

~~~go
type Options struct {
	Root           string
	Milestone      string
	ExpectedOrigin string
	GitBinary      string
}

func Check(ctx context.Context, opts Options) (checkresult.Result, error)
~~~

Inspect tracked files and modes with Git; verify every commit signature status and fingerprint; match each non-merge commit to a valid implementation attestation; and allow an admitted `merge-service` fingerprint only on a two-parent merge whose parent commits already verify. Compare imported files with the exchange lock; verify LICENSE and NOTICE; require SPDX on `.go`, `.md`, `.ps1`, `.sh`, `.yml`, and `.yaml`; reject denied remotes, imports, paths, and content; and sort findings deterministically. The checker never opens a network connection.

- [ ] **Step 6: Implement the CLI and prove negative canaries**

~~~powershell
go test ./internal/provenance -count=1
go run ./cmd/provenancecheck -root . -milestone M0
go test ./internal/provenance -run 'TestMissingAttestationRejected|TestDeniedRemoteRejected|TestDigestMismatchRejected' -count=1
~~~

Expected: unit tests pass, the repository check selects a nonzero set and reports `pass`, and every named canary passes by observing the intended rejection.

- [ ] **Step 7: Commit independently authored provenance tooling**

~~~powershell
git add --all
git diff --cached --check
git commit -S -m 'feat: enforce implementation provenance'
~~~

### Task 8: Add Preflight, Coverage, and Fail-Closed Selection

**Execution role:** Implementation contributor.

**Requirements:** `PLGO-CR-M0-010`

**Files:**

- Create: `internal/preflight/run.go`, `run_test.go`
- Create: `internal/coveragegate/gate.go`, `gate_test.go`
- Create: `cmd/preflight/main.go`, `cmd/coveragegate/main.go`

- [ ] **Step 1: Write failing registry and zero-selection tests**

Define checks with exact name, minimum milestone, command function, and one reviewed not-applicable reason. Tests require unknown tiers, unknown checks, empty applicable selections, duplicate names, missing reasons, and a check returning no evidence to fail.

The only M0 not-applicable entries are:

| Check | Reason |
|---|---|
| Conformance on each platform | `milestone-m0-has-no-conformance-vectors` |
| Determinism Comparison | `milestone-m0-has-no-machine-state` |

- [ ] **Step 2: Run red tests**

~~~powershell
go test ./internal/preflight ./internal/coveragegate -count=1
~~~

Expected: compilation fails because both packages are absent.

- [ ] **Step 3: Implement preflight orchestration**

`go run ./cmd/preflight -tier commit` runs tracked-file/conflict-marker checks, gofmt diff, SPDX/provenance, all unit tests, and committed fuzz seeds. `-tier push` adds vet, race on supported hosts, `go mod verify`, a tidy-diff check, `go list -deps -json ./...`, vulnerability scan invocation validation, dependency-license review, coverage, and gate canaries. `-tier release` adds signed-commit history, exchange-lock signature evidence, clean working tree, and M0 acceptance evidence read from the explicit `PLGO_EVIDENCE_DIR`. A missing, relative, home-directory, or shared-cache evidence path fails.

Every subcheck emits a `plgo.check-result/1` record. Preflight stops scheduling new checks after an operational error but still emits a final failing result naming checks not run. Policy failures remain visible and cannot be converted to a pass.

- [ ] **Step 4: Implement coverage thresholds**

Parse `go tool cover -func` output without locale-dependent matching. Exclude command packages from per-package thresholds. Require at least 85 percent for each non-command production package and 90 percent repository total. Exclusions require an exact file path, exact rationale, owner, and expiry condition; wildcard exclusions fail.

- [ ] **Step 5: Run commit and push tiers**

~~~powershell
go run ./cmd/preflight -tier commit
go run ./cmd/preflight -tier push
~~~

Expected: both tiers print every selected check count and end with `result:"pass"`. Conformance and determinism report the exact M0 not-applicable reasons rather than silently selecting zero.

- [ ] **Step 6: Commit**

~~~powershell
git add cmd/coveragegate cmd/preflight internal/coveragegate internal/preflight
git commit -S -m 'feat: add fail-closed preflight gates'
~~~

### Task 9: Install Immutable CI and Branch Protection

**Execution role:** Exchange contributor for exchange workflow; implementation contributor for Go workflow; sponsor administrator for rulesets.

**Requirements:** `PLGO-CR-M0-005`, `PLGO-CR-M0-006`, `PLGO-CR-M0-010`

**Files:**

- Create: exchange `.github/workflows/admission.yml`
- Create: implementation `.github/workflows/pr.yml`
- Update: both `.github/CODEOWNERS`

- [ ] **Step 1: Add workflow-policy tests before workflows**

Add repository tests that parse tracked workflow text and reject floating `uses:` values, write permissions not explicitly justified, `continue-on-error`, retry wrappers, ignored exit codes, and missing stable check names. Run them before creating workflows and observe failure for missing workflow files.

- [ ] **Step 2: Pin official actions**

Use these immutable commits, verified from the official repositories on 2026-07-15:

~~~yaml
actions/checkout@9c091bb21b7c1c1d1991bb908d89e4e9dddfe3e0
actions/setup-go@924ae3a1cded613372ab5595356fb5720e22ba16
~~~

Set top-level `permissions: contents: read`. PR jobs never receive a release token.

- [ ] **Step 3: Create exchange checks**

`admission.yml` exposes stable checks `Artifact Admission`, `Contamination Canary`, `Format and Vet`, `Unit — Go 1.25`, and `Unit — Go 1.26`. It runs admission on the full candidate tree, then runs the negative contaminated fixture and requires the candidate rejection. No job downloads corpus or model payloads.

- [ ] **Step 4: Create all fourteen implementation PR checks**

`pr.yml` always reports these names:

1. Provenance and License
2. Format and Vet
3. Unit and Contract — Go 1.25
4. Unit and Contract — Go 1.26
5. Race — Linux amd64
6. Conformance — Linux amd64
7. Conformance — Linux arm64
8. Conformance — Windows amd64
9. Conformance — macOS arm64
10. Determinism Comparison
11. Fuzz Exploration
12. Coverage
13. Vulnerability and Dependency
14. Gate Canaries

Checks 6 through 10 call preflight and emit the exact reviewed M0 not-applicable result where applicable. The fuzz job runs the strict JSON and provenance decoders for 30 seconds per target. The vulnerability job runs `go run golang.org/x/vuln/cmd/govulncheck@v1.6.0 ./...` and preserves its native exit status. Record that tool and license review in `tools/tools.lock.json`.

Every Go job sets `GOFLAGS=-mod=readonly` and `GOWORK=off`; all non-race jobs set `CGO_ENABLED=0`. The race job records its instrumentation exception and never produces a release artifact.

- [ ] **Step 5: Run untrusted code only in the implementation sandbox**

The implementation runner checks out source, then runs all Go commands in an ephemeral environment with no reference mount, no inherited developer home, no credentials, and denied outbound egress. The sandbox receives only source, the admitted exchange release cache by digest, Go toolchain/cache, and a writable temporary directory. A network canary attempts DNS and TCP egress and must observe denial before tests run.

- [ ] **Step 6: Verify workflow policy and open pull requests**

~~~powershell
go test ./... -count=1
git diff --check
git add .github tools/tools.lock.json
git commit -S -m 'ci: enforce clean-room quality gates'
git push --set-upstream origin HEAD
~~~

Expected: exchange checks and all fourteen implementation checks report on their respective pull requests; none are skipped or neutral.

- [ ] **Step 7: Apply branch rulesets**

Require pull requests, two approvals for exchange policy paths, CODEOWNERS review, conversation resolution, signed commits, and every stable check listed above. Preserve signed contributor commits in merge history; an admitted GitHub merge-service key may sign only merge commits. Disable force pushes, branch deletion, and administrator bypass except a logged break-glass sponsor path that triggers taint review.

### Task 10: Run Gate Canaries and M0 Acceptance

**Execution role:** Independent verifier runs evidence; sponsor and legal/provenance reviewer sign. Implementation and reference contributors do not approve their own evidence.

**Requirements:** `PLGO-CR-M0-001` through `PLGO-CR-M0-012`

**Files:**

- Create in exchange: `evidence/m0/m0-acceptance.json`, `evidence/m0/sponsor-signoff.json`, `evidence/m0/legal-provenance-signoff.json`
- Create in exchange: corresponding `manifests/evidence/*.json`
- Verify in implementation: `.cleanroom/exchange.lock.json`

- [ ] **Step 1: Run the complete negative canary set**

From disposable copies, independently introduce one mutation at a time: decoded contaminated URL, missing manifest, altered digest, unauthorized reviewer, unknown JSON field, executable bit, symlink, LFS pointer, archive magic, empty artifact selection, missing contributor attestation, unsigned implementation commit, denied remote, altered LICENSE, and zero-test selection. Require the exact stable finding for every mutation. Delete disposable copies after retaining hashes and logs; never merge the mutations.

- [ ] **Step 2: Verify the fixed policy release and implementation pin**

Use the two-builder archive digest and signatures published in Task 6. Confirm implementation `.cleanroom/exchange.lock.json` names that fixed policy release, exact archive byte length, SHA-256, admission commit, signatures, and imported policy digest. Do not rebuild the policy release after implementation evidence exists; that would create a cross-repository digest cycle. Run:

~~~powershell
go run ./cmd/provenancecheck -root . -milestone M0
go run ./cmd/preflight -tier push
~~~

Expected: both report a nonzero selected count and `pass`. The release tier is intentionally deferred until the signed acceptance evidence exists.

- [ ] **Step 3: Verify the M0 environment boundary**

From the implementation developer image and CI sandbox, prove denied reference clone attempts, DNS/TCP egress, host home access, reference mounts, shared agent transcripts, and unapproved caches are unavailable. Prove the admitted exchange archive is readable only by its digest. Record commands, timestamps, environment image digest, and outcomes without recording denied source content.

- [ ] **Step 4: Produce the acceptance report**

`evidence/m0/m0-acceptance.json` uses a closed schema and records all twelve requirement IDs with `satisfied` or `unsatisfied`, the fixed exchange policy commit and archive digest, implementation commit and lock digest, repository ruleset IDs, role-registry digest, canary results, CI run URLs, environment evidence digest, remaining risks, and overall result. No requirement may be inferred from wiring alone. This evidence is admitted after the policy release and is not an implementation input. Create its `manifests/evidence/` record only after every `satisfied` result has an evidence digest and its test demonstrated the intended red case. Commit the report and manifest together as `audit: record M0 acceptance candidate` on an exchange evidence branch.

- [ ] **Step 5: Sign the operating protocol and acceptance report**

The sponsor and legal/provenance reviewer each create a `plgo.signoff/1` object naming their role-key fingerprint, the already-signed operating-protocol SHA-256, M0 acceptance SHA-256, decision `approved`, and an RFC 3339 UTC timestamp. Each adds only its own signoff file to the evidence branch and commits with its own signing key. The admission checker verifies distinct authorized identities. These evidence commits do not change the fixed policy release digest.

- [ ] **Step 6: Admit requirement evidence and rerun final gates**

Leave the immutable policy release's `requirements/m0.json` statuses unchanged. At the final evidence-branch head, run in exchange:

~~~powershell
go test ./... -count=1
go run ./cmd/admissioncheck -root . -milestone M0
git diff --check
~~~

Push the evidence branch, require the exchange admission checks, and merge it through branch protection. Export only `m0-acceptance.json`, both evidence signoffs, their manifest, and the protected evidence commit identity into `C:\plgo-evidence\m0-acceptance-2026-07-15.1`. Verify each exported byte against the protected commit before running the implementation release tier.

Run in implementation:

~~~powershell
$env:PLGO_EVIDENCE_DIR = 'C:\plgo-evidence\m0-acceptance-2026-07-15.1'
if (!(Test-Path -LiteralPath $env:PLGO_EVIDENCE_DIR -PathType Container)) { throw 'Explicit M0 evidence directory is absent' }
go test ./... -count=1
go vet ./...
go test -race ./...
go run ./cmd/provenancecheck -root . -milestone M0
go run ./cmd/preflight -tier release
git diff --check
~~~

Expected: all applicable checks pass, both N/A checks name their exact M0 reason, and the working trees are clean after evidence commits.

- [ ] **Step 7: Create protected M0 completion tags**

Retain the Task 6 signed policy tag `exchange-m0-foundation-2026-07-15.1`. Create signed tags `exchange-m0-acceptance-2026-07-15.1` on the admitted evidence commit and `go-m0-foundation-2026-07-15.1` on the verified implementation commit. Publish checksums, signatures, admission report, M0 acceptance report, LICENSE, and NOTICE. Do not publish game packages, model weights, raw oracle data, or implementation environment credentials.

## Plan Self-Review Gate

Before admitting or executing this plan:

- [ ] Map each `PLGO-CR-M0-*` requirement to at least one red canary, one positive verification, one evidence owner, and one protected CI check.
- [ ] Confirm every target path appears in exactly one repository tree and no implementation task executes in the reference clone.
- [ ] Confirm the Go types and JSON schemas use identical field names, enums, timestamp rules, digest formats, and closed-object behavior.
- [ ] Confirm every command names an expected pass, expected rejection, or explicit M0 not-applicable outcome.
- [ ] Search the plan for unresolved marker words by constructing each search term from two string fragments; the search must select zero lines.
- [ ] Count opening and closing Markdown fences and require an even total.
- [ ] Run `git diff --check` and review `git diff -- docs/superpowers/plans/2026-07-15-projectlegends-go-m0-cleanroom-foundation.md`.
- [ ] Have a provenance reviewer verify that the plan contains functional process requirements only and no reference-derived implementation expression.

## Completion Boundary

M0 is complete only when all twelve requirements are `satisfied`, both repositories are protected, the contaminated sample and every gate canary have produced their intended rejection, the implementation pins the final exchange digest, all mandatory checks report, and both required signoffs verify. Repository creation, passing unit tests, or merged workflow wiring alone is not completion.

After M0, write separate implementation plans in this order:

1. M1 public Go contract and deterministic machine lifecycle.
2. M1 canonical snapshots, state hashing, and conformance runner.
3. M1 cross-platform quality, fuzz, race, determinism, and release evidence.
4. M2/M3 real-mode machine and DOS services.
5. M4 corpus acquisition, safe preparation, and deterministic game replays.
6. M5 `plgo-ai/1`, `plgo-refplayer`, local-model qualification, and report promotion.
