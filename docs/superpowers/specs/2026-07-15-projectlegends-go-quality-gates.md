<!--
SPDX-License-Identifier: Apache-2.0
Copyright 2026 Charles Hoskinson and Contributors
-->

# ProjectLegends Go Clean-Room Quality and Verification Gates

Date: 2026-07-15
Status: draft for sponsor and clean-room admission review
Quality policy version: 1
License: Apache-2.0

## 1. Purpose

This specification carries ProjectLegends' strongest engineering practices into
the independent Go implementation while replacing C++-specific machinery with
Go-native controls. It defines the minimum local, pull-request, nightly, and
release gates for the headless nucleus and defines how the same evidence model
extends to the DOS reference corpus and AI play agent in later milestones.

The governing rule is evidence before assertion: a requirement is complete
only when its required test can fail for the intended reason and the mandatory
gate records a passing result.

## 2. Toolchain policy

As of 2026-07-15:

- the minimum supported toolchain is Go 1.25.12;
- the primary and release toolchain is Go 1.26.5;
- the go directive is 1.25.0;
- the toolchain directive pins go1.26.5;
- CGO_ENABLED is zero for all M1 builds and tests;
- module mode is readonly in CI;
- the public module has no replace directives in protected branches.

Go supports a major release until two newer major releases exist. A reviewed
toolchain-policy change updates the minimum and primary versions together,
replays all conformance vectors, rebuilds release artifacts, and records the
new digests.

Primary references:

- https://go.dev/doc/devel/release
- https://go.dev/doc/articles/race_detector
- https://go.dev/doc/security/fuzz/
- https://go.dev/doc/security/vuln/

## 3. Quality principles

1. **One gate entry point.** Local development and CI invoke the same
   repository-owned preflight command.
2. **Test behavior, not implementation shape.** Tests name requirement IDs and
   assert public effects or independent invariants.
3. **No hidden green.** Missing tests, empty selections, scanner errors,
   unavailable vectors, and artifact upload failures fail the gate.
4. **No automatic retries.** A retry may collect evidence but cannot replace
   the original failing conclusion.
5. **No silent demotion.** Every skip, quarantine, relaxed assertion, excluded
   package, or weakened gate has a tracked owner and exit condition.
6. **Determinism is cross-environment.** Same-process repetition alone is
   insufficient.
7. **Decoders are hostile-input surfaces.** Snapshots, programs, vectors, and
   input batches have fuzz and boundary tests from their first merge.
8. **Provenance is a correctness property.** Functionally correct code with
   incomplete clean-room evidence cannot merge or ship.
9. **Standard library first.** Dependencies are exceptions justified in a
   decision record.
10. **Quality ratchets upward.** Threshold reductions are demotions.
11. **AI exploration is evidence discovery, not an oracle.** Only a reviewed,
    deterministic replay may become a mandatory product gate.

## 4. Repository-owned commands

The implementation repository exposes these stable commands:

| Command | Contract |
|---|---|
| go run ./cmd/preflight -tier commit | Fast formatting, generated-file, SPDX, unit, and seed checks |
| go run ./cmd/preflight -tier push | Complete local-reachable PR gates |
| go run ./cmd/preflight -tier release | All release gates except other operating systems |
| go run ./cmd/vectorcheck | Validate and replay an immutable exchange release |
| go run ./cmd/coveragegate | Enforce package, total, and changed-line thresholds |
| go run ./cmd/provenancecheck | Verify clean-room manifests, contributor attestations, dependencies, and forbidden imports |
| go run ./cmd/determinismcheck | Repeat traces and compare normalized checkpoint manifests |
| go run ./cmd/corpusctl verify | Validate active corpus manifests, license evidence, objectives, and cached digests without substitution |
| go run ./cmd/gamecheck | Run deterministic admitted game replays through the neutral AI adapter |
| go run ./cmd/agentcheck | Validate reference-agent reports, policies, model-bundle identities, transcripts, and canary episodes |

The commands contain orchestration and validation only. Core behavior remains
in importable packages with unit tests.

Every selector prints the selected test, package, vector, or artifact count.
Zero selected items is an error unless the command has a documented
not-applicable result that still reports a successful check conclusion.

## 5. Test taxonomy

| Class | Location | Purpose |
|---|---|---|
| Unit | package-local files ending in _test.go | Pure functions, validation, boundary behavior |
| Contract | contracttest/ | Public API requirements and typed errors |
| Conformance | exchange vectors through vectorcheck | Approved black-box and normative behavior |
| Property | package tests | Invariants over generated structured values |
| Metamorphic | contracttest/metamorphic/ | Split-step, round-trip, replay, and sensitivity relations |
| Fuzz | package tests named Fuzz... | Coverage-guided hostile input exploration |
| Race | all packages and concurrency fixtures | Runtime data-race detection |
| Determinism | determinism/ | Cross-run, cross-platform, cross-toolchain equality |
| Soak | soak/ | Long-run lifecycle, queue, snapshot, and resource stability |
| Benchmark | package benchmarks and benchmarks/ | Regression budgets without correctness assertions |
| Canary | internal/gatecanary/ | Proves gates fail when their oracle is violated |
| Corpus | corpus/ through corpusctl | Package identity, license evidence, safe acquisition, and reproducible preparation |
| Adapter | adaptertest/ | Neutral AI protocol, bounds, forbidden operations, and prompt-injection isolation |
| Game replay | compatibility/replays/ | Deterministic system-level DOS compatibility evidence |
| Agent exploration | evaluator-owned nightly lane | Discovers paths and produces reviewed reports; never directly decides conformance |
| Local model qualification | evaluator-owned pinned-hardware lane | Selects and versions the reference policy; never directly decides product conformance |

Every normative test includes at least one requirement ID in its name or test
metadata. A requirement index maps each published ID to at least one mandatory
test and rejects nonexistent tests.

## 6. Test design rules

### 6.1 Unit and contract tests

- Use table-driven tests for value partitions and boundary matrices.
- Assert ErrorCode with errors.As; never match diagnostic error strings.
- Assert the complete public result when all fields are normative.
- Verify state hashes before and after every operation required to be atomic on
  failure.
- Verify caller-owned slice and string mutations cannot alter machine state.
- Avoid sleeps, wall-clock deadlines, host locale, random map order, and
  scheduling assumptions.
- Use deterministic seeds written into failure output.
- A fixed defect adds a regression test that fails on the pre-fix behavior.

### 6.2 Properties and metamorphic relations

M1 continuously checks:

- Save(S) equals Save(S).
- Load(Save(S)) preserves StateHash and canonical snapshot bytes.
- A failed Load preserves StateHash.
- With the complete input trace queued before execution, Step(a) followed by
  Step(b) reaches the same final state, captures, generation, and state hash as
  Step(a+b); executed-cycle and processed-input totals are additive when no
  halt boundary changes the allowed execution.
- Queueing an admitted ordered batch equals queueing the same events one at a
  time.
- Capturing a surface does not change FrameGeneration or StateHash.
- Reset returns the post-New StateHash.
- Rejected input leaves queue length and StateHash unchanged.
- Distinct admitted seeds, programs, or meaningful inputs change at least one
  designated sensitivity checkpoint.

### 6.3 Fuzzing

Native Go fuzz targets exist for:

1. PLGOPRG1 program decoding;
2. snapshot header and section decoding;
3. InputEvent batch validation;
4. exchange JSON and NDJSON schema decoding;
5. canonical state encoding;
6. operation-sequence state-machine execution.

Each target:

- has a small committed seed corpus;
- validates resource bounds before allocation;
- checks that no panic, hang, race, or unbounded allocation occurs;
- asserts round-trip or rejection atomicity where applicable;
- stores minimized failures as committed regression seeds after provenance
  review;
- does not call the reference oracle.

PR fuzz exploration runs each target for 30 seconds on linux/amd64. Nightly
exploration runs each target for 15 minutes on linux/amd64 and linux/arm64.
Seed replay runs on every supported operating system and is deterministic.

### 6.4 Race testing

The mandatory race job runs:

~~~text
go test -race -count=1 ./...
~~~

Concurrency fixtures deliberately overlap Step, capture, QueueInput, Reset,
Load, StateHash, and Close and verify the concurrency contract. Race-only skips
are prohibited in M1. The job also runs a representative vector workload under
a race-built vectorcheck binary because the detector observes only executed
paths.

## 7. Coverage policy

Coverage is enforced over non-generated production packages.

M1 thresholds:

- machine, snapshot, clock, input, and statehash packages: at least 90 percent
  statement coverage each;
- every other non-command production package: at least 85 percent;
- repository total: at least 90 percent;
- changed executable lines: at least 95 percent;
- every ErrorCode and every snapshot rejection branch: at least one test.

Generated schema bindings, command argument plumbing, and unreachable defensive
panic stubs may be excluded only by a reviewed coverage policy file naming the
exact file and reason. The coverage gate rejects stale or wildcard exclusions.

Coverage is necessary but not sufficient. A canary suite mutates known branch
outcomes in a disposable copy and proves the requirement tests detect the
change. Canary failure blocks release and runs nightly.

## 8. Determinism verification

### 8.1 Environment matrix

Every PR replays the deterministic vector subset on:

- Ubuntu, amd64, Go 1.25.12;
- Ubuntu, amd64, Go 1.26.5;
- Ubuntu, arm64, Go 1.26.5;
- Windows, amd64, Go 1.26.5;
- macOS, arm64, Go 1.26.5.

Each cell emits a normalized checkpoint manifest. A final mandatory job
compares the manifests byte-for-byte.

Each Linux cell repeats with:

- GOMAXPROCS 1;
- GOMAXPROCS 2;
- host-default GOMAXPROCS;
- TZ UTC and one non-UTC zone;
- two supported UTF-8 locales;
- distinct temporary paths and process IDs.

### 8.2 Replay requirements

- Every determinism case runs twice in fresh processes.
- The comparison includes StepResult, captures, snapshot SHA-256, and
  StateHash.
- Expected platform differences are forbidden in M1 observable state.
- A mismatch uploads both normalized manifests and input digests, never
  implementation memory or reference-side data.
- No platform becomes optional because it is temporarily red.

## 9. Static, security, and dependency gates

Mandatory commands:

~~~text
gofmt check over every tracked .go file
go vet ./...
go test ./...
govulncheck ./...
go mod verify
go mod tidy diff check
go list -deps -json ./...
~~~

The govulncheck invocation uses its normal exit status rather than a
report-only JSON mode. Tool versions are pinned in the repository and updated
through reviewed dependency changes.

Dependency rules:

- M1 production packages SHOULD use only the standard library.
- A third-party production module requires a decision record describing
  necessity, version, source, license, maintenance health, reachable API,
  vulnerability status, and removal strategy.
- GPL, AGPL, LGPL, SSPL, source-available, unknown, or custom-license modules
  are denied from the Apache-2.0 implementation unless the sponsor and legal
  reviewer approve a new policy version.
- Test-only modules follow the same provenance review even when they do not
  ship.
- go.sum is mandatory and module downloads use the public checksum database or
  an approved immutable internal mirror.
- CI never executes an unverified downloaded script.
- GitHub Actions and external tools are pinned to immutable commit or artifact
  digests and updated by an authenticated dependency bot.

## 10. Clean-room and license gates

Every PR runs provenancecheck, which verifies:

- all source and specification files carry SPDX-License-Identifier:
  Apache-2.0;
- LICENSE contains the unchanged Apache License 2.0 text;
- NOTICE matches the approved attribution inventory;
- every commit author has a current implementation-team non-exposure
  attestation;
- every exchange artifact belongs to the pinned admitted exchange release;
- no Git remote, URL, path, symbol, identifier inventory, or copied text refers
  to denied repositories beyond the approved policy wording;
- dependency licenses match the allow policy;
- generated files identify their admitted inputs and generator version;
- no reference-oracle package, binary, container, credential, or network route
  exists in the implementation environment;
- every corpus artifact is active under the corpus policy, stored outside the
  source tree, and matches its manifest byte length and SHA-256;
- Class C and D game artifacts and observations never enter public CI or
  exchange artifacts; and
- agent reports admitted to exchange contain no internal reference details,
  unrestricted guest data, credentials, model chain-of-thought, or denied
  implementation advice.

The scanner uses exact forbidden patterns maintained by the provenance
reviewer. Scanner findings cannot be ignored inline.

## 11. CI tiers

### 11.1 Commit tier

Target: deterministic feedback suitable for a local pre-commit hook.

Required:

- tracked-file and conflict-marker checks;
- gofmt;
- SPDX and provenance manifest syntax;
- generated-file freshness;
- affected package unit tests;
- fuzz seed replay for affected decoders.

Skipping local hooks never changes server-side requirements.

### 11.2 Pull-request tier

Stable mandatory check names:

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

All fourteen checks always report. Changed-path optimization may skip work
inside a successful check only after a fail-closed impact analyzer proves the
change irrelevant. Unknown paths run everything.

### 11.3 Nightly tier

Nightly adds:

- 15-minute fuzzing per target and fuzz-corpus artifact retention;
- 100-run shuffled contract burn-in with recorded seeds;
- four-hour bounded lifecycle and snapshot soak;
- peak allocation and goroutine leak checks;
- benchmark comparison against the protected baseline;
- full dependency, SBOM, and license inventory;
- gate canary mutation suite;
- exchange schema and provenance revalidation;
- supported-toolchain and platform rehearsal;
- deterministic replay of each active game from a fresh writable overlay; and
- informational reference-agent exploration with the admitted local profile,
  plus model identity, offline operation, schema, disclosure, resource, and
  replay-candidate validation.

Nightly failures open or update a tracked incident. A red nightly result does
not become informational through workflow syntax. In the reference-agent lane,
adapter, policy, schema, or artifact-pipeline failures are red; the explored
game's pass, fail, or inconclusive result remains informational until promoted
to a deterministic replay.

### 11.4 Release tier

A release requires:

- every PR and nightly gate green on the release commit;
- no active gate demotion or expired quarantine;
- complete requirement-to-test traceability;
- clean-room audit approval tied to the commit and exchange digest;
- two independent release builders producing identical artifact SHA-256;
- source archive, module inventory, CycloneDX SBOM, checksums, provenance
  attestation, LICENSE, NOTICE, and security contact;
- successful install and vector replay from the produced artifacts;
- a signed release manifest naming Go, tool, exchange, source, and artifact
  digests;
- for M4 and later, green deterministic replays for every active game whose
  required capabilities are claimed; and
- for M5 and later, a green AI-adapter contract suite and reference-agent
  report canary.

### 11.5 Milestone-applicable compatibility checks

Beginning with M4, branch protection adds these stable check names:

15. Corpus Manifest and Acquisition
16. AI Adapter Contract
17. Game Replay Stability

Beginning with M5 it also adds:

18. Reference Agent Report Canary

Before activation, the checks report a schema-valid `not-applicable` conclusion
that names the milestone and missing capability; they do not silently select
zero tests. Check 18 validates the admitted model-bundle digest, offline agent
boundary, hostile-observation controls, and report pipeline. It does not require
a game win. An exploratory game outcome remains informational until converted
to an admitted deterministic replay.

## 12. Flake and quarantine policy

A test is flaky when identical declared inputs can both pass and fail.

- CI does not retry a flaky test to turn the check green.
- A quarantine requires an issue with owner, first-failure evidence, affected
  requirement, risk, bounded replacement coverage, and explicit removal
  condition.
- Quarantined tests remain enabled in nightly and carry the issue identifier.
- Quarantine expires after 14 calendar days unless the sponsor approves a
  dated extension.
- Deleting or weakening an assertion solely to remove a failure is forbidden.
- Timing tolerances require a measured platform reason and do not apply to
  deterministic state.

## 13. Gate demotion policy

The following are demotions:

- continue-on-error, ignored exit codes, unconditional success fallbacks, or
  report-only conversion of a mandatory tool;
- removing a platform, toolchain, package, vector family, fuzz target, or race
  workload;
- lowering coverage, benchmark, resource, or determinism requirements;
- adding a skip, quarantine, suppression, exclusion, allowlist, or scanner
  ignore;
- accepting missing artifacts or zero selected tests;
- changing a mandatory check name without updating branch protection in the
  same administrative transaction.

A demotion change requires before merge:

1. a tracked issue;
2. named owner;
3. evidence and risk statement;
4. smallest possible scope;
5. explicit exit criterion;
6. automated signal proving the demotion still exists;
7. sponsor approval.

No release may contain an active M1 provenance, conformance, determinism,
snapshot-integrity, race, or vulnerability-gate demotion.

At M4 and later, the same rule applies to corpus identity, acquisition safety,
and required game-replay demotions. At M5 and later it also applies to the
AI-adapter contract. Model-provider availability and exploratory agent skill
are not product release gates.

## 14. Benchmarks and resource budgets

Correctness gates never depend on elapsed time. Performance benchmarks record:

- Step throughput for fixed admitted programs;
- snapshot encode and decode throughput;
- StateHash throughput;
- QueueInput batch throughput;
- capture-copy throughput;
- allocations per operation;
- retained heap and goroutine count after repeated lifecycle runs.

The protected benchmark baseline stores raw samples, environment metadata, and
commit digest. A regression blocks nightly when the median degrades by more
than 10 percent and the 95 percent confidence interval excludes zero across at
least ten samples. Release blockers require reproduction on a second runner.

Hard correctness resource limits remain independently tested regardless of
benchmark results.

### 14.1 Local reference-model qualification

The evaluator implements the model-selection and replacement protocol in
section 9.4 of the DOS corpus and reference-agent specification. The
provisional quality model is Qwen3.6-27B; Qwen3.5-9B is the compact development
profile. Neither a model name nor a vendor leaderboard result is a test result.

There are three schedules:

1. **Change canary.** After a model, quantization, runtime, prompt, policy,
   memory, parser, adapter, action schema, or observation-encoding change, run
   the fixed hostile-observation and small text/graphics set three times. Its
   gate covers identity, isolation, legal protocol use, complete artifacts, and
   schema validity, not game skill.
2. **Nightly exploration.** Run one fixed seed per active objective using the
   admitted local profile. Infrastructure, isolation, or artifact failures are
   red; state-verified game progress remains informational.
3. **Qualification.** Before first activation or replacement, and at least
   quarterly, run five paired game states or emulator seeds by three inference
   seeds per applicable objective. Run eight repetitions on the reliability
   subset and compare every candidate against no-op, random-valid-action, and
   scripted-oracle controls.

The test set is frozen before results are inspected and is split by game title,
not merely by save state. It contains locked sponsor-authored Class A titles in
addition to active public games. State clearing covers the writable overlay,
emulator, adapter, model conversation, explicit memory, prompt cache, and
runtime request state before every episode.

The primary model measures are:

- state-verified binary objective success, normalized milestone progress, and
  the complete milestone vector;
- macro-average progress by game, plus genre, horizon, observation-modality,
  and worst-quartile breakdowns;
- full-suite `pass^1` and reliability-subset `pass^3`, `pass^5`, and
  `pass^8`;
- progress per action and the actions, emulated cycles, wall time, tokens, and
  model decisions required to reach each milestone;
- first-pass schema validity, legal and executable action rate, invalid,
  rejected, repaired, duplicate, stale, no-effect, loop, and stall rates;
- grounding accuracy for bounded click, drag, key, chord, and hold-duration
  fixtures;
- recovery after a rejected action or injected adapter fault;
- observation-to-action latency p50, p95, and p99, deadline misses, peak RAM,
  peak device memory, and prompt and generation throughput; and
- reviewed deterministic replay-candidate yield.

`pass^k` means that all `k` repeated attempts succeed; it is not `pass@k`,
which credits one success among `k` attempts.

The test report gives game-clustered bootstrap 95 percent confidence intervals
and paired comparisons on shared seeds. It retains the model, runtime, hardware,
driver, quantization, prompt, policy, parser, action-schema, observation-
encoding, and corpus digests. Artifact size is not reported as peak RAM or
VRAM; memory qualification measures a fully warmed worst-case image, context,
and output workload at concurrency one and preserves headroom.

Qualification also runs paused-versus-real-time, raw-RGBA-versus-text-versus-
fused, memory-off-versus-on, context-pressure, prompt-paraphrase, scaler and
resolution, target-size, missing or delayed frame, rejected action, and bounded
input-repeat or input-drop diagnostics. These are named profiles or ablations;
their outcomes are never pooled silently.

Exact model tokens and action trajectories are not cross-platform goldens.
Safety boundaries, schema validity, state-verified outcomes, and deterministic
replays are the stable assertions. A stochastic agent report cannot replace a
product conformance vector or required game replay.

## 15. Formal specification

The exchange repository contains independently authored Apache-2.0 TLA+ models
for:

- lifecycle and idempotent Close;
- atomic snapshot load;
- input ordering and queue capacity;
- cycle scheduler tie-breaking;
- concurrent-call rejection;
- deterministic replay equivalence.

Model checking is mandatory when a change modifies a modeled state transition.
The CI selector lists the models chosen and fails on zero selection. Model
checking supplements executable tests and never substitutes for vector replay.

## 16. Review and completion definition

A feature is complete only when:

- its normative requirement has an immutable ID;
- a test first demonstrated the missing behavior;
- implementation and tests pass locally through preflight;
- requirement mapping, documentation, and vector impact are reviewed;
- all mandatory CI gates pass without demotion;
- no new unreviewed dependency or provenance input exists;
- the protected branch contains the evidence artifacts.

Release completion additionally requires the release-tier evidence in section
11.4. A milestone status document reports unmet items explicitly; it never
infers completion from merged wiring.
