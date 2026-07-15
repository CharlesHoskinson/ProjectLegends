<!--
SPDX-License-Identifier: Apache-2.0
Copyright 2026 Charles Hoskinson and Contributors
-->

# ProjectLegends Go Clean-Room Program — Design

Date: 2026-07-15
Status: draft for sponsor and counsel review
License: Apache-2.0
Decision owner: ProjectLegends sponsor

## 1. Decision summary

The program will create a new Apache-2.0 implementation in Go through a strict
two-team clean-room process. The implementation team will have no access to
ProjectLegends, DOSBox-X, or other disallowed source material. It will receive
only approved specifications, public standards, sponsor-owned test programs,
and reproducible black-box conformance vectors through a controlled exchange
repository.

The first independently shippable milestone is a headless deterministic
nucleus. It establishes lifecycle, cycle-based stepping, timestamped input,
text and RGBA capture, canonical snapshots, and stable state hashing before
the program attempts a complete x86 PC or DOS implementation.

This document defines the program and architectural boundaries. Normative
behavior and verification are defined in:

- **2026-07-15-projectlegends-go-headless-nucleus-contract.md**
- **2026-07-15-projectlegends-go-conformance-vectors.md**
- **2026-07-15-projectlegends-go-quality-gates.md**
- **2026-07-15-projectlegends-go-dos-corpus-and-reference-agent.md**

## 2. Goals

1. Produce an independently authored Go codebase distributable under
   Apache-2.0.
2. Preserve the engineering properties that matter most in ProjectLegends:
   deterministic execution, explicit lifecycle, bounded inputs, atomic state
   restore, headless operation, cross-platform tests, honest CI, fuzzing,
   race detection, and traceable requirements.
3. Establish a neutral contract that can later support a Go API, generated C
   adapter, process protocol, or additional hosts without coupling the machine
   core to any one transport.
4. Make provenance auditable at the artifact, commit, contributor, and release
   levels.
5. Deliver useful, testable increments rather than waiting for full DOSBox
   compatibility.

## 3. Non-goals

The first milestone will not:

- copy or translate ProjectLegends or DOSBox-X source, headers, tests, comments,
  symbols, file structure, or save-state layout;
- promise binary, C ABI, or snapshot compatibility with ProjectLegends;
- execute arbitrary commercial DOS software;
- provide a desktop user interface, audio device, networking, MIDI, printer,
  Glide, PC-98, or host file-system mounting;
- use cgo, assembly, unsafe, plugins, reflection-based serialization, or
  dynamically loaded native libraries;
- optimize ahead of measured conformance and benchmark evidence;
- claim that process controls replace legal review.

## 4. Clean-room operating model

### 4.1 Roles

| Role | May inspect reference implementation | May write Go implementation | Responsibilities |
|---|---:|---:|---|
| Sponsor | Yes | No | Sets product scope, funds review, owns final risk decision |
| Reference team | Yes | No | Runs black-box experiments and creates candidate behavioral evidence |
| Specification custodian | Candidate artifacts only | No | Normalizes requirements, removes expressive leakage, maintains exchange manifests |
| Corpus steward | Approved public packages and license evidence only | No | Classifies, hash-pins, audits, and activates reference software |
| Gameplay evaluator | No source; black-box adapter access only | No | Runs reference-agent episodes and proposes behavioral reports and replays |
| Legal/provenance reviewer | As required | No | Approves artifact admission and release evidence |
| Implementation team | No | Yes | Implements only from admitted exchange artifacts and public standards |
| Independent verifier | No reference source required | No production code | Replays vectors, audits CI, and verifies release provenance |

No person or agent may serve simultaneously on the reference and implementation
teams. An implementation-team member who accesses a denied artifact is removed
from implementation work until the sponsor and legal reviewer document a
remediation decision.

### 4.2 Repository topology

The program uses three separately administered repositories:

1. **Reference repository**
   - Contains the existing ProjectLegends material and oracle tooling.
   - Is inaccessible to the implementation team.
   - May produce candidate observations but never pushes directly to the
     implementation repository.

2. **Exchange repository**
   - Contains only Apache-2.0 specifications, schemas, sponsor-owned test
     programs, conformance vectors, approved corpus metadata and replays,
     hashes, and provenance records.
   - Uses protected branches and mandatory admission review.
   - Is the only information channel into implementation.

3. **Implementation repository**
   - Contains the new Go module, tests derived from exchange artifacts, build
     automation, release metadata, and Apache-2.0 license files.
   - Denies network access to the reference repository in CI and developer
     environments.
   - Rejects commits without contributor provenance attestations.

Chat transcripts, issue trackers, shared drives, package caches, and agent
context are information channels and follow the same separation as source
repositories.

### 4.3 Artifact admission

Every exchange artifact has a machine-readable manifest containing:

- immutable artifact identifier and SHA-256 digest;
- artifact type and schema version;
- authoring role and reviewer identities;
- generation command and tool versions;
- complete input list with license and ownership classification;
- statement that no denied source text is embedded;
- legal/provenance disposition: admitted, quarantined, or rejected;
- approval timestamp and superseded artifact identifiers.

Admitted inputs are limited to:

- public hardware and software standards approved for the program;
- sponsor-authored functional requirements;
- sponsor-owned or permissively licensed test programs;
- approved corpus programs used under their recorded licenses for black-box
  observation, while their binaries remain outside exchange;
- black-box inputs and observable outputs generated from approved programs;
- numerical limits and interoperability facts approved by the custodian;
- new explanatory text written for the exchange repository;
- generated hashes, traces, and binary fixtures whose inputs are documented.

Denied inputs include:

- ProjectLegends or DOSBox-X source, headers, tests, documentation, comments,
  disassembly, debug symbols, or generated source-derived diagrams;
- copied identifiers, type layouts, error prose, constants, tables, or file
  organization unless independently required by an admitted public standard;
- third-party game binaries, firmware, fonts, media, screenshots, or agent
  observations outside the corpus classification and disclosure policy;
- oracle crash dumps or logs containing source paths, symbols, or snippets;
- unreviewed AI output trained or prompted with denied material for the
  implementation task.

### 4.4 One-way publication workflow

1. The reference team proposes an experiment in the reference repository.
2. The experiment uses only an approved test program and declared inputs.
3. Raw oracle output remains reference-side.
4. The specification custodian converts the observation into a minimal
   functional statement or vector.
5. Automated scanners check manifests, SPDX identifiers, forbidden tokens,
   source-path leakage, binary types, and digests.
6. The legal/provenance reviewer admits or rejects the artifact.
7. An admitted artifact is merged into the exchange repository.
8. The implementation team imports the immutable exchange release by digest.
9. CI records which exchange release each implementation commit targets.

The implementation team may submit questions only through an exchange issue
template. Answers become new reviewed specification text or vectors; direct
conversation with the reference team about implementation details is not an
allowed channel.

### 4.5 Taint response

When a denied artifact reaches the implementation side:

1. freeze merges and releases;
2. preserve access logs and affected commit ranges;
3. quarantine affected branches and build artifacts;
4. identify every exposed implementation contributor;
5. obtain a documented legal/provenance decision;
6. replace affected contributors or independently recreate affected work when
   required;
7. rerun the complete clean-room and release audit before unfreezing.

History is never rewritten to conceal an incident.

## 5. Product architecture

### 5.1 Dependency direction

The headless nucleus is organized around a deterministic machine kernel:

~~~text
host adapter
    |
    v
public contract
    |
    v
machine coordinator
    +--> execution core
    +--> deterministic clock and scheduler
    +--> input queue
    +--> text/video surfaces
    +--> snapshot codec
    +--> state hasher
    |
    v
pure device interfaces
~~~

Dependencies point inward. The machine kernel imports no UI, OS window,
network, wall-clock, audio-device, database, or reference-oracle package.

### 5.2 Proposed Go package boundaries

| Package | Responsibility | Allowed dependencies |
|---|---|---|
| **legends** | Public Go contract, values, errors, capability discovery | Standard library value types |
| **machine** | Lifecycle and atomic orchestration of all subsystems | Contract plus internal subsystem interfaces |
| **clock** | Integer cycle accounting and stable event ordering | Standard library only |
| **input** | Validation and timestamped input queue | Contract and clock values |
| **display** | Canonical text cells, cursor, RGBA frame, dirty generations | Contract values |
| **snapshot** | Canonical versioned encoding, validation, atomic decode | Contract and subsystem state values |
| **statehash** | Domain-separated SHA-256 over observable state | Standard library crypto/sha256 |
| **testmachine** | Scripted execution core used only for contract development | Internal interfaces |
| **vectorcheck** | Exchange-vector loader and conformance runner | Public contract and schema decoder |

Future CPU, bus, memory, PIC, PIT, keyboard, BIOS, DOS, audio, and host adapter
packages join only after the nucleus contract is stable. The scripted
testmachine is never shipped as a claim of PC compatibility.

Only **legends** is a supported library import in M1. The remaining packages
are private implementation packages or command internals; their names and
layout are not compatibility promises.

### 5.3 Design constraints

- All observable time is an unsigned integer cycle count.
- Wall-clock time, goroutine scheduling, map iteration order, pointer values,
  host paths, and random sources never enter observable state.
- All externally supplied byte counts and dimensions are checked before
  allocation.
- Mutating calls are synchronous and atomic from the caller's perspective.
- The public machine is not concurrently mutable. A concurrent mutation
  returns a typed error rather than waiting in an order that depends on the Go
  scheduler.
- Snapshot encoding is canonical, versioned, bounded, and independent of Go
  struct layout.
- Core packages use the Go standard library by default. Every third-party
  module requires a written dependency decision.
- Resource ownership is explicit. Close is idempotent, and use after close
  returns a stable error.

## 6. Milestone decomposition

### M0 — Clean-room foundation

Exit criteria:

- the three repositories and access groups exist;
- exchange and implementation repositories contain Apache-2.0 LICENSE and
  NOTICE files plus SPDX policy;
- contributor disclosure and artifact-admission checks are mandatory;
- a deliberately contaminated sample is rejected by the admission pipeline;
- corpus classification, acquisition, and AI-evaluator disclosure policies are
  admitted while downloaded binaries remain outside the exchange repository;
- sponsor and legal/provenance reviewer sign the operating protocol.

### M1 — Headless deterministic nucleus

Exit criteria:

- the normative Go contract is implemented without cgo or unsafe;
- lifecycle, cycle stepping, input, capture, snapshot, and state-hash vectors
  pass on every mandatory platform;
- two independent executions of every vector produce identical checkpoint
  hashes;
- race, fuzz, vulnerability, coverage, and provenance gates pass;
- no implementation commit has reference-repository access in its provenance
  record;
- the release is labeled experimental and makes no PC-compatibility claim.

### M2 — Minimal real-mode machine

Adds a clean-room 8086/8088 execution core, 20-bit address space, reset vector,
deterministic bus, and sponsor-owned instruction corpus. Each opcode family is
admitted and implemented as a separate conformance increment.

### M3 — Bootable headless PC

Adds the minimum interrupt controller, interval timer, keyboard controller,
text display, firmware interface, and boot medium needed to run an approved
open test image. Firmware and test images require independent redistribution
approval.

### M4 — DOS services and richer devices

Adds DOS-facing services, file-system sandboxing, graphics modes, audio model,
and compatibility growth. Approved DOS corpus games are activated as their
required capabilities land. Each subsystem and game profile receives its own
specification, deterministic replay, and implementation plan.

### M5 — Host and interoperability adapters

Adds desktop or service hosts, a generated C adapter, process isolation, and
the Go side of the neutral `plgo-ai/1` adapter. The separately administered
evaluator deploys its isolated reference play agent against that adapter.
Optional legacy-facing interoperability follows only after separate legal and
compatibility review.

## 7. Decision rules

1. **Conformance before completeness.** A small admitted behavior set that is
   fully verified outranks a broad undocumented emulator.
2. **Determinism before real-time behavior.** Hosts translate real time into
   explicit cycle budgets outside the kernel.
3. **Canonical data before ABI compatibility.** The project owns stable
   schemas, not Go memory layouts.
4. **Standard library before dependencies.** A dependency must reduce more
   risk than its provenance and maintenance cost adds.
5. **Fail closed.** Missing provenance, unknown vector versions, incomplete
   test selection, and scanner failures block the gate.
6. **No silent demotion.** Any weakened gate or quarantined test requires a
   tracked owner, reason, expiry condition, and removal criterion.
7. **Questions become artifacts.** No implementation-relevant answer bypasses
   the exchange admission process.

## 8. Risks and controls

| Risk | Control |
|---|---|
| Expressive leakage into specifications | Independent custodian review, forbidden-token scans, minimal functional prose |
| Shared agent or developer context | Separate accounts, machines or isolated environments, and disclosure attestations |
| Oracle output embeds protected material | Approved sponsor-owned inputs, output normalization, manual artifact review |
| False confidence from differential tests | Independent properties, public-standard tests, metamorphic tests, fuzzing |
| Go runtime nondeterminism | Integer time, ordered collections, canonical serialization, cross-run/cross-platform replay |
| Snapshot decoder attack surface | Bounded lengths, checksums, atomic staging, native fuzz targets |
| Gate drift | One versioned preflight command used locally and in CI |
| Dependency compromise | Minimal dependencies, immutable versions, go.sum, vulnerability scan, SBOM, attestations |
| Corpus licensing or supply-chain ambiguity | Explicit classes, official allowlisted sources, hash pins, embedded-license audit, no abandonware mirrors |
| Nondeterministic or overconfident AI verdict | Informational exploration only; human review and three-run deterministic replay before gate promotion |
| Clean-room process blocks delivery | Small exchange releases, question SLA measured operationally, milestone-scoped specs |

## 9. Legal and licensing basis

This design is a process specification, not a legal opinion. U.S. Copyright
Office guidance distinguishes copyrightable program expression from
uncopyrightable ideas and functional concepts such as program logic,
algorithms, systems, and methods. The program nevertheless requires counsel to
approve the jurisdiction-specific observation, interoperability, artifact,
trademark, and distribution rules.

Apache-2.0 is applied unchanged. The implementation repository includes the
license text, a NOTICE file when attribution is required, and SPDX identifiers
on source and specification files. Contributions are accepted only from
contributors authorized to grant the license's copyright and patent rights.

Primary references:

- https://www.copyright.gov/register/tx-programs.html
- https://www.copyright.gov/circs/circ61.pdf
- https://www.apache.org/licenses/LICENSE-2.0
- https://www.apache.org/foundation/license-faq.html

## 10. Approval conditions

The design is ready for implementation planning only after the sponsor
confirms:

- the neutral contract rather than legacy ABI compatibility is the M1 target;
- the separate-team and three-repository topology is enforceable;
- Apache-2.0 ownership and contribution policy are authorized;
- the legal/provenance reviewer accepts the artifact-admission model;
- the linked behavioral, vector, quality, corpus, and reference-agent
  specifications are approved as a coherent set.
