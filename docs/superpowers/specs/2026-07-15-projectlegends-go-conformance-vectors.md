<!--
SPDX-License-Identifier: Apache-2.0
Copyright 2026 Charles Hoskinson and Contributors
-->

# ProjectLegends Go Clean-Room Conformance Vectors

Date: 2026-07-15
Status: draft for sponsor and clean-room admission review
Vector schema version: 1
License: Apache-2.0

## 1. Purpose

Conformance vectors are the only reference-derived behavioral evidence that
can decide compliance with the neutral machine contract. They turn approved
black-box observations and independent requirements into deterministic,
reviewable test cases without giving the implementation team oracle access.

Approved game-compatibility replays and reports are a separate evidence class
defined by `2026-07-15-projectlegends-go-dos-corpus-and-reference-agent.md`.
They may inform compatibility claims but cannot change or waive contract
conformance.

This specification defines the exchange layout, schemas, generation controls,
runner semantics, versioning, and admission criteria.

JSON snippets in this document illustrate closed schema shapes. Example hashes,
commits, reviewer keys, and counts are deliberately non-admitted values; a real
release is valid only through the digest and admission rules below.

## 2. Core rules

1. A vector release is immutable and addressed by SHA-256.
2. Every file is Apache-2.0, sponsor-owned test data, or an approved generated
   fact with recorded provenance.
3. The implementation repository never runs the reference oracle.
4. Raw oracle logs never enter the exchange repository.
5. Every expected value is machine-checkable; explanatory prose is
   non-normative.
6. All uint64 and int64 JSON values are decimal strings to avoid JSON number
   precision loss.
7. Binary equality is represented by a required SHA-256 and, only when needed
   for replay, an admitted blob.
8. Unknown schema versions, operations, fields marked closed, or missing
   provenance fail closed.
9. Vector releases contain no third-party game package, game screenshot, game
   audio, save file, or AI-agent transcript. Deterministic game replays remain
   in the separately reviewed corpus namespace.

## 3. Release layout

~~~text
exchange/
  LICENSE
  NOTICE
  release.json
  schemas/
    release.schema.json
    provenance.schema.json
    case.schema.json
    operation.schema.json
    expectation.schema.json
  programs/
    <program-sha256>.bin
    <program-sha256>.provenance.json
  cases/
    <suite>/
      <case-id>/
        case.json
        operations.ndjson
        expectations.ndjson
        provenance.json
        blobs/
          <sha256>.bin
  SHA256SUMS
~~~

Paths use lowercase ASCII letters, digits, hyphen, underscore, slash, and dot.
Case IDs are globally unique and match:

~~~text
^[a-z][a-z0-9]*(?:-[a-z0-9]+)*$
~~~

No symlink, submodule, Git LFS pointer, executable, archive, encrypted file, or
file larger than 64 MiB is allowed in a vector release.

## 4. Release manifest

**release.json** has this closed shape:

~~~json
{
  "schema": 1,
  "contract_version": 1,
  "release_id": "m1-vectors-2026-07-15.1",
  "created_utc": "2026-07-15T00:00:00Z",
  "previous_release_sha256": null,
  "case_count": 1,
  "program_count": 1,
  "minimum_runner_version": "1.0.0",
  "admission_commit": "0123456789abcdef0123456789abcdef01234567"
}
~~~

Requirements:

- created_utc is RFC 3339 UTC with second precision.
- release_id is informational and unique; the release digest is authoritative.
- previous_release_sha256 is null for the first release and the exact prior
  digest thereafter.
- case_count and program_count equal the files present.
- admission_commit is the full protected-branch exchange commit.
- SHA256SUMS covers every regular file except SHA256SUMS itself and is sorted by
  path using byte ordering.

## 5. Provenance manifest

Every case and program has a provenance manifest:

~~~json
{
  "schema": 1,
  "artifact_id": "lifecycle-create-close",
  "artifact_sha256": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
  "classification": "black-box-functional-vector",
  "license": "Apache-2.0",
  "author_role": "specification-custodian",
  "generation": {
    "tool": "reference-vector-normalizer",
    "version": "1.0.0",
    "command_id": "lifecycle-v1"
  },
  "inputs": [
    {
      "id": "sponsor-program-basic-1",
      "sha256": "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
      "ownership": "sponsor-owned",
      "license": "Apache-2.0"
    }
  ],
  "source_exposure": "reference-team-only",
  "contains_denied_expression": false,
  "review": {
    "custodian": "custodian-key-1",
    "provenance_reviewer": "reviewer-key-1",
    "decision": "admitted",
    "decided_utc": "2026-07-15T00:00:00Z"
  }
}
~~~

The real manifests use stable reviewer key identifiers established by the
exchange repository. Personal email addresses are not required in released
vectors.

An artifact is consumable only when:

- decision is admitted;
- the manifest digest matches the referenced artifact;
- every input is admitted or listed as an approved public standard;
- contains_denied_expression is false;
- both reviewers are authorized at admission_commit.

## 6. Program artifacts

M1 programs use the PLGOPRG1 format defined by the headless-nucleus contract.
A program filename is its lowercase SHA-256 plus .bin. Program provenance
records how the program was authored and confirms that all visual text,
colors, and patterns are sponsor-owned.

The exchange admission checker parses every program independently and rejects:

- invalid magic, version, flags, lengths, coordinates, ordering, or opcodes;
- records outside the declared configuration limits of every referencing case;
- embedded text that is not declared in provenance;
- duplicate files with different provenance;
- a digest mismatch.

## 7. Case manifest

**case.json** is closed and contains:

~~~json
{
  "schema": 1,
  "case_id": "lifecycle-create-step-close",
  "suite": "lifecycle",
  "requirement_ids": [
    "HN-LC-001",
    "HN-ST-001"
  ],
  "contract_version": 1,
  "program_sha256": "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
  "config": {
    "memory_bytes": "65536",
    "clock_hz": "1000000",
    "max_pending_input": "32",
    "text_columns": "80",
    "text_rows": "25",
    "frame_width": "320",
    "frame_height": "200",
    "seed_hex": "0000000000000000000000000000000000000000000000000000000000000000"
  },
  "operation_count": 4,
  "expectation_count": 4,
  "tags": [
    "pr",
    "determinism"
  ]
}
~~~

Rules:

- suite and case_id satisfy the path grammar.
- requirement_ids are unique and sorted.
- the program digest names a program in the same release.
- every config field maps exactly to Config in contract version 1.
- operation_count equals the nonblank lines in operations.ndjson.
- expectation_count equals operation_count.
- tags are unique, sorted, and selected from pr, nightly, release, negative,
  determinism, corruption, boundary, or regression.
- Comments and blank lines are forbidden in NDJSON files.

## 8. Operations

Each line of **operations.ndjson** is a closed JSON object with sequence,
operation, and operation-specific arguments.

### 8.1 Common field

~~~json
{"sequence":"1","operation":"new"}
~~~

Sequence begins at 1 and increases by 1.

### 8.2 Operation catalog

| Operation | Arguments | Meaning |
|---|---|---|
| new | none | Call New using case config and program |
| config | none | Read normalized Config |
| current_cycle | none | Read CurrentCycle |
| queue_input | events | Queue the complete event array |
| pending_input | none | Read PendingInput |
| step | cycles | Step the requested decimal-string cycle budget |
| capture_text | none | Capture the text surface |
| capture_rgba | none | Capture the RGBA surface |
| frame_generation | none | Read generation |
| save | save_as | Save and bind returned bytes to a local blob name |
| load_local | load_from | Load bytes previously bound by save |
| load_blob | sha256 | Load an admitted blob |
| state_hash | none | Read StateHash |
| reset | none | Reset |
| has_capability | capability | Query a numeric capability |
| close | none | Close |

An input event is:

~~~json
{
  "at_cycle":"10",
  "sequence":"1",
  "kind":"text",
  "code":"0",
  "x":"0",
  "y":"0",
  "text":"A"
}
~~~

Allowed kind strings map one-to-one to the InputKind constants: key_down,
key_up, text, mouse_move, mouse_button_down, and mouse_button_up.

`text` is the normal valid-UTF-8 representation. A negative UTF-8 vector
replaces it with `text_hex`, an even-length lowercase hexadecimal string whose
decoded bytes are placed directly into the Go string. Exactly one of `text` or
`text_hex` is present. Non-text events use `text: ""` and cannot use
`text_hex`.

Local blob bindings exist only inside a case and are ASCII identifiers matching
the case-ID grammar. A local binding cannot overwrite another binding.

## 9. Expectations

Each line of **expectations.ndjson** has the same sequence as its operation.
The common fields are:

~~~json
{
  "sequence":"1",
  "error_code":"0",
  "state_unchanged":false
}
~~~

Error code zero means success. Nonzero values are decimal-string ErrorCode
values from contract version 1. Error text is never normative.

Operation-specific result fields are:

| Operation | Expected fields |
|---|---|
| new, reset, close, queue_input, load_local, load_blob | common fields only |
| config | normalized config object |
| current_cycle | cycle |
| pending_input | count |
| step | start_cycle, end_cycle, executed_cycles, processed_input, halted |
| capture_text | generation, columns, rows, cells_sha256, cursor |
| capture_rgba | generation, width, height, pixels_sha256 |
| frame_generation | generation |
| save | bytes_sha256, bytes_length, optional admitted blob_sha256 |
| state_hash | state_hash |
| has_capability | supported |

All hashes are lowercase 64-character SHA-256 hex.

Text cells are hashed over the row-major concatenation of CodePoint uint32,
Foreground uint32, Background uint32, and Attributes uint16 for each cell,
without the section count or cursor. RGBA pixels are hashed over the raw
row-major byte sequence. State hashes use the domain-separated algorithm in the
contract and are not re-hashed.

When state_unchanged is true, the runner records a state hash immediately
before and after the operation and requires equality. This field is REQUIRED
for every expected error against an active machine. A failed New instead
requires `machine_absent: true`. An operation rejected after Close requires
`machine_closed: true` and the runner verifies that Config and capabilities
remain coherent while every error-returning operation still returns ErrClosed.

## 10. Runner behavior

The implementation repository provides a command named **vectorcheck**.

Normative invocation:

~~~text
go run ./cmd/vectorcheck \
  -exchange <immutable-exchange-directory> \
  -tags pr,determinism \
  -json-out vector-results.json
~~~

The runner:

1. verifies release and file digests before parsing cases;
2. validates every schema before running any case;
3. sorts selected cases by suite then case_id;
4. runs each case in a fresh process when the release tag is present and MAY
   run PR cases in-process for speed;
5. compares only normative fields;
6. records toolchain, GOOS, GOARCH, GOMAXPROCS, module digest, exchange digest,
   and case result;
7. exits nonzero for a schema, provenance, digest, execution, or comparison
   failure;
8. produces no updated golden files.

The implementation team cannot approve or regenerate expected values.

## 11. Vector families

Each contract requirement is covered by complementary vector styles:

- **example vectors** for ordinary behavior;
- **boundary vectors** for each minimum, maximum, zero, and overflow edge;
- **negative vectors** for every externally inducible typed error; ErrInternal
  is covered by implementation-side invariant fault injection, never by a
  crafted public input;
- **metamorphic vectors** such as split-step equivalence and save/load
  equivalence;
- **determinism vectors** repeated across process, platform, architecture,
  toolchain, GOMAXPROCS, locale, and time zone;
- **corruption vectors** for every snapshot framing and integrity check;
- **regression vectors** for minimized fuzz failures;
- **sensitivity vectors** proving that meaningful config, input, program, and
  state changes alter expected results.

No conformance family relies only on oracle equality. At least one independent
invariant or metamorphic property accompanies each oracle-derived behavior
family.

## 12. Oracle generation

Oracle generation occurs only in the reference repository.

1. The reference team selects an admitted sponsor-owned test input.
2. The oracle runs in a pinned container or virtual machine with network
   disabled and a declared locale, time zone, clock source, and random seed.
3. The raw observation is stored reference-side with tool and binary digests.
4. The normalizer removes paths, symbols, prose, and nonfunctional metadata.
5. The custodian expresses the minimum expected functional fields.
6. The case is replayed at least twice from a clean environment.
7. Divergent observations are quarantined, not averaged or selected.
8. The provenance reviewer admits the normalized artifact.

The implementation team sees the admitted result only after it is published in
an exchange release.

## 13. Updates and disputes

- A vector is never edited after release. A correction creates a new release
  and records the superseded case digest.
- An implementation disagreement opens a structured exchange question with
  the case ID, observed result, and public contract interpretation.
- The implementation team submits no code excerpts with the question.
- The custodian responds with clarified specification text, a corrected vector,
  a new discriminating vector, or a statement that the implementation is
  nonconforming.
- Every response follows the normal admission workflow.
- Removing a vector requires a reason and a replacement when it covered a
  published requirement.

## 14. Admission test

A vector release is admissible only when a clean validation environment can:

1. verify all SHA-256 entries;
2. validate every JSON and NDJSON file against closed schemas;
3. parse every PLGOPRG1 program and snapshot blob with an independent validator;
4. prove all counts, references, names, orderings, and digests are consistent;
5. confirm every artifact has an admitted provenance manifest;
6. scan for denied source paths, symbols, licenses, archive formats, and
   executable content;
7. replay all vectors against the reference-side normalizer's abstract model;
8. generate a signed admission report tied to the exchange commit.

The implementation CI verifies the admission report and repeats checks 1
through 6 before executing vectors.
