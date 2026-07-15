<!--
SPDX-License-Identifier: Apache-2.0
Copyright 2026 Charles Hoskinson and Contributors
-->

# ProjectLegends Go — DOS Reference Corpus and AI Play Agent

Date: 2026-07-15
Status: draft for sponsor and clean-room admission review
Protocol version: `plgo-ai/1`
License: Apache-2.0

## 1. Decision and purpose

ProjectLegends will maintain a hash-pinned corpus of legally classified DOS
games and a black-box reference agent that plays them exclusively through a
neutral AI adapter. The corpus measures system-level compatibility and feature
coverage. It does not replace the deterministic conformance vectors or make
game behavior part of the M1 nucleus contract.

The first public corpus is drawn from the official FreeDOS package repository.
It deliberately spans text and graphics modes, real and protected mode,
keyboard and mouse input, timing-sensitive play, persistent files, long-running
state, and later audio support. Commercial games may be evaluated only from
user-supplied copies in private runs.

The reference agent explores games and reports evidence. An AI judgment never
becomes a required gate by itself. A discovered path or defect becomes a gate
only after it is reduced to a deterministic replay with machine-checkable
assertions and reviewed provenance.

The key words MUST, MUST NOT, REQUIRED, SHALL, SHALL NOT, SHOULD, SHOULD NOT,
RECOMMENDED, MAY, and OPTIONAL are interpreted as described by RFC 2119 and
RFC 8174 when written in uppercase.

## 2. Relationship to the clean-room program

This document is a companion to:

- `2026-07-15-projectlegends-go-cleanroom-program-design.md`;
- `2026-07-15-projectlegends-go-headless-nucleus-contract.md`;
- `2026-07-15-projectlegends-go-conformance-vectors.md`; and
- `2026-07-15-projectlegends-go-quality-gates.md`.

Three evidence classes remain separate:

1. **Contract conformance** is decided by admitted, deterministic vectors.
2. **Game compatibility** is decided by reproducible corpus episodes and
   deterministic replays.
3. **Exploratory quality** is informed by AI-agent reports and human review.

A game passing does not prove the core contract. A game failing does not by
itself identify an implementation defect; the game, DOS environment, adapter,
reference emulator, and objective may each be the cause.

The Go implementation team receives only approved manifests, neutral machine
profiles, adapter contracts, objectives, replays, and behavioral evidence. It
does not receive legacy source, internal symbols, memory traces, debugger
output, raw reference-team prompts containing denied material, or suggestions
about implementation structure.

## 3. Corpus classes and admission

Every corpus entry has one of these classes:

| Class | Meaning | Public CI | Vendoring |
|---|---|---:|---:|
| A | Sponsor-authored DOS microgame or fixture under an approved permissive license | yes | yes |
| B | Third-party open-source or expressly redistributable package | yes after audit | only if separately approved |
| C | Freeware or shareware with use permission but restricted redistribution | private CI only | no |
| D | User-owned commercial title | local/private only | no |

Class is not inferred from terms such as “abandonware.” That term is not an
admission category. A package is inactive until its manifest contains:

- the exact acquisition URL and final resolved URL;
- byte length and SHA-256 digest;
- upstream title and version;
- source page and captured license evidence;
- the declared license text and a reviewed SPDX expression when one applies;
- redistribution, modification, screenshot, and remote-model-disclosure
  decisions;
- archive inventory and license-file digests;
- required DOS, CPU, memory, video, audio, and input capabilities;
- deterministic preparation and launch recipes;
- a named reviewer and approval timestamp.

An upstream package declaration is evidence, not the final project license
decision. Mixed code and data licenses are recorded separately. Removal or
expiry of an upstream download does not authorize substitution from an
unapproved mirror.

## 4. Repository and cache model

The exchange repository owns only metadata and artifacts approved for
publication:

~~~text
corpus/
  schema/game-manifest.schema.json
  schema/episode.schema.json
  schema/report.schema.json
  games/<game-id>/manifest.json
  games/<game-id>/objectives/*.json
  profiles/*.json
  replays/<game-id>/*.ndjson
  licenses/<sha256>.txt
  sources/<sha256>.json
agent/
  prompts/
  policies/
  schemas/
~~~

Downloaded packages, extracted trees, writable disks, screenshots, audio, and
save files are not committed by default. `corpusctl` stores them in a local
content-addressed cache chosen by an explicit command-line flag. It MUST NOT
silently use a developer's home directory or a shared package cache.

This abbreviated candidate manifest illustrates the canonical identity fields;
the closed schema additionally requires every applicable admission field from
section 3:

~~~json
{
  "schema": "plgo.game/1",
  "id": "freedos14-vitetris-055a",
  "title": "Vitetris",
  "version": "0.55a",
  "class": "B",
  "status": "candidate",
  "acquisition": {
    "url": "https://www.ibiblio.org/pub/micro/pc-stuff/freedos/files/repositories/1.4/games/vitetris.zip",
    "resolved_url": "https://www.ibiblio.org/pub/micro/pc-stuff/freedos/files/repositories/1.4/games/vitetris.zip",
    "bytes": 355263,
    "sha256": "53a0be1c42ae9f2cb3e501d9cbf5e4b9d1d829b934966e2ca0d6ab0486dd7843"
  },
  "license": {
    "upstream_declaration": "Simplified (2-Clause) BSD License",
    "evidence_path": "GAMES/VITETRIS/LICENCE.TXT",
    "evidence_sha256": "d4843dac6382d91d9a6e14f9ff608f2a71fe0f4b2e13f635b8dc0206b900847b",
    "redistribution": "pending-review"
  },
  "machine_profile": "pc386-text-v1",
  "launch_recipe": "dos-vitetris-v1",
  "objectives": ["boot", "play-basic", "save-or-exit"],
  "review": {
    "decision": "pending"
  }
}
~~~

Schema validation rejects unknown fields. Status is one of `candidate`,
`active`, `quarantined`, or `retired`. Only `active` entries run in required
lanes. An active entry replaces the pending review object with a reviewer,
decision, and RFC 3339 approval timestamp.

## 5. Acquisition and preparation security

`corpusctl fetch` MUST fail closed and enforce all of the following:

- HTTPS only, with certificate verification enabled;
- a per-entry hostname allowlist and at most three redirects, each to an
  allowlisted HTTPS host;
- the exact expected compressed byte length and a hard global limit;
- streaming SHA-256 verification before an artifact is admitted to cache;
- no automatic search, scraping, mirror discovery, or hash substitution;
- no credentials in manifests, URLs, logs, or reports;
- archive rejection for absolute paths, `..` traversal, alternate data
  streams, symlinks, hard links, device files, duplicate normalized paths,
  case-folding collisions, excessive file counts, or decompression bombs;
- extraction into a new empty directory followed by a complete inventory;
- preservation of license and notice files; and
- read-only source packages during episode preparation.

Version 1 global ceilings are 128 MiB compressed bytes, 1 GiB extracted bytes,
20,000 archive entries, 1,024 UTF-8 bytes per archive path, and a 1,000:1
expanded-to-compressed ratio. A manifest MAY impose lower limits. Raising a
global ceiling requires a corpus-policy version change and new extraction
security tests.

Preparation builds a fresh writable overlay or disk image from the verified
source package and a separately verified DOS environment. The recipe fixes file
order, timestamps, volume label, locale, keyboard layout, environment variables,
and configuration files. Every prepared image receives its own SHA-256 digest.
No episode reuses a prior writable overlay.

Network devices are absent by default. Games that genuinely exercise network
emulation use an isolated, deterministic virtual network with no route to the
host or Internet.

## 6. Initial downloadable reference set

The following Class B packages are the required seed-corpus candidates. The
digests identify the bytes fetched from the cited FreeDOS repository on
2026-07-15. A later upstream change MUST fail verification and trigger a normal
manifest-review change; it MUST NOT be accepted automatically.

| Game ID | Package and declared license | Bytes | SHA-256 | Primary exercise |
|---|---|---:|---|---|
| `freedos14-blkdrop-02` | [BlockDrop 0.2](https://www.ibiblio.org/pub/micro/pc-stuff/freedos/files/repositories/1.4/html/en/games/blkdrop/20250911.0/index.html), BSD 3-Clause | 170,597 | `af4670b67866db841292a8c52ba61334ea7745262e921f13ff814152d8387fcc` | 386, VGA, relative mouse, frame changes |
| `freedos14-flpybird-10a` | [Floppy Bird 1.0a](https://www.ibiblio.org/pub/micro/pc-stuff/freedos/files/repositories/1.4/html/en/games/flpybird/20250409.9/index.html), MIT | 2,073,159 | `a6f5c0c1bf5aa1746c9a335714c58835d4ce1ed90caa8de9072d9fb7f1d08ac9` | 16-bit COM, keyboard edges, timing sensitivity |
| `freedos14-vitetris-055a` | [Vitetris 0.55a](https://www.ibiblio.org/pub/micro/pc-stuff/freedos/files/repositories/1.4/html/en/games/vitetris/20250410.1/index.html), BSD 2-Clause | 355,263 | `53a0be1c42ae9f2cb3e501d9cbf5e4b9d1d829b934966e2ca0d6ab0486dd7843` | ANSI text, 16-bit and DPMI paths, keyboard |
| `freedos14-nethack-367` | [NetHack 3.6.7](https://www.ibiblio.org/pub/micro/pc-stuff/freedos/files/repositories/1.4/html/en/games/nethack/20250410.0/index.html), NetHack General Public License | 8,016,624 | `79e3f4e0f84a391f6a3488ba9bbb251a581df60996c0bc29822da3afbb6b54c8` | text UI, long sessions, random state, save/load files |
| `freedos14-boom-202a` | [Boom 2.02a with Freedoom](https://www.ibiblio.org/pub/micro/pc-stuff/freedos/files/repositories/1.4/html/en/games/boom/20250409.8/index.html), package declares GPL v2 | 8,026,461 | `aced9ebb171a5bda87fdfc04d8736de53fda8d816a0be286ef6ce38271ff1aa0` | 386/DPMI, VGA, mouse, high-rate rendering, later audio |
| `freedos14-kraptor-2004` | [KRaptor Apr-2004](https://www.ibiblio.org/pub/micro/pc-stuff/freedos/files/repositories/1.4/html/en/games/kraptor/20250527.3/index.html), MIT | 10,377,798 | `d14e3a780a488be427dbaa577aef8e878f2d62e8b6ab516902c4e9fc99c929cd` | protected mode, scrolling graphics, keyboard, later audio |
| `freedos14-wing-07a` | [Wing 0.7a](https://www.ibiblio.org/pub/micro/pc-stuff/freedos/files/repositories/1.4/html/en/games/wing/20250410.1/index.html), GPL v2 | 1,934,844 | `dfafabe3aacb6cdd503b34dcff4b90870a2ed7e2a7373ccf3b257e93f511affd` | menus, sprites, collision, digital audio behavior |
| `freedos14-vertigo-026a` | [Vertigo 0.26a](https://www.ibiblio.org/pub/micro/pc-stuff/freedos/files/repositories/1.4/html/en/games/vertigo/20250410.1/index.html), GPL v2 | 3,386,747 | `10f0beccb8f8126575a2511f8466e7006b71e48b75c0977f63a81549e97975dc` | protected mode, continuous controls, numerical simulation |

Canonical acquisition URLs are:

~~~text
https://www.ibiblio.org/pub/micro/pc-stuff/freedos/files/repositories/1.4/games/blkdrop/20250911.0/blkdrop.zip
https://www.ibiblio.org/pub/micro/pc-stuff/freedos/files/repositories/1.4/games/flpybird.zip
https://www.ibiblio.org/pub/micro/pc-stuff/freedos/files/repositories/1.4/games/vitetris.zip
https://www.ibiblio.org/pub/micro/pc-stuff/freedos/files/repositories/1.4/games/nethack.zip
https://www.ibiblio.org/pub/micro/pc-stuff/freedos/files/repositories/1.4/games/boom.zip
https://www.ibiblio.org/pub/micro/pc-stuff/freedos/files/repositories/1.4/games/kraptor/20250527.3/kraptor.zip
https://www.ibiblio.org/pub/micro/pc-stuff/freedos/files/repositories/1.4/games/wing.zip
https://www.ibiblio.org/pub/micro/pc-stuff/freedos/files/repositories/1.4/games/vertigo.zip
~~~

The flat FreeDOS URLs are mutable discovery locations; the digest, byte length,
and captured license evidence are the identity. Before activation, the corpus
steward MUST inspect every embedded component, including Freedoom data bundled
with Boom, rather than treating the package-level declaration as sufficient.

## 7. Feature profiles and initial objectives

All games first run in the deterministic `pc386-v1` profile family. Concrete
profiles such as `pc386-text-v1`, `pc386-vga-v1`, and
`pc386-vga-mouse-v1` inherit a fixed CPU model and clock, fixed RAM, fixed RTC
epoch, US English keyboard, deterministic PRNG seed, no networking, and audio
disabled unless the objective explicitly tests audio. Profile changes create a
new profile ID and new baselines.

Initial objectives are deliberately short and externally observable:

| Game | Required basic episode |
|---|---|
| BlockDrop | launch, establish a nonblank frame, move the mouse, click a removable group, observe a board or score change, exit |
| Floppy Bird | launch the COM program, pulse Space with explicit key-down and key-up events, observe flight and obstacle progression, exit or reach the action budget |
| Vitetris | start A-type play, move, rotate, hard-drop at least ten pieces, pause, resume, and exit |
| NetHack | create a named game, move for at least twenty turns, open inventory, save, restart from a fresh process, restore, and exit |
| Boom/Freedoom | enter a new game, move, turn, fire, reach normal level play, then exit; an audio variant additionally requires non-silent PCM |
| KRaptor | enter play, move, fire, observe an enemy or score-state change, and exit; an audio variant checks PCM activity |
| Wing | enter play, move, fire, observe combat-state change, and exit; known upstream exit or missing-audio behavior is recorded as reference evidence rather than silently normalized |
| Vertigo | start a flight, change throttle and attitude, observe a sustained instrument or horizon change, return to menu, and exit |

“Observe” means evidence from the adapter's public text, RGBA, audio, lifecycle,
or guest-file channels. It never means inspecting guest memory, registers, code,
or emulator internals. Each objective has an action budget, cycle budget, wall
clock safety timeout, allowed observation types, success predicates, and
explicit `inconclusive` conditions.

The seed corpus becomes required in stages:

- M1 and M2 validate only neutral fixtures and do not claim game support.
- M3 validates boot and DOS-environment preparation.
- M4 activates text and graphics game episodes as their required devices land.
- M5 makes the public AI adapter and reference-agent lane a release capability.

Unsupported objectives are reported as `not-applicable` with the missing
capability. They are not reported as passing.

## 8. Neutral AI adapter protocol

`plgo-ai/1` is a black-box control and observation protocol. It is a new,
technology-neutral contract, not a compatibility promise for any legacy C or
internal LLM interface. The reference side and Go side each implement an
adapter from their public machine controls without sharing adapter source.

The protocol uses UTF-8 NDJSON control messages. Each request has `schema`,
`request_id`, and `op`; every episode-scoped request also has `episode_id`.
Each response repeats the request fields and has either `ok: true` plus a result
or `ok: false` plus a stable error code. Unknown fields, duplicate JSON keys,
non-integer numbers, invalid UTF-8, oversized messages, and unsupported protocol
versions are rejected.

Cycle, sequence, byte-count, and budget values are unsigned decimal strings in
JSON. Signed axes are signed decimal strings. A control line is at most 1 MiB;
larger observations use content-addressed blobs with objective-specific limits
and never appear inline.

Required operations are:

| Operation | Purpose |
|---|---|
| `hello` | negotiate exactly one protocol version and enumerate capabilities |
| `open_episode` | verify an episode descriptor, prepare a fresh image, create the machine, and launch the game |
| `observe` | obtain lifecycle status and selected public observations |
| `read_blob` | read a bounded chunk of an episode-scoped observation by handle and digest |
| `act` | enqueue an ordered input batch without advancing hidden time |
| `advance` | advance an exact cycle budget and return actual progress |
| `checkpoint` | create a content-addressed episode checkpoint when supported |
| `restore` | atomically restore a checkpoint created for this episode |
| `reset` | rebuild the episode from its pristine prepared image |
| `close_episode` | close the machine and finalize adapter evidence |

Stable version 1 error codes are:

| Code | Meaning |
|---|---|
| `invalid-message` | malformed JSON, duplicate or unknown field, bad encoding, or missing field |
| `unsupported-version` | no exact protocol-version agreement |
| `duplicate-request` | request_id was already consumed on this connection |
| `invalid-state` | operation is not legal in the current episode state |
| `unknown-episode` | episode_id was never opened on this connection |
| `invalid-argument` | a well-formed operation has an invalid value |
| `unsupported-capability` | the target lacks an objective-requested operation or observation |
| `resource-limit` | a declared message, action, cycle, blob, or artifact limit would be exceeded |
| `integrity-failure` | corpus, image, checkpoint, or blob identity failed verification |
| `target-closed` | the target exited or was closed before the operation |
| `target-fault` | the target reported an abnormal execution failure |
| `host-timeout` | a host safety deadline expired; no emulated-time conclusion is implied |
| `forbidden` | the request attempts a channel denied by policy |
| `internal` | an adapter invariant failed and the episode is no longer trusted |

Request IDs are unique per connection. `hello` is valid before an episode;
`open_episode` creates exactly one fresh episode ID; all other operations except
`hello` require that ID. `close_episode` is idempotent for an ID opened on the
connection. After close, only `hello` and repeated `close_episode` are valid for
that ID. An `internal` error forces close before another episode is opened.

The adapter exposes these action kinds when the target advertises them:

- key down and key up using protocol-defined physical key identifiers;
- byte-exact text entry only when a text-entry capability exists;
- signed relative mouse motion and explicit mouse-button edges;
- absolute tablet motion only under a separate capability;
- joystick axis values and button edges; and
- deterministic media insertion or ejection declared by the episode.

Every action has an absolute emulated cycle and a strictly increasing sequence
number. The adapter MUST NOT synthesize a key release, repeat, delay, mouse
movement, or wait that is absent from the request. `advance` uses emulated
cycles, never wall-clock milliseconds. A host timeout is only a safety guard
and is recorded separately from emulated progress.

Public observation kinds are:

- lifecycle status, current cycle, exit reason, and stable adapter warnings;
- canonical text cells, cursor, and text-surface SHA-256;
- raw RGBA frame metadata, content-addressed bytes, and SHA-256;
- deterministic interleaved signed 16-bit little-endian PCM windows when audio
  is enabled, with start cycle, end cycle, sample rate, and channel count;
- machine capability flags and public state hash when the target provides one;
- hashes and approved contents of guest files explicitly named in the
  objective, such as a save file; and
- adapter event records such as reset, media change, or abnormal target exit.

An observation blob is retrieved only by its SHA-256 and episode-scoped handle.
Handles cannot address host paths. The adapter provides no operation for guest
memory, CPU registers, I/O trace, disassembly, symbols, logs containing internal
function names, arbitrary guest files, host files, environment variables, or
network access.

The adapter treats all guest-rendered text as untrusted data. Screen content
cannot alter the system prompt, objective, allowed operations, reporting
schema, or disclosure policy. It is framed as observation data with explicit
length and provenance.

## 9. Reference play agent

The reference agent is named `plgo-refplayer`. It runs in an evaluator
environment separate from both source teams and sees emulator instances only
through `plgo-ai/1`. The evaluator may target a reference build, a Go candidate,
or both in separate episodes. It never mounts source repositories.

For each run, the orchestrator fixes and records:

- game and prepared-image digests;
- machine profile, adapter version, target build digest, and capability set;
- objective version, initial checkpoint, emulation seed, and action budget;
- agent policy and prompt digests;
- model provider, model identifier, model revision when available, inference
  parameters, and inference seed when supported;
- whether observations may leave the evaluator machine; and
- timestamps and host identity used only for provenance, not comparison.

The agent loop is:

1. request the smallest sufficient observation;
2. state a short machine-readable intent and confidence;
3. submit explicit actions;
4. advance an explicit cycle budget;
5. evaluate the objective from admitted observations;
6. checkpoint important milestones; and
7. stop on success, a defined failure, an action or cycle budget, adapter loss,
   or an evidence-quality problem.

The agent MUST distinguish:

- `pass`: every required predicate has evidence;
- `fail`: a reproducible required predicate is contradicted;
- `inconclusive`: evidence, capability, or agent competence is insufficient;
- `not-applicable`: the objective declares a capability not yet implemented.

Repeated unchanged frames are not alone a hang. An emulator hang requires no
emulated progress or an explicit target fault; a game-level stall requires the
objective's defined progress predicate to expire. A black frame is evidence,
not a crash classification.

The agent does not open issues, modify baselines, approve corpus packages,
change gates, or communicate with implementation workers. It writes a report
bundle for sponsor review.

Evaluator outbound network access is disabled by default. Remote model
inference is allowed only when the game manifest and episode policy both permit
the selected observation classes to leave the evaluator, the endpoint is
allowlisted, and the disclosure decision is recorded. Class D observations are
local-model-only unless the rights holder gives a separate written approval.

## 10. Episode, replay, and report artifacts

Every episode produces a content-addressed bundle:

~~~text
episode.json
provenance.json
transcript.ndjson
observations/<sha256>
checkpoints/<sha256>
replay.ndjson
report.json
report.md
adapter-events.ndjson
~~~

`transcript.ndjson` is append-only and contains every protocol request and
response with observation bodies replaced by digests. `replay.ndjson` contains
only objective setup, explicit actions, exact advance budgets, observation
checkpoints, and machine-checkable assertions. It contains no model reasoning.

`report.json` includes:

- overall result and confidence;
- reached and missed milestones with evidence digests;
- cycle and action consumption;
- first divergent checkpoint for paired reference/candidate runs;
- crash, hang, adapter, visual, audio, input, save/load, and determinism
  findings in separate categories;
- a minimal reproduction when one exists;
- three-run replay stability results;
- capability coverage and untested features;
- suspected component stated as a hypothesis, never as fact without evidence;
- links by digest to screenshots, text frames, PCM windows, checkpoints, and
  guest-file evidence; and
- a natural-language summary that cannot override the structured result.

Reports redact model credentials, host paths, user identities, proprietary
guest data not approved for disclosure, and internal reference-team material.
Artifacts from Class C and D games remain private even if the adapter or agent
would otherwise publish them.

## 11. Comparison and clean-room publication

Paired evaluation uses the same game digest, prepared-image digest, profile,
objective, seed, initial checkpoint semantics, and deterministic replay. Exact
comparison is required for lifecycle results, accepted actions, cycle progress,
checkpoint restoration, and any channel declared canonical by its milestone.

Game screenshots and audio are compatibility evidence, not necessarily
byte-exact conformance data. Each objective states its comparator:

- exact hash;
- exact text cells after an allowed normalization;
- region-based RGBA equality;
- approved perceptual image metric and threshold;
- PCM activity, silence, frequency-band, or exact-window assertion; or
- a human-reviewed visual or auditory observation.

The evaluator sends the clean-room review function a candidate publication
bundle. Publication requires confirmation that it contains only:

- public corpus identity and license evidence;
- neutral objective and machine profile;
- deterministic action replay;
- externally observable outputs permitted by the corpus policy;
- normalized difference report; and
- no implementation recommendation or denied artifact.

The implementation team may dispute an admitted compatibility report with a
counter-replay. Resolution changes the objective or expected evidence through
the same versioned admission workflow used for conformance artifacts.

## 12. Quality gates

The following gates apply once their milestone is active:

1. `corpus-manifest` validates schemas, URLs, digests, license evidence,
   archive inventories, objectives, and profile references without downloading.
2. `corpus-fetch` downloads from a clean cache, verifies exact bytes, performs
   safe extraction, and reproduces prepared-image digests.
3. `adapter-contract` runs malformed-message, bounds, state-machine, capability,
   prompt-injection, and forbidden-operation tests against each adapter.
4. `game-smoke` runs one deterministic basic replay per active game.
5. `game-replay-stability` repeats every required replay three times from fresh
   overlays and requires identical declared canonical checkpoints.
6. `reference-agent-nightly` runs exploratory objectives and publishes reports
   as informational evidence.
7. `reference-agent-canary` evaluates a fixed small episode set after any agent,
   prompt, model, adapter, or observation-encoding change. Its required verdict
   covers protocol use, artifact completeness, and schema validity, not whether
   the model wins a game.

Required PR and release gates consume only deterministic replays. An
exploratory agent failure, model outage, refusal, or behavioral drift cannot
block a release unless a separately admitted replay demonstrates the product
failure.

A newly discovered replay is promoted only when:

- a human reproduces or independently reviews the evidence;
- it succeeds or fails consistently in three fresh runs;
- assertions do not depend on incidental frame timing or model prose;
- the replay has a stated feature and requirement mapping;
- reference behavior is documented, including known reference defects; and
- clean-room and corpus-policy review approve publication.

Required game lanes inherit the flake, quarantine, demotion, and evidence-
retention rules in the quality-gates specification. Quarantining a game does
not erase the underlying compatibility defect or permit a release claim that
the quarantined feature is supported.

## 13. Completion criteria

This design is ready for implementation planning when reviewers approve:

- the eight seed candidates and the Class A–D policy;
- `plgo.game/1`, episode, replay, and report schemas;
- deterministic acquisition and preparation rules;
- the `plgo-ai/1` black-box operation and observation boundary;
- the `plgo-refplayer` isolation and disclosure policy;
- staged M4/M5 activation and non-blocking exploratory-agent policy; and
- promotion of AI discoveries only through deterministic, reviewed replays.

The first implementation milestone for this document is complete when all
eight manifests validate, all packages fetch to the stated digests, at least
one text game and one graphics game have stable deterministic replays on the
reference target, and `plgo-refplayer` produces a schema-valid reviewed report
without access to emulator internals.

## 14. Primary sources

- [FreeDOS 1.4 download page](https://www.freedos.org/download/) identifies the
  official distribution and states that the LiveCD includes games.
- [FreeDOS 1.4 build report](https://www.ibiblio.org/pub/micro/pc-stuff/freedos/files/distributions/1.4/report.html)
  lists the game packages included in the distribution.
- [FreeDOS package format](https://help.freedos.org/docs/info/package.html)
  documents the package layout used by the corpus.
- The versioned package pages linked in the seed table provide upstream
  version, package metadata, declared copying policy, and downloads.
