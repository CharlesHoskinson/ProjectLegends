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

### 9.1 Initial local-model decision

As of 2026-07-15, the provisional primary local policy is
`Qwen/Qwen3.6-27B`. The first consumer-hardware profile is
`plgo-ref-qwen36-27b-q4km-v1`; the compact development profile is
`plgo-dev-qwen35-9b-q4km-v1`. This is a selection for qualification, not a
claim that a public benchmark has already proved Qwen3.6 best at the
ProjectLegends corpus.

The tiered decision is intentional:

| Role | Model and format | Initial local envelope | Use |
|---|---|---|---|
| Quality control | `Qwen/Qwen3.6-27B-FP8` | at least 48 GiB usable accelerator memory or an admitted multi-device host | Measures loss caused by the consumer quantization; scheduled qualification only |
| Primary local reference | `Qwen/Qwen3.6-27B`, `Q4_K_M` | one 24 GiB-class accelerator, 64 GiB system RAM, one inference slot | Canonical exploratory and replay-discovery policy after qualification |
| Compact development | `Qwen/Qwen3.5-9B`, `Q4_K_M` | one 12 GiB-class accelerator or a measured CPU/unified-memory host | Adapter, image transport, schema, report, and inexpensive smoke testing |

The primary choice is based on capabilities relevant to this workload rather
than generic chat rankings. The official Qwen3.6 card identifies an
Apache-2.0, 27-billion-parameter model with a vision encoder, a native 262,144
token context, and tool-calling support. In its vendor-reported same-harness
table, Qwen3.6-27B records 94.7 on V* and 70.3 on AndroidWorld. These are useful
visual-grounding and action proxies, but they are not DOS-game results and do
not override the corpus qualification in section 9.4.

The upstream source identity for the first primary candidate is:

~~~text
repository: Qwen/Qwen3.6-27B
revision:   6a9e13bd6fc8f0983b9b99948120bc37f49c13e9
license:    Apache-2.0
~~~

The quality-control source is `Qwen/Qwen3.6-27B-FP8` revision
`e89b16ebf1988b3d6befa7de50abc2d76f26eb09`. The compact source is
`Qwen/Qwen3.5-9B` revision
`c202236235762e1c871ad0ccb60c8ee5ba337b9a`. Each remains subject to the
complete shard and license capture required by `plgo.agent-model/1`.

For a quick local bootstrap, the 2026-07-15 Ollama
`qwen3.6:27b-q4_K_M` registry manifest was 710 bytes with SHA-256
`a50eda8ed977ab48a12431878896b27ffd5cef552c17af3317d9623b939a7f1e`.
Its GGUF model layer was 17,420,420,832 bytes with digest
`sha256:83c54730a5fea8a0958598c01617c1419c431e93b33bacf980b49a420c798926`.
The compact `qwen3.5:9b-q4_K_M` manifest had SHA-256
`6488c96fa5faab64bb65cbd30d4289e20e6130ef535a93ef9a49f42eda893ea7`;
its 6,594,462,816-byte model layer had digest
`sha256:dec52a44569a2a25341c4e4d3fee25846eed4f6f0b936278e3a3c900bb99d37c`.

An Ollama tag is a mutable discovery name, not an admitted identity. The
quantized artifact MUST NOT be represented as derived from the cited Qwen
revision until its conversion lineage is reviewed. The preferred canonical
artifact is independently rebuilt from the pinned official weights with a
pinned conversion and quantization recipe, reproduced by two builders, and
then named only by its final byte length and SHA-256. The captured Ollama
manifest is eligible as a bootstrap candidate under the same review; it is not
grandfathered by this document.

The official FP8 weights are the quantization-control lane. They are not the
consumer default because their approximately 31 GB weight footprint leaves no
safe room on a 24 GiB device for the vision path, recurrent or KV state,
scratch buffers, and driver reserve. Advertised context length is likewise a
capability ceiling, not a memory budget.

### 9.2 Model bundle and runtime pinning

Each runnable model profile has a `plgo.agent-model/1` manifest in the
evaluator repository. It records and hashes:

- profile ID, role, status, reviewer, and approval time;
- upstream repository, immutable revision, license evidence, and every source
  shard's byte length and SHA-256;
- conversion and quantization commands, tool commits, build flags, and output
  artifact digests, including a separate vision projector when present;
- tokenizer, processor, chat template, generation configuration, action JSON
  schema, legal-action validator, system prompt, policy, memory algorithm, and
  observation-encoding digests;
- runtime release and full commit, binary or container digest, backend, build
  flags, GPU offload, context and cache types, batch size, thread count,
  concurrency, and prompt-cache policy;
- OS, architecture, CPU ISA, GPU model and count, driver, CUDA, ROCm, Vulkan,
  or Metal versions as applicable;
- context length, maximum output tokens, seed, temperature, top-k, top-p,
  min-p, penalties, stops, and thinking-mode treatment; and
- measured peak committed RAM, peak device memory, warm and cold latency, and
  tokens per second on the admitted host.

No profile uses `latest`, an unqualified model name, a floating container tag,
or a branch name. A tag may be used to fetch only after its manifest and every
referenced blob have been resolved and compared with the admitted digests.
Downloaded weights live in an explicit content-addressed evaluator cache, not
in either source repository or a developer home-directory default.

The first portable reference runtime candidate is llama.cpp release `b10025`,
commit `a3e5b96ac5e278c390df429df0b68efcee3ee1b5`, because the Qwen project
explicitly lists llama.cpp text-and-vision support and llama.cpp provides local
GGUF loading plus constrained JSON-schema or grammar output across the target
host families. Its exact binary or locally built artifact is still pinned by
SHA-256. The first convenience runtime candidate is Ollama `v0.32.0`, commit
`f1a0ffd6219b5ef82aee77254f895b383efb5486`; it may be used for developer and
consumer-profile runs because it supports local image input, JSON-schema
structured output, tool calling, fixed seeds, and cloud disablement.

Runtime results are separate profiles. A llama.cpp result is not pooled with
an Ollama, vLLM, SGLang, Transformers, CPU, CUDA, ROCm, Vulkan, or Metal result
merely because the visible model name is the same. Exact model-token output is
not expected to be cross-runtime or cross-hardware deterministic.

The initial 24 GiB candidate starts with one inference slot, a 16,384-token
context, bounded output, a fixed list of inference seeds, and the model-bundle
sampling parameters. That profile, and any larger context, is admitted only
after the worst-case image and history workload fits with measured reserve. The
evaluator keeps a compact explicit state summary and recent action/outcome
window; it does not rely on silent context shifting. Image dimensions, integer
scaling, pixel format, frame-selection rule, and optional public text-cell
channel are part of the observation-encoding digest.

After acquisition, the evaluator runs with outbound egress denied. Ollama, when
used, sets `OLLAMA_NO_CLOUD=1`, binds only to loopback, has one loaded model and
one request slot, and reads a read-only admitted cache. The model server has no
adapter credential, corpus write path, source-tree mount, arbitrary filesystem
tool, shell, or network tool. `plgo-refplayer` requests a constrained action
proposal, validates it, and only then emits allowed `plgo-ai/1` operations.
Model reasoning is neither published nor retained; only the bounded intent,
confidence, proposal, validation result, and selected action enter the report
bundle.

### 9.3 Action and observation policy

The model emits exactly one schema-constrained proposal per decision. The
proposal may request another admitted observation, submit a bounded batch of
keyboard, mouse, or joystick events, advance a stated cycle budget, checkpoint,
or stop with a structured reason. It cannot name arbitrary functions. The
orchestrator rejects unknown actions, out-of-range coordinates, invalid key
edges, excessive holds, stale observation IDs, and cycle or action budgets that
exceed the objective.

Inference is paused time by default: no emulated cycle advances while the model
is thinking. A separate real-time research track MAY advance the target during
inference, but its results carry a different profile and are never pooled with
paused results. Wall-clock latency, stale-observation rate, and frames elapsed
are reported in both tracks and are not silently converted into emulated time.

Where the adapter exposes both canonical text cells and RGBA, the primary
policy may use both. Qualification also runs a bounded raw-RGBA-only,
text-only, and fused-observation ablation where applicable. No OCR, object
detector, hidden structured game state, memory read, or annotated click target
is smuggled into the primary lane. An oracle-perception lane is allowed only as
a named diagnostic on Class A fixtures whose author publishes the semantic
labels through the objective harness. It never reads reference or candidate
emulator internals and never becomes compatibility or conformance evidence.

### 9.4 Qualification, comparison, and replacement

The first M5 qualification MUST compare the provisional Qwen3.6 profile with:

- its official FP8 control, to measure consumer-quantization loss;
- `google/gemma-4-31B-it-qat-q4_0-gguf`, an official-quant Apache-2.0
  alternative;
- `Qwen/Qwen3-VL-30B-A3B-Instruct`, which has direct published game-agent
  evidence;
- `ByteDance-Seed/UI-TARS-1.5-7B`, a small computer-control specialist; and
- the compact Qwen3.5 profile plus deterministic no-op, random-valid-action,
  and scripted-oracle baselines.

Every challenger receives separate license and artifact admission. The list
may be updated before the test is unsealed, but it and all profile digests are
then frozen. The primary is selected by ProjectLegends evidence, not by the
vendor benchmark that nominated it.

The qualification corpus contains active Class B games plus sponsor-authored
Class A fixtures. It is split by title into prompt-development and locked
qualification sets. At least two Class A titles, their objectives, maps, and
seeds remain undisclosed until the prompt, memory policy, parser, and profiles
are frozen. This reduces memorization and prompt-tuning contamination. Class C
or D titles never become public model benchmarks.

For each applicable objective, each candidate runs the same five initial game
states or emulator seeds and three fixed inference seeds, for fifteen fresh-
overlay episodes. A smaller reliability subset runs eight repetitions. The
same initial states, observation encoding, action and cycle budgets, stopping
rules, and verifier versions are paired across models. No failed episode is
retried into a pass.

“State-verified” in this specification means a deterministic predicate over
the public lifecycle, text, RGBA, audio, approved guest-file, checkpoint, or
adapter-event channels in section 8. It never means reading guest memory,
registers, emulator objects, or source-team instrumentation. The scripted
oracle uses the same `plgo-ai/1` action and observation boundary, or a fully
predetermined action replay; it receives no privileged target state.

Eligibility is fail-closed. A profile must:

- match every model, runtime, prompt, policy, schema, and observation digest;
- start and finish offline with no model-server crash, OOM, or undeclared
  fallback on the admitted qualification host;
- produce complete, schema-valid episode and report bundles for every run;
- execute zero invalid or forbidden adapter operations, even when a game
  renders hostile instructions;
- pass every adapter-use, action-schema, image-transport, report, disclosure,
  state-clearing, and prompt-injection control fixture; and
- complete at least one locked text objective and one locked graphics
  objective in at least two of three repeated runs.

The legal-action validator, not the model, guarantees that an invalid proposal
is not executed. First-pass proposal validity, rejection and repair rates are
still reported; they cannot be hidden behind the validator.

Eligible models are ranked lexicographically, without a hand-tuned opaque
score, by:

1. macro-average normalized milestone progress with every game weighted
   equally;
2. state-verified full-objective success;
3. full-suite `pass^1` and reliability-subset `pass^3`, `pass^5`, and
   `pass^8`;
4. reviewed deterministic replay-candidate yield;
5. first-pass schema validity, legal-action rate, and recovery after rejection;
6. worst-game, genre, horizon, and observation-modality performance; and
7. action, token, latency, peak RAM, and peak device-memory efficiency.

`pass^k` is the estimated probability that all `k` repeated attempts succeed;
it is not `pass@k`, where one success among `k` attempts is sufficient.

Reports include game-clustered bootstrap 95 percent confidence intervals and a
paired comparison on the shared seeds. They also include progress-versus-
action curves, time/actions/tokens to each milestone, deaths, restarts,
irreversible errors, loops, stale or no-effect actions, and failure categories
for perception, grounding, timing, state tracking, memory, planning, invalid
action, premature stop, and budget exhaustion. Each expected challenge is
labeled `handled`, `blocked`, or `untested` so a capability that the trajectory
never reached is not blamed for the outcome.

A challenger replaces the canonical profile only when it clears every
eligibility gate, improves macro progress by at least five absolute percentage
points with a paired 95 percent confidence interval excluding zero, introduces
no greater-than-ten-point regression in any required observation or control
class, and passes provenance review. Replacement creates a new profile ID and
keeps all historical reports under their original identities. There is no
automatic model upgrade. The evaluator reviews challengers at least quarterly
and whenever a model, runtime, quantization, prompt, memory policy, adapter, or
observation encoding materially changes.

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
- model-profile and bundle digests, runtime and hardware profile, and the
  exact prompt, policy, parser, action-schema, memory, and observation-encoding
  digests;
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
8. `reference-model-qualification` runs the section 9.4 paired suite before a
   model profile is activated or replaced and at the scheduled challenger
   review. Model skill remains informational to product releases.

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
- the Qwen3.6 provisional primary, compact Qwen3.5 profile, immutable
  `plgo.agent-model/1` bundle, and paired replacement protocol;
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
- [Qwen3.6-27B](https://huggingface.co/Qwen/Qwen3.6-27B) provides the selected
  upstream model card, Apache-2.0 declaration, architecture, context,
  deployment, tool-use, and vendor evaluation evidence. The
  [Qwen3.6 repository](https://github.com/QwenLM/Qwen3.6) records supported
  local runtimes, including llama.cpp text and vision.
- [Qwen3.5-9B](https://huggingface.co/Qwen/Qwen3.5-9B) provides the compact
  profile's model card. The captured
  [Qwen3.6 Ollama tag](https://ollama.com/library/qwen3.6:27b-q4_K_M) and
  [registry manifest](https://registry.ollama.ai/v2/library/qwen3.6/manifests/27b-q4_K_M)
  provide bootstrap artifact evidence, not automatic provenance admission.
- [llama.cpp b10025](https://github.com/ggml-org/llama.cpp/releases/tag/b10025)
  and [Ollama v0.32.0](https://github.com/ollama/ollama/releases/tag/v0.32.0)
  identify the initial runtime candidates. Ollama separately documents
  [vision](https://docs.ollama.com/capabilities/vision),
  [structured outputs](https://docs.ollama.com/capabilities/structured-outputs),
  [tool calling](https://docs.ollama.com/capabilities/tool-calling), and
  [local-only operation](https://docs.ollama.com/faq).
- [Gemma 4](https://ai.google.dev/gemma/docs/core/model_card_4),
  [Qwen3-VL-30B-A3B-Instruct](https://huggingface.co/Qwen/Qwen3-VL-30B-A3B-Instruct),
  and [UI-TARS-1.5-7B](https://huggingface.co/ByteDance-Seed/UI-TARS-1.5-7B)
  provide the initial challenger model cards. Each challenger still requires
  independent license and artifact admission.
- [GameWorld](https://arxiv.org/abs/2604.07429) motivates paired computer-use
  and semantic-action tracks, state-verifiable progress, repeated runs, and
  action-validity measurement. [VideoGameBench](https://arxiv.org/abs/2505.18134)
  motivates title-level holdouts and separate paused and real-time results.
- [lmgame-Bench](https://arxiv.org/abs/2505.15146) identifies brittle visual
  perception, prompt sensitivity, and data contamination as game-agent
  evaluation confounders. [BALROG](https://proceedings.iclr.cc/paper_files/paper/2025/hash/f0b1515be276f6ba82b4f2b25e50bef0-Abstract-Conference.html)
  motivates fine-grained progress and observation-modality ablations.
