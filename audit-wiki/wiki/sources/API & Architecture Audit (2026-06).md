---
type: source
aliases: ["API Architecture Report"]
tags: [source, type/source, topic/audit]
created: 2026-06-09
updated: 2026-06-09
status: draft
title: API & Architecture Audit (2026-06)
authors: [Claude audit fleet]
url:
publisher:
published: 2026
accessed: 2026-06-09
source_type: report
covers:
  - "[[Legends C API Layer]]"
  - "[[IPC Runtime (Project Legends)]]"
  - "[[Build & CI System (Project Legends)]]"
  - "[[Project Legends Test Suite]]"
  - "[[IPC Trust Boundary Gaps]]"
  - "[[Licensing Inconsistency]]"
  - "[[Documentation Drift]]"
  - "[[Prior-Audit Remediation Status]]"
---

# API & Architecture Audit (2026-06)

## Summary

API surface and architecture audit of Project Legends (2026-06-09, baseline AUDIT.md 2026-02-24), assigning health grade C: the in-process C ABI (50 functions in include/legends/legends_embed.h) is professional and most prior findings are verified fixed, but the new IPC runtime split is unwired, unverified in CI, and semantically divergent from the in-process path. Eleven new findings (api-01 through api-11, four HIGH per the report) center on an IPC mode that cannot boot, non-identical runtime semantics, a version handshake that never crosses the process boundary, and module-DAG/licensing enforcement that lags the new architecture.

## Key takeaways

- Overall health grade C: the core C ABI is genuinely good for a single-instance, in-process, build-from-source embedder, but the headline architecture additions (IPC runtime, RuntimeHost facade) are unwired, unverified in CI, and divergent between backends.
- api-01 (HIGH): IPC mode cannot run end-to-end — ProxyConnection::connect() is invoked only by tests (src/legends_proxy/proxy_connection.cpp:13-51), so every proxied legends_* call returns LEGENDS_ERR_NOT_INITIALIZED and the app exits with EngineCreateFailed (src/app/application.cpp:909-917); the SDL2+IPC executable cannot even link (CMakeLists.txt:1173-1180 omits legends_app while src/main.cpp:9 needs legends::Application).
- The linux-ipc CI job builds headless-only and never builds project_legends, so neither the boot failure nor the link failure is caught (.github/workflows/ci.yml:95-127).
- api-02 (HIGH): the two runtimes diverge — six API functions are NOT_SUPPORTED over IPC (e.g. legends_set_log_callback at proxy_api.cpp:424-426, so logging silently disappears); legends_destroy(NULL) is a no-op in-process but destroys the live engine over IPC (proxy_api.cpp:81-83); roughly half the proxy functions skip handle validation (e.g. proxy_api.cpp:116-132); legends_capture_rgb silently skips the copy and returns LEGENDS_OK on a too-small buffer (proxy_api.cpp:214-233).
- api-03 (HIGH): the ABI/version handshake does not survive the IPC boundary — CreateReq drops api_version, struct_size, config_path, and working_dir (proxy_api.cpp:59-68), and the proxy discards HandshakeAck.protocol_version/engine_version (proxy_connection.cpp:41-43); dropping config_path means the app's DOS .conf is silently ignored in IPC mode.
- api-04 (MEDIUM, high consequence): ProxyConnection::request<> never checks msg_type or sequence_id on receive (proxy_connection.h:39-45), so a timed-out request leaves a stale response in the pipe and the next request reinterprets it as a different message type, desynchronizing the stream.
- api-05 ("installed package is broken for embedders") was rated HIGH in the report but was REFUTED by adversarial verification; its claims (never-installed aibox headers behind the 25 forwarding headers, uninstallable runtime_host implementation) should not be relied on.
- api-06 (MEDIUM): InProcessEngineRuntime and IpcEngineRuntime are byte-for-byte identical ~300-line subclasses (src/app/runtime_host.cpp:25-318 and 328-621); the facade covers only 32 of the 50 C APIs, and the public header include/legends/runtime_host.h is implemented in the app layer — an inverted layering.
- api-07 (MEDIUM): ModuleManifest.cmake declares DAG edges for six modules, but ModuleDAG.cmake still verifies only legends_core, legends_pal, and aibox_core (ModuleDAG.cmake:196-206, :124), so the license-critical constraints legends_proxy → legends_ipc only and legends_engine_host → legends_core;legends_ipc are declared but never enforced at configure time; legends_app is absent from the manifest entirely.
- api-08 (MEDIUM): legends_config_t evolution policy is self-contradictory — legends_embed.h:114 promises additive evolution but legends_create rejects any struct_size != sizeof(legends_config_t) exactly (legends_embed_api.cpp:829-833); the API grew from 22 to 50 functions since February while LEGENDS_API_VERSION_MINOR is still 0 and CHANGELOG.md has only [Unreleased].
- api-09 (MEDIUM): the README motivates multi-instance embedding but the design is explicitly single-instance (legends_embed.h:13, atomic CAS at legends_embed_api.cpp:803-819), and the IPC layer re-bakes the limit via a hard-singleton ProxyConnection (proxy_connection.cpp:8-11) and single g_handle (engine_dispatcher.cpp:13).
- api-10 (LOW): the GetStateHashReq handler serializes resp.hash even when the call failed, leaking up to 32 bytes of engine-host stack across the process boundary (engine_dispatcher.cpp:177-182); several protocol message types are dead or unsolicited.
- api-11 (LOW): the SDL3 project_legends target re-lists ~45 app sources inline (CMakeLists.txt:1211-1268) instead of linking legends_app, so every new app source must be registered in multiple places.
- Prior findings verified: C1 (27 duplicated header pairs), H5 (destroy fallback), L2 (unused error codes), and L4 (LEGENDS_ERROR macro collision) are resolved; L3 (HandleRegistry implemented but unused) is confirmed open — handles are still validated by pointer equality against a single g_active_instance (legends_embed_api.cpp:79-82) — and the IPC proxy reintroduces H5's permissive destroy across the process boundary.
- Documentation drift: README/ARCHITECTURE present IPC mode as a working build mode (ARCHITECTURE.md:547-554) while TODO.md records "GPL v2 Process Isolation 2/16"; semver exists on paper but has never been exercised.

## Covers

- [[Legends C API Layer]] — 50-function in-process C ABI judged professional (consistent two-call pattern, reachable error codes, deep-copied config), with a self-contradictory struct_size evolution policy and a single-instance constraint as remaining gaps.
- [[IPC Runtime (Project Legends)]] — the proxy/engine-host split is structurally sound but cannot boot in production, exposes divergent semantics from the in-process path, and never validates versions across the boundary.
- [[Build & CI System (Project Legends)]] — SDL2+IPC link failure, headless-only linux-ipc CI job that exercises neither failure, duplicated SDL3 source lists, and ModuleDAG verification that lags the declared module set.
- [[Project Legends Test Suite]] — a dedicated C-mode ABI test exists, but ProxyConnection::connect and HandleRegistry live only in tests, and no conformance suite runs the C ABI against both runtimes.
- [[IPC Trust Boundary Gaps]] — uncorrelated responses (no msg_type/sequence_id checks), unvalidated handshake versions, and up to 32 bytes of engine-host stack leaked via GetStateHashResp.
- [[Licensing Inconsistency]] — the MIT/GPL link constraints the licensing story depends on are declared in ModuleManifest but never enforced at configure time, leaving GPL leakage guarded only by an IPC-mode-only post-build check.
- [[Documentation Drift]] — README/ARCHITECTURE claim a working IPC build mode and multi-instance embeddability that the code does not deliver; CHANGELOG and semver discipline are unexercised.
- [[Prior-Audit Remediation Status]] — C1, H5, L2, L4 verified resolved at HEAD; L3 confirmed open; H5's behavior effectively regressed in the IPC proxy.
