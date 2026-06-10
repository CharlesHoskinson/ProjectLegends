# Entities index

Each entry: `[[Page]] — one-line summary`.

- [[Legends C API Layer]] — the 50-function public C ABI; strongest-engineered layer with joystick, reentrancy-coverage, and documentation soft spots.
- [[IPC Runtime (Project Legends)]] — proxy/message/host out-of-process runtime; ~2,700 real lines that cannot boot end-to-end and diverge from in-process semantics.
- [[Engine Bridge (DOSBox-X)]] — facade over the 1.05M-line vendored engine; hosts the mem-01 overflow and the contested C2 stub linkage.
- [[Build & CI System (Project Legends)]] — broad sanitizer/fuzz/TLA+/packaging machinery whose gating, GPL enforcement, and release path are unwired or never-run.
- [[Project Legends Test Suite]] — ~4,600 TEST macros across 252 files; wide but under-enforced with weak oracles.
- [[Project Legends Documentation Corpus]] — documents of record split into a verified-fresh era and a drifted February era.
- [[CI Workflows (GitHub Actions)]] — the four workflow files: triggers, job tiers, caching, artifacts, and the five-way duplicate-build overlap with no concurrency control.
- [[Verification Lanes (Sanitizers, Fuzz, Coverage, Determinism)]] — per-lane enforcement reality: ASan/UBSan enforced-when-run, TSan/MSan allow-failure (MSan cannot run), corpus never persisted, coverage threshold tag-only and never triggered.
- [[Quality Gate Scripts & Hooks]] — the eleven check_*.py scripts, the one-check opt-in pre-commit hook, the never-run openspec CLI, and the graphify gate's allow-missing strictness.
- [[Local Dev Loop]] — what developers actually run vs the mandatory CI tier: 10 of 14 gate rows have no local counterpart by default and no single command replicates the tier.
