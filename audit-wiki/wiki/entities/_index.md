# Entities index

Each entry: `[[Page]] — one-line summary`.

- [[Legends C API Layer]] — the 50-function public C ABI; strongest-engineered layer with joystick, reentrancy-coverage, and documentation soft spots.
- [[IPC Runtime (Project Legends)]] — proxy/message/host out-of-process runtime; ~2,700 real lines that cannot boot end-to-end and diverge from in-process semantics.
- [[Engine Bridge (DOSBox-X)]] — facade over the 1.05M-line vendored engine; hosts the mem-01 overflow and the contested C2 stub linkage.
- [[Build & CI System (Project Legends)]] — broad sanitizer/fuzz/TLA+/packaging machinery whose gating, GPL enforcement, and release path are unwired or never-run.
- [[Project Legends Test Suite]] — ~4,600 TEST macros across 252 files; wide but under-enforced with weak oracles.
- [[Project Legends Documentation Corpus]] — documents of record split into a verified-fresh era and a drifted February era.
