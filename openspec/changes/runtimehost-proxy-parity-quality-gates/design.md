## Design

Build on `scripts/check_capability_matrix.py` instead of replacing it. The existing script already checks that `proxy-supported` APIs do not directly return `LEGENDS_ERR_NOT_SUPPORTED` and that request types have dispatcher cases. Strengthen it only where needed for the new variable payload paths.

### Proxy Parity Report

Add a human-readable report under `docs/architecture/` or extend `docs/architecture/2026-06-08-public-capability-truth-matrix.md` with:

- Count of public C APIs.
- Count of proxy-supported, proxy-partial, and proxy-missing APIs.
- Remaining unsupported proxy APIs and explicit reason/deferred design owner.

### RuntimeHost Gate

Application-layer direct bypasses must remain exactly:

- `Application::init -> legends_create`
- `Application::shutdown -> legends_destroy`

No new application-layer direct `legends_*` call is allowed.

### CI

If a new script is added, wire it into `Sprint 2 Checks` only if it is deterministic, dependency-free, and fast.
