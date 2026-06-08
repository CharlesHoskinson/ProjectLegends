## Why

The capability matrix previously allowed "proxy-supported" to mean "there is an IPC route." Codex had to correct `legends_joystick_event` to `proxy-partial` because routed transport is not the same as functional public support.

## What Changes

Refine capability truth semantics so routing, partial support, and full support are separate, machine-checked concepts.

Add or document statuses such as:

- `proxy-routed`
- `proxy-supported`
- `proxy-partial`
- `proxy-unsupported`
- `proxy-missing`

Then update the validator so it rejects overclaims where a proxy route exists but the underlying direct capability is partial or unsupported unless the manifest explicitly explains why the proxy is functionally stronger than direct mode.

## Scope

In scope:

- `docs/architecture/capability_truth.json` semantics update.
- Markdown matrix sync.
- Validator updates in `scripts/check_capability_matrix.py`.
- A generated or documented summary of routed-vs-supported proxy APIs.

Out of scope:

- Implementing missing capabilities.
- Changing public C ABI names.
- Reclassifying APIs without evidence.

## Audit Strategy

Codex will compare manifest status claims against direct implementation behavior, dispatcher routing, proxy body behavior, and tests. Claims must distinguish "transport route exists" from "public feature works."
