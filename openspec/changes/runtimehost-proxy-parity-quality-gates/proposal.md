## Why

Capability status has become an architectural control surface. As proxy parity expands, the repository needs stronger drift detection so a public API cannot be claimed as supported without proxy code, dispatcher cases, tests, and documentation agreeing.

## What Changes

Add or strengthen gates around proxy parity:

- Capability truth validation for new proxy-supported APIs.
- A focused proxy parity report listing remaining `LEGENDS_ERR_NOT_SUPPORTED` proxy APIs.
- Graphify/runtimehost checks showing application direct bypasses remain exactly two lifecycle calls.
- QA artifact requirements for Gemini handoff.

## Scope

In scope:

- Scripts, docs, and tests that verify capability/proxy truth.
- CI wiring if a lightweight new check is added.

Out of scope:

- Implementing additional proxy APIs beyond the two parity OpenSpecs.
- Remote CI remediation unless the new checks reveal a direct failure.

## Audit Strategy

Codex will run the validators locally, inspect the matrix changes, and compare proxy code against dispatcher cases before accepting the Gemini handoff.
