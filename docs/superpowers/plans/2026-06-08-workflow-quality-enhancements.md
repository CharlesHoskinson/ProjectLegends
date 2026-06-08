# Workflow Quality Enhancements

Date: 2026-06-08

## What We Learned

The Flash implementation workflow is fast, but fast implementation needs stronger contracts. Codex found defects in four recurring categories:

- ABI parity details were incomplete: null handles, required output pointers, default initialization, and two-call buffer behavior.
- IPC tests were too happy-path-oriented: dynamic payload mismatch, truncation, odd typed-array payloads, and hostile counts needed auditor fixes.
- Capability truth overclaimed support: IPC routing was treated as functional support for `legends_joystick_event`.
- QA artifacts overstated results when post-audit changes altered test counts and classifications.

## Workflow Changes

1. OpenSpec designs must include negative and adversarial scenarios, not only success paths.
2. XML prompts must require edge-case tests before capability or QA status claims.
3. Capability documentation must distinguish transport routing from public support.
4. QA artifacts must include exact command output summaries and a section for failed or blocked commands.
5. Codex audit fixes should be promoted into permanent scripts or CI gates.

## Standing Gemini Instructions

- Do not classify an API as `proxy-supported` just because a message route exists.
- Do not mark a gate PASS until tests prove null-handle, null-output, buffer sizing, and malformed payload behavior where applicable.
- Prefer dependency-free Python validators for architecture truth and QA drift checks.
- Keep Graphify and capability reports synchronized after code changes.
- Return a QA artifact that identifies the top five Codex audit targets.
