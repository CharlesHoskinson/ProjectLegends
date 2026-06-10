<!-- llm-wiki: v1 -->
# Project Legends Audit Wiki — wiki schema

**Domain:** End-to-end audit of the Project Legends embeddable x86 emulation framework (C:\projectLegends) — findings, risks, subsystem assessments, and sprint planning rationale.

This repository is an LLM-maintained knowledge wiki (Karpathy "LLM Wiki" pattern).
The `llm-wiki` skill operates it. Humans curate sources and ask questions; the
LLM writes and maintains all pages.

## Layout
- `raw/` — immutable source documents (never edited): audit-agent reports, build logs, excerpts of prior audits. `raw/assets/` for images.
- `wiki/sources|entities|concepts|syntheses/` — LLM-generated pages (+ `_index.md` each).
- `wiki/maps/` — topic MOCs. `wiki/overview.md` — evolving thesis (root MOC).
- `index.md` — router to category indexes. `log.md` — append-only history.

## Domain mapping
- **Sources** = one page per audit-agent report or prior-audit document ingested from `raw/`.
- **Entities** = subsystems under audit (legends core, engine, IPC layer, PAL, build system, test suite).
- **Concepts** = recurring findings/themes (e.g. global-state remnants, save/load integrity, ABI stability).
- **Syntheses** = cross-agent analyses, prioritization rationale, the sprint plan derivation.

## Workflows
- Ingest / Query / Lint / Init / Scrape are defined by the `llm-wiki` skill. Follow it.

## Conventions (summary; full rules in the skill's references/conventions.md)
- `[[wikilinks]]`; unique titles; every page ≥1 link + in a MOC + category index.
- Every claim on a concept/entity page carries an inline `^[from [[Source]] — "quote"]` marker.
- Contradictions append + flag (`status:` + `> [!conflict]`), never overwrite.
- One atomic git commit per ingest (stage only wiki paths).
