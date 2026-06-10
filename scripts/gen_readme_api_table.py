#!/usr/bin/env python3
"""
Generate README API and error-code tables from include/legends/legends_embed.h.

The output is deterministic and intended to be pasted between the generated
README markers.
"""

import argparse
import re
import sys
from pathlib import Path


API_RE = re.compile(r"^LEGENDS_API\s+\w+\s+(legends_\w+)\s*\(")
BRIEF_RE = re.compile(r"@brief\s+(.*)")
ERR_RE = re.compile(r"^#define\s+(LEGENDS_(?:OK|ERR_[A-Z0-9_]+))\s+(-?\d+)\s*(?:/\*\s*(.*?)\s*\*/)?\s*$")

ERROR_FALLBACKS = {
    "LEGENDS_OK": "Success",
    "LEGENDS_ERR_NULL_HANDLE": "Null handle passed",
    "LEGENDS_ERR_NULL_POINTER": "Null pointer argument",
    "LEGENDS_ERR_ALREADY_CREATED": "Single instance violation",
    "LEGENDS_ERR_NOT_INITIALIZED": "Instance not initialized",
    "LEGENDS_ERR_REENTRANT_CALL": "Step called from within callback",
    "LEGENDS_ERR_BUFFER_TOO_SMALL": "Buffer too small",
    "LEGENDS_ERR_INVALID_CONFIG": "Invalid configuration",
    "LEGENDS_ERR_INVALID_STATE": "Invalid state data",
    "LEGENDS_ERR_VERSION_MISMATCH": "API or save-state version mismatch",
    "LEGENDS_ERR_IO_FAILED": "I/O operation failed",
    "LEGENDS_ERR_OUT_OF_MEMORY": "Allocation failed",
    "LEGENDS_ERR_NOT_SUPPORTED": "Operation not supported",
    "LEGENDS_ERR_INTERNAL": "Internal error",
    "LEGENDS_ERR_WRONG_THREAD": "Called from non-owner thread",
}


def clean(text: str) -> str:
    return " ".join(text.strip().split())


def parse_header(path: Path) -> tuple[list[tuple[str, str]], list[tuple[str, str, str]]]:
    functions: list[tuple[str, str]] = []
    errors: list[tuple[str, str, str]] = []
    pending_brief: str | None = None

    for line in path.read_text(encoding="utf-8").splitlines():
        stripped = line.strip()

        brief = BRIEF_RE.search(stripped)
        if brief:
            pending_brief = clean(brief.group(1))
            continue

        api_match = API_RE.match(stripped)
        if api_match:
            name = api_match.group(1)
            functions.append((name, pending_brief or "No @brief text found"))
            pending_brief = None
            continue

        err_match = ERR_RE.match(stripped)
        if err_match:
            name, value, comment = err_match.groups()
            description = clean(comment or ERROR_FALLBACKS.get(name, "Error code"))
            errors.append((name, value, description))

    return functions, errors


def emit(functions: list[tuple[str, str]], errors: list[tuple[str, str, str]]) -> str:
    lines: list[str] = []
    lines.append("<!-- BEGIN GENERATED: legends-api-table -->")
    lines.append(f"Generated from `include/legends/legends_embed.h` ({len(functions)} `LEGENDS_API` functions).")
    lines.append("")
    lines.append("| Function | Description |")
    lines.append("|----------|-------------|")
    for name, brief in functions:
        lines.append(f"| `{name}` | {brief} |")
    lines.append("<!-- END GENERATED: legends-api-table -->")
    lines.append("")
    lines.append("## Error Codes")
    lines.append("")
    lines.append("<!-- BEGIN GENERATED: legends-error-table -->")
    lines.append(f"Generated from `include/legends/legends_embed.h` ({len(errors)} public status codes).")
    lines.append("")
    lines.append("| Code | Value | Description |")
    lines.append("|------|-------|-------------|")
    for name, value, description in errors:
        lines.append(f"| `{name}` | {value} | {description} |")
    lines.append("<!-- END GENERATED: legends-error-table -->")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Generate README API and error-code tables from legends_embed.h"
    )
    parser.add_argument(
        "--path",
        "-p",
        type=Path,
        default=Path("."),
        help="Repository root path (default: .)",
    )
    parser.add_argument(
        "--header",
        type=Path,
        default=Path("include/legends/legends_embed.h"),
        help="Header path relative to --path unless absolute (default: include/legends/legends_embed.h)",
    )
    args = parser.parse_args()

    root = args.path.resolve()
    header = args.header if args.header.is_absolute() else root / args.header

    if not header.is_file():
        print(f"ERROR: header not found: {header}", file=sys.stderr)
        return 1

    functions, errors = parse_header(header)
    if not functions or not errors:
        print("ERROR: failed to parse API functions or error codes", file=sys.stderr)
        return 1

    sys.stdout.write(emit(functions, errors))
    return 0


if __name__ == "__main__":
    sys.exit(main())
