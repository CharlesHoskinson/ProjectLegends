#!/usr/bin/env python3
"""Detect completed OpenSpec changes that should have been archived."""

import argparse
import re
import sys
from pathlib import Path


TASK_RE = re.compile(r"^- \[([ xX])\]")
PROTECTED_ACTIVE_PREFIXES = (
    "abi-parity-",
    "capability-truth-",
    "ipc-wire-",
    "runtimehost-",
)


def task_counts(path: Path) -> tuple[int, int]:
    checked = 0
    unchecked = 0
    for line in path.read_text(encoding="utf-8").splitlines():
        match = TASK_RE.match(line)
        if not match:
            continue
        if match.group(1).lower() == "x":
            checked += 1
        else:
            unchecked += 1
    return checked, unchecked


def is_protected_active_change(name: str) -> bool:
    return name.startswith(PROTECTED_ACTIVE_PREFIXES)


def scan(root: Path) -> tuple[list[tuple[str, int]], list[tuple[str, int]]]:
    changes = root / "openspec" / "changes"
    if not changes.is_dir():
        raise FileNotFoundError(f"OpenSpec changes directory not found: {changes}")

    stale: list[tuple[str, int]] = []
    protected_complete: list[tuple[str, int]] = []
    for change in sorted(p for p in changes.iterdir() if p.is_dir()):
        if change.name == "archive":
            continue
        tasks = change / "tasks.md"
        if not tasks.is_file():
            continue

        checked, unchecked = task_counts(tasks)
        if checked == 0 or unchecked != 0:
            continue

        if is_protected_active_change(change.name):
            protected_complete.append((change.name, checked))
        else:
            stale.append((change.name, checked))

    return stale, protected_complete


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Flag completed non-protected OpenSpec changes that remain active"
    )
    parser.add_argument(
        "--path",
        "-p",
        type=Path,
        default=Path("."),
        help="Repository root path (default: .)",
    )
    args = parser.parse_args()

    try:
        stale, protected_complete = scan(args.path.resolve())
    except FileNotFoundError as exc:
        print(f"ERROR: {exc}")
        return 1

    if stale:
        print("ERROR: completed OpenSpec changes still active under openspec/changes/:")
        for name, checked in stale:
            print(f"  - {name}: {checked} checked task(s), 0 unchecked")
        print("Move completed changes to openspec/changes/archive/ and baseline their specs.")
        return 1

    print("OK: no completed non-protected OpenSpec changes remain active.")
    if protected_complete:
        print("INFO: protected active June 2026 change(s) left unarchived by directive:")
        for name, checked in protected_complete:
            print(f"  - {name}: {checked} checked task(s), 0 unchecked")
    return 0


if __name__ == "__main__":
    sys.exit(main())
