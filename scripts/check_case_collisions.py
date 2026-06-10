#!/usr/bin/env python3
"""
Scan tracked repository paths for case-insensitive filename collisions.

Exit codes:
  0 - No case-insensitive path collisions found
  1 - One or more collisions found, or the scan could not be completed
"""

import argparse
import subprocess
import sys
from pathlib import Path


def git_tracked_paths(root: Path) -> list[str] | None:
    try:
        result = subprocess.run(
            ["git", "-C", str(root), "ls-files"],
            check=True,
            capture_output=True,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError):
        return None

    return [line.strip() for line in result.stdout.splitlines() if line.strip()]


def filesystem_paths(root: Path) -> list[str]:
    skip_dirs = {".git", "build", ".claude"}
    paths: list[str] = []
    for path in root.rglob("*"):
        try:
            rel_parts = path.relative_to(root).parts
        except ValueError:
            continue
        if any(part in skip_dirs for part in rel_parts[:-1]):
            continue
        if path.is_file():
            paths.append(path.relative_to(root).as_posix())
    return paths


def find_collisions(paths: list[str]) -> dict[str, list[str]]:
    grouped: dict[str, list[str]] = {}
    for path in paths:
        key = path.replace("\\", "/").casefold()
        grouped.setdefault(key, []).append(path.replace("\\", "/"))
    return {
        key: sorted(values)
        for key, values in grouped.items()
        if len({value for value in values}) > 1
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Scan repository paths for case-insensitive collisions"
    )
    parser.add_argument(
        "--path",
        "-p",
        type=Path,
        default=Path("."),
        help="Root directory to scan (default: current directory)",
    )
    args = parser.parse_args()

    root_dir = args.path.resolve()
    if not root_dir.exists() or not root_dir.is_dir():
        print(f"ERROR: Scan path does not exist or is not a directory: {root_dir}")
        return 1

    paths = git_tracked_paths(root_dir)
    source = "git index"
    if paths is None:
        paths = filesystem_paths(root_dir)
        source = "filesystem"

    collisions = find_collisions(paths)
    if collisions:
        print("ERROR: Case-insensitive path collisions detected!")
        print("=================================================")
        for values in collisions.values():
            print("Collision group:")
            for path in values:
                print(f"  {path}")
        print(f"Found {len(collisions)} collision group(s) in {len(paths)} {source} path(s).")
        return 1

    print(f"OK: No case-insensitive path collisions found in {len(paths)} {source} path(s).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
