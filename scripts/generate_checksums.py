#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-2.0-or-later
# Copyright (C) 2024-2025 Charles Hoskinson and Contributors
#
# REQ-SEC-036: Generate SHA-256 checksums for release artifacts.

import hashlib
import sys
from pathlib import Path

EXTENSIONS = {".zip", ".tar.gz", ".gz", ".dmg", ".exe", ".msi", ".deb", ".rpm", ".pkg"}


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()


def is_artifact(path: Path) -> bool:
    name = path.name.lower()
    return any(name.endswith(ext) for ext in EXTENSIONS)


def generate(build_dir: str) -> None:
    build = Path(build_dir)
    if not build.is_dir():
        print(f"Error: {build_dir} is not a directory", file=sys.stderr)
        sys.exit(1)

    artifacts = sorted(p for p in build.iterdir() if p.is_file() and is_artifact(p))
    if not artifacts:
        print("No release artifacts found", file=sys.stderr)
        sys.exit(1)

    out = build / "SHA256SUMS.txt"
    lines = []
    for art in artifacts:
        digest = sha256_file(art)
        lines.append(f"{digest}  {art.name}")
        print(f"{digest}  {art.name}")

    out.write_text("\n".join(lines) + "\n")
    print(f"\nWritten to {out}")


def verify(sums_file: str) -> None:
    path = Path(sums_file)
    if not path.exists():
        print(f"Error: {sums_file} not found", file=sys.stderr)
        sys.exit(1)

    parent = path.parent
    ok = True
    for line in path.read_text().strip().splitlines():
        expected, name = line.split("  ", 1)
        fpath = parent / name
        if not fpath.exists():
            print(f"MISSING: {name}")
            ok = False
            continue
        actual = sha256_file(fpath)
        if actual == expected:
            print(f"OK:      {name}")
        else:
            print(f"FAILED:  {name}")
            ok = False

    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    if len(sys.argv) < 3:
        print(f"Usage: {sys.argv[0]} generate <build_dir>")
        print(f"       {sys.argv[0]} verify <SHA256SUMS.txt>")
        sys.exit(1)

    cmd = sys.argv[1]
    if cmd == "generate":
        generate(sys.argv[2])
    elif cmd == "verify":
        verify(sys.argv[2])
    else:
        print(f"Unknown command: {cmd}", file=sys.stderr)
        sys.exit(1)
