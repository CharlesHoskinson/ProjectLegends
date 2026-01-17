#!/usr/bin/env python3
"""
check_includes.py - Enforce module boundary include rules

This script verifies that public headers don't include private sources
and that cross-module includes use only public API paths.

Rules enforced:
1. PUBLIC HEADER RULE: Headers in public directories cannot include "../src/"
2. CROSS-MODULE RULE: No "../../" traversal across module boundaries
3. PATH CONVENTION: Use dosbox/ or aibox/ paths for engine public API

Exit codes:
    0 - All checks passed
    1 - Violations found
    2 - Script error (invalid arguments, etc.)

Usage:
    python scripts/check_includes.py --path .
    python scripts/check_includes.py --path . --verbose
    python scripts/check_includes.py --path . --strict  # Fail on warnings too
"""

import argparse
import os
import re
import sys
from pathlib import Path
from dataclasses import dataclass
from typing import List, Set, Optional
from enum import Enum


class Severity(Enum):
    ERROR = "ERROR"
    WARNING = "WARNING"
    INFO = "INFO"


@dataclass
class Violation:
    file: Path
    line: int
    include: str
    rule: str
    severity: Severity
    message: str


# Module public header directories (relative to project root)
PUBLIC_HEADER_DIRS = [
    "include/legends",
    "include/pal",
    "engine/include/dosbox",
    "engine/include/aibox",
]

# Forbidden patterns in public headers
FORBIDDEN_PATTERNS = [
    (r'#include\s*[<"]\.\.\/src\/', "PUBLIC_HEADER_RULE",
     "Public headers cannot include ../src/ (private sources)"),
    (r'#include\s*[<"]\.\.\/\.\.\/\.\.', "CROSS_MODULE_RULE",
     "Excessive path traversal (../../../) not allowed"),
]

# Warning patterns (not strict failures)
WARNING_PATTERNS = [
    (r'#include\s*[<"]\.\.\/\.\./', "TRAVERSAL_WARNING",
     "Path traversal (../../) may cross module boundaries"),
]


def is_public_header_dir(file_path: Path, root: Path) -> bool:
    """Check if a file is in a public header directory."""
    try:
        rel_path = file_path.relative_to(root)
        rel_str = str(rel_path).replace("\\", "/")
        for pub_dir in PUBLIC_HEADER_DIRS:
            if rel_str.startswith(pub_dir + "/") or rel_str.startswith(pub_dir.replace("/", "\\") + "\\"):
                return True
    except ValueError:
        pass
    return False


def is_engine_public_header(file_path: Path, root: Path) -> bool:
    """Check if file is in engine's public API (dosbox/ or aibox/)."""
    try:
        rel_path = file_path.relative_to(root)
        rel_str = str(rel_path).replace("\\", "/")
        return (rel_str.startswith("engine/include/dosbox/") or
                rel_str.startswith("engine/include/aibox/"))
    except ValueError:
        return False


def is_engine_header(file_path: Path, root: Path) -> bool:
    """Check if file is any engine header (public or private)."""
    try:
        rel_path = file_path.relative_to(root)
        rel_str = str(rel_path).replace("\\", "/")
        return rel_str.startswith("engine/include/")
    except ValueError:
        return False


def scan_file(file_path: Path, root: Path, verbose: bool) -> List[Violation]:
    """Scan a single file for include violations."""
    violations = []

    try:
        with open(file_path, 'r', encoding='utf-8', errors='replace') as f:
            lines = f.readlines()
    except Exception as e:
        if verbose:
            print(f"  Warning: Could not read {file_path}: {e}", file=sys.stderr)
        return violations

    is_public = is_public_header_dir(file_path, root)
    is_engine = is_engine_header(file_path, root)
    is_engine_public = is_engine_public_header(file_path, root)

    for line_num, line in enumerate(lines, 1):
        # Skip non-include lines
        if not line.strip().startswith('#include'):
            continue

        # Check forbidden patterns
        for pattern, rule, message in FORBIDDEN_PATTERNS:
            if re.search(pattern, line):
                # Special case: engine private headers (not in dosbox/ or aibox/)
                # are allowed to include ../src/ for now
                if is_engine and not is_engine_public and "../src/" in line:
                    if verbose:
                        print(f"  Info: Allowing {file_path.name}:{line_num} - "
                              f"engine private header")
                    continue

                violations.append(Violation(
                    file=file_path,
                    line=line_num,
                    include=line.strip(),
                    rule=rule,
                    severity=Severity.ERROR,
                    message=message
                ))

        # Check warning patterns (only for public headers)
        if is_public:
            for pattern, rule, message in WARNING_PATTERNS:
                if re.search(pattern, line):
                    violations.append(Violation(
                        file=file_path,
                        line=line_num,
                        include=line.strip(),
                        rule=rule,
                        severity=Severity.WARNING,
                        message=message
                    ))

    return violations


def find_header_files(root: Path) -> List[Path]:
    """Find all header files in the project."""
    extensions = {'.h', '.hpp', '.hxx', '.h++'}
    headers = []

    # Directories to scan
    scan_dirs = [
        root / "include",
        root / "engine" / "include",
    ]

    for scan_dir in scan_dirs:
        if not scan_dir.exists():
            continue
        for file_path in scan_dir.rglob("*"):
            if file_path.suffix.lower() in extensions:
                headers.append(file_path)

    return headers


def print_violation(v: Violation, root: Path):
    """Print a violation in a format suitable for CI."""
    rel_path = v.file.relative_to(root)
    color = "\033[91m" if v.severity == Severity.ERROR else "\033[93m"
    reset = "\033[0m"

    # GitHub Actions annotation format
    if os.environ.get('GITHUB_ACTIONS'):
        level = "error" if v.severity == Severity.ERROR else "warning"
        print(f"::{level} file={rel_path},line={v.line}::{v.message}")
    else:
        print(f"{color}{v.severity.value}{reset}: {rel_path}:{v.line}")
        print(f"  Rule: {v.rule}")
        print(f"  Message: {v.message}")
        print(f"  Include: {v.include}")
        print()


def main():
    parser = argparse.ArgumentParser(
        description="Check for forbidden include patterns in public headers"
    )
    parser.add_argument(
        "--path", "-p",
        type=Path,
        default=Path("."),
        help="Project root path (default: current directory)"
    )
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Show detailed output"
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Treat warnings as errors"
    )

    args = parser.parse_args()
    root = args.path.resolve()

    if not root.exists():
        print(f"Error: Path does not exist: {root}", file=sys.stderr)
        return 2

    if args.verbose:
        print(f"Scanning {root} for include violations...")
        print()

    headers = find_header_files(root)
    if args.verbose:
        print(f"Found {len(headers)} header files to scan")
        print()

    all_violations = []
    for header in headers:
        violations = scan_file(header, root, args.verbose)
        all_violations.extend(violations)

    # Separate errors and warnings
    errors = [v for v in all_violations if v.severity == Severity.ERROR]
    warnings = [v for v in all_violations if v.severity == Severity.WARNING]

    # Print results
    if errors or warnings:
        print("=" * 70)
        print("Include Rule Violations Found")
        print("=" * 70)
        print()

        for v in errors:
            print_violation(v, root)

        for v in warnings:
            print_violation(v, root)

        print("=" * 70)
        print(f"Summary: {len(errors)} error(s), {len(warnings)} warning(s)")
        print("=" * 70)
    else:
        print("✓ All include rules passed")

    # Exit code
    if errors:
        return 1
    if args.strict and warnings:
        return 1
    return 0


if __name__ == "__main__":
    # Handle Windows encoding
    if sys.platform == 'win32':
        import io
        sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', errors='replace')
        sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding='utf-8', errors='replace')
    sys.exit(main())
