#!/usr/bin/env python3
"""
Scan the repository recursively for unresolved Git merge conflict markers.
Enforces that no conflict markers are left in source files, config files, or build scripts.

Exit codes:
  0 - No unresolved conflict markers found
  1 - Unresolved conflict markers found
"""

import argparse
import sys
import re
from pathlib import Path

# Common binary and generated extensions to skip
SKIP_EXTENSIONS = {
    '.exe', '.dll', '.so', '.dylib', '.a', '.lib', '.obj', '.o',
    '.png', '.jpg', '.jpeg', '.gif', '.ico', '.pdf', '.zip', '.tar', '.gz',
    '.db', '.sqlite', '.pck', '.bin', '.img', '.iso', '.ima', '.sf2'
}

# Directories to skip
SKIP_DIRECTORIES = {
    '.git',
    'build',
    'external',
    '.claude',
}

# Files to explicitly exclude (like this script and documentation of this check)
SKIP_FILES = {
    'check_conflict_markers.py',
    '2026-06-08-gemini-35-flash-implementation-qa.md',
}

# Regex for Git conflict markers
# Start: <<<<<<< followed by space/newline (branch name/hash usually follows)
# Mid:   ======= exactly
# End:   >>>>>>> followed by space/newline
RE_START = re.compile(r'^<<<<<<<(?:\s|$)')
RE_MID   = re.compile(r'^=======\s*$')
RE_END   = re.compile(r'^>>>>>>>(?:\s|$)')

def is_binary(path: Path) -> bool:
    """Check if a file is binary by looking for null bytes in the first block."""
    try:
        with open(path, 'rb') as f:
            chunk = f.read(1024)
            return b'\x00' in chunk
    except Exception:
        return True  # Treat unreadable files as binary/unsafe

def scan_file(path: Path) -> list:
    """Scan a single file for conflict markers. Returns list of (line_num, line_content, type) tuples."""
    results = []
    try:
        with open(path, 'r', encoding='utf-8', errors='ignore') as f:
            for idx, line in enumerate(f, 1):
                stripped = line.strip()
                if RE_START.match(stripped):
                    results.append((idx, stripped, "START"))
                elif RE_MID.match(stripped):
                    results.append((idx, stripped, "MID"))
                elif RE_END.match(stripped):
                    results.append((idx, stripped, "END"))
    except Exception:
        # If we can't read it as text, ignore it
        pass
    return results

def main() -> int:
    parser = argparse.ArgumentParser(description='Scan repository for unresolved merge conflict markers')
    parser.add_argument(
        '--path',
        type=Path,
        default=Path('.'),
        help='Root directory to scan (default: current directory)'
    )
    parser.add_argument(
        '-v', '--verbose',
        action='store_true',
        help='Print scanned files'
    )
    args = parser.parse_args()

    root_dir = args.path.resolve()
    if not root_dir.exists() or not root_dir.is_dir():
        print(f"ERROR: Scan path does not exist or is not a directory: {root_dir}")
        return 1

    total_files = 0
    conflict_files_count = 0
    found_conflicts = {}

    # Traverse directory
    for path in root_dir.rglob('*'):
        if not path.is_file():
            continue

        # Check if any parent directory is in SKIP_DIRECTORIES
        parts = path.relative_to(root_dir).parts
        if any(d in SKIP_DIRECTORIES for d in parts[:-1]):
            continue

        # Skip specific file names or extensions
        if path.name in SKIP_FILES:
            continue
        if path.suffix.lower() in SKIP_EXTENSIONS:
            continue

        # Skip binary files
        if is_binary(path):
            continue

        total_files += 1
        if args.verbose:
            print(f"Scanning {path.relative_to(root_dir)}")

        file_conflicts = scan_file(path)
        # To avoid false alarms, we check if there are actual matching patterns
        # Typically a conflict has at least a START and an END (and usually a MID).
        # We flag a file if it contains any of the three, but to be safe and avoid any
        # single '=' lines, let's require at least a START or END marker, or a MID marker.
        # Actually, let's flag if it has START or END marker, since '=======' might still
        # occasionally appear in formatted code/comments.
        has_start = any(t == "START" for _, _, t in file_conflicts)
        has_end = any(t == "END" for _, _, t in file_conflicts)

        # If we have conflict markers (either START or END or both)
        if has_start or has_end:
            found_conflicts[path.relative_to(root_dir)] = file_conflicts
            conflict_files_count += 1

    # Print report
    if found_conflicts:
        print("ERROR: Unresolved merge conflict markers detected!")
        print("==================================================")
        for filepath, conflicts in found_conflicts.items():
            print(f"File: {filepath}")
            for line_num, content, mtype in conflicts:
                print(f"  Line {line_num} [{mtype}]: {content}")
            print()
        print(f"Found unresolved conflict markers in {conflict_files_count} file(s) (scanned {total_files} files).")
        return 1

    print(f"OK: No unresolved merge conflict markers found (scanned {total_files} files).")
    return 0

if __name__ == '__main__':
    sys.exit(main())
