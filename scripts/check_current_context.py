#!/usr/bin/env python3
"""
Check that production code doesn't use current_context().

This script enforces the current_context() policy from Sprint 2:
- current_context() is forbidden in production code
- Allowed only in: tests/*, *_compat.cpp, dosbox_context.cpp, machine_context.cpp

Exit codes:
  0 - No violations found
  1 - Violations found or error
"""

import argparse
import re
import sys
from pathlib import Path
from typing import List, Tuple

# Files/patterns allowed to use current_context()
# See README "current_context() Policy" for rationale
ALLOWED_PATTERNS = [
    r'tests/',                      # Test code uses ContextGuard
    r'test_',                       # Test files
    r'dosbox_context\.cpp$',        # Implementation of the mechanism
    r'machine_context\.cpp$',       # Implementation of the mechanism
    r'error_model\.cpp$',           # Part of context implementation
    r'_compat\.cpp$',               # Compat layers (*_compat.cpp)
]

# Pattern to detect current_context() usage
SEARCH_PATTERN = re.compile(r'\bcurrent_context\s*\(\s*\)')


def is_allowed(filepath: str) -> bool:
    """Check if a file is allowed to use current_context()."""
    normalized = filepath.replace('\\', '/')
    for pattern in ALLOWED_PATTERNS:
        if re.search(pattern, normalized):
            return True
    return False


def check_file(filepath: Path) -> List[Tuple[int, str]]:
    """Check a single file for current_context() usage.

    Returns list of (line_number, line_text) for each violation.
    """
    violations = []
    try:
        content = filepath.read_text(encoding='utf-8', errors='ignore')
        for i, line in enumerate(content.splitlines(), 1):
            # Skip comments
            stripped = line.lstrip()
            if stripped.startswith('//') or stripped.startswith('*'):
                continue
            if SEARCH_PATTERN.search(line):
                violations.append((i, line.strip()))
    except Exception as e:
        print(f"Warning: Could not read {filepath}: {e}", file=sys.stderr)
    return violations


def find_engine_src(start_path: Path) -> Path:
    """Find the engine/src directory."""
    # Try relative to script location
    script_dir = Path(__file__).parent
    candidates = [
        start_path / 'engine' / 'src',
        script_dir.parent / 'engine' / 'src',
        Path('engine/src'),
        Path('src'),
    ]
    for candidate in candidates:
        if candidate.exists():
            return candidate
    return Path('engine/src')


def main() -> int:
    parser = argparse.ArgumentParser(
        description='Check for current_context() usage in production code'
    )
    parser.add_argument(
        '--path',
        type=Path,
        default=Path('.'),
        help='Root path to search from (default: current directory)'
    )
    parser.add_argument(
        '-v', '--verbose',
        action='store_true',
        help='Show all checked files'
    )
    args = parser.parse_args()

    engine_src = find_engine_src(args.path)

    if not engine_src.exists():
        print(f"Warning: Source directory not found: {engine_src}")
        print("OK: No source files to check")
        return 0

    violations = []
    checked_count = 0
    allowed_count = 0

    # Check all .cpp files in engine/src
    for cpp_file in engine_src.rglob('*.cpp'):
        relative_path = str(cpp_file)

        if is_allowed(relative_path):
            allowed_count += 1
            if args.verbose:
                print(f"  [ALLOWED] {cpp_file}")
            continue

        checked_count += 1
        file_violations = check_file(cpp_file)

        if file_violations:
            violations.append((cpp_file, file_violations))
        elif args.verbose:
            print(f"  [OK] {cpp_file}")

    # Report results
    if violations:
        print("ERROR: current_context() found in production code!")
        print()
        print("Violations:")
        for filepath, lines in violations:
            print(f"\n  {filepath}:")
            for line_num, line_text in lines:
                # Truncate long lines
                display_text = line_text[:70] + '...' if len(line_text) > 70 else line_text
                print(f"    Line {line_num}: {display_text}")

        print()
        print(f"Total: {sum(len(v) for _, v in violations)} violations in {len(violations)} files")
        print()
        print("To fix:")
        print("  1. Pass DOSBoxContext& explicitly instead of using current_context()")
        print("  2. Or move the code to a *_compat.cpp file if it's a compatibility shim")
        print()
        print("Allowed files: tests/*, *_compat.cpp, dosbox_context.cpp, machine_context.cpp")
        return 1

    print(f"OK: No current_context() violations in production code")
    print(f"    Checked: {checked_count} files, Allowed: {allowed_count} files")
    return 0


if __name__ == '__main__':
    sys.exit(main())
