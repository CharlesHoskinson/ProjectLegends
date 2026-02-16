#!/usr/bin/env python3
"""
Check that production code doesn't use current_context().

This script enforces the current_context() policy from Sprint 2:
- current_context() is forbidden in production code (.cpp AND .h files)
- Allowed only in: tests/*, *_compat.cpp, dosbox_context.cpp, machine_context.cpp
- Header files (.h) are NEVER allowed to use current_context() inline
  (function declarations and documentation comments are OK)

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

# Header files that are allowed to DECLARE (not use) current_context()
# These are the definition headers for the mechanism itself
HEADER_DECLARATION_ALLOWED = [
    r'dosbox_context\.h$',          # Declares current_context()
    r'machine_context\.h$',         # Declares MachineContext::current()
    r'error_model\.h$',             # Forward-references current_context_ptr()
]

# Pattern to detect current_context() usage (not just declaration/docs)
SEARCH_PATTERN = re.compile(r'\bcurrent_context\s*\(\s*\)')

# Pattern for function declarations (allowed in headers)
DECLARATION_PATTERN = re.compile(
    r'^\s*(\[\[nodiscard\]\]\s+)?'  # optional [[nodiscard]]
    r'(DOSBoxContext|MachineContext)\s*[&*]?\s+'  # return type
    r'current_context\s*\('         # function name
)


def is_allowed(filepath: str) -> bool:
    """Check if a file is allowed to use current_context()."""
    normalized = filepath.replace('\\', '/')
    for pattern in ALLOWED_PATTERNS:
        if re.search(pattern, normalized):
            return True
    return False


def is_header_declaration_allowed(filepath: str) -> bool:
    """Check if a header file is allowed to declare current_context()."""
    normalized = filepath.replace('\\', '/')
    for pattern in HEADER_DECLARATION_ALLOWED:
        if re.search(pattern, normalized):
            return True
    return False


def is_declaration_or_doc(line: str) -> bool:
    """Check if a line is a function declaration or documentation."""
    stripped = line.lstrip()
    # Skip comments and documentation
    if stripped.startswith('//') or stripped.startswith('*') or stripped.startswith('/*'):
        return True
    # Skip function declarations
    if DECLARATION_PATTERN.search(line):
        return True
    # Skip extern declarations
    if 'extern' in line and 'current_context' in line:
        return True
    return False


def check_file(filepath: Path, is_header: bool = False) -> List[Tuple[int, str]]:
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
                # For headers: also skip declarations and doc references
                if is_header and is_declaration_or_doc(line):
                    continue
                violations.append((i, line.strip()))
    except Exception as e:
        print(f"Warning: Could not read {filepath}: {e}", file=sys.stderr)
    return violations


def find_engine_dir(start_path: Path, subdir: str) -> Path:
    """Find an engine subdirectory."""
    script_dir = Path(__file__).parent
    candidates = [
        start_path / 'engine' / subdir,
        script_dir.parent / 'engine' / subdir,
        Path(f'engine/{subdir}'),
    ]
    for candidate in candidates:
        if candidate.exists():
            return candidate
    return Path(f'engine/{subdir}')


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

    engine_src = find_engine_dir(args.path, 'src')
    engine_include = find_engine_dir(args.path, 'include')

    violations = []
    checked_count = 0
    allowed_count = 0
    header_checked = 0

    # ─────────────────────────────────────────────────────────────────────
    # Check .cpp files in engine/src
    # ─────────────────────────────────────────────────────────────────────
    if engine_src.exists():
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
    else:
        print(f"Warning: Source directory not found: {engine_src}")

    # ─────────────────────────────────────────────────────────────────────
    # Check .h files in engine/include (PR #9 enforcement)
    # ─────────────────────────────────────────────────────────────────────
    if engine_include.exists():
        for h_file in engine_include.rglob('*.h'):
            relative_path = str(h_file)

            # Skip declaration headers (they define the mechanism)
            if is_header_declaration_allowed(relative_path):
                allowed_count += 1
                if args.verbose:
                    print(f"  [ALLOWED] {h_file} (declaration header)")
                continue

            header_checked += 1
            file_violations = check_file(h_file, is_header=True)

            if file_violations:
                violations.append((h_file, file_violations))
            elif args.verbose:
                print(f"  [OK] {h_file}")
    else:
        print(f"Warning: Include directory not found: {engine_include}")

    # ─────────────────────────────────────────────────────────────────────
    # Report results
    # ─────────────────────────────────────────────────────────────────────
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
        print("  3. Header files must NEVER use current_context() inline")
        print()
        print("Allowed .cpp files: tests/*, *_compat.cpp, dosbox_context.cpp, machine_context.cpp")
        print("Allowed .h files: dosbox_context.h, machine_context.h (declarations only)")
        return 1

    print(f"OK: No current_context() violations in production code")
    print(f"    Checked: {checked_count} .cpp files, {header_checked} .h files")
    print(f"    Allowed: {allowed_count} files")
    return 0


if __name__ == '__main__':
    sys.exit(main())
