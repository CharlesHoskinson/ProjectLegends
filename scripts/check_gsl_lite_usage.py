#!/usr/bin/env python3
"""
CI Gate: Verify gsl-lite usage follows library contract.

This script enforces the following rules:
1. No use of legacy header <gsl/gsl-lite.hpp> (conflicts with Microsoft GSL)
2. No gsl_FEATURE_GSL_COMPATIBILITY_MODE in public headers
3. gsl-lite types not exposed in public C ABI headers (legends_embed.h)

Run this in CI to prevent gsl-lite misuse from breaking the library contract.

Usage:
    python scripts/check_gsl_lite_usage.py [--path PATH]
"""

import argparse
import re
import sys
from pathlib import Path
from typing import List, Tuple


# ═══════════════════════════════════════════════════════════════════════════════
# Forbidden Patterns
# ═══════════════════════════════════════════════════════════════════════════════

FORBIDDEN_PATTERNS = [
    # Pattern, Error message, Applies to files matching
    (
        r'#\s*include\s*[<"]gsl/gsl-lite\.hpp[">]',
        "Use <gsl-lite/gsl-lite.hpp>, not <gsl/gsl-lite.hpp> (legacy header)",
        r'.*\.(cpp|hpp|h)$'
    ),
    (
        r'gsl_FEATURE_GSL_COMPATIBILITY_MODE',
        "Do not define gsl_FEATURE_GSL_COMPATIBILITY_MODE (affects API/ABI)",
        r'.*\.(cpp|hpp|h|cmake|txt)$'
    ),
]

# Direct gsl_lite:: usage (should use legends::gsl:: alias)
# Exclude the bridge header which defines the alias
DIRECT_GSL_LITE_PATTERN = (
    r'(?<!::)gsl_lite::',  # gsl_lite:: not preceded by ::
    "Use legends::gsl:: alias, not gsl_lite:: directly (see include/legends/gsl.hpp)",
    r'.*\.(cpp|hpp|h)$'
)
BRIDGE_HEADER_PATH = 'include/legends/gsl.hpp'

# Public headers where gsl-lite types must NOT appear
PUBLIC_HEADER_PATTERNS = [
    r'include/legends/legends_embed\.h',
    r'include/legends/ffi.*\.h',
]

GSL_TYPES_IN_PUBLIC_HEADERS = [
    (
        r'\bgsl::|gsl_lite::|not_null|span<',
        "gsl-lite types must not appear in public C ABI headers",
        PUBLIC_HEADER_PATTERNS
    ),
]


# ═══════════════════════════════════════════════════════════════════════════════
# Checker
# ═══════════════════════════════════════════════════════════════════════════════

def check_file(filepath: Path) -> List[Tuple[int, str, str]]:
    """Check a single file for forbidden patterns.

    Returns list of (line_number, line_content, error_message).
    """
    errors = []
    rel_path = str(filepath)

    try:
        content = filepath.read_text(encoding='utf-8', errors='replace')
    except Exception as e:
        return [(0, '', f"Could not read file: {e}")]

    lines = content.split('\n')

    # Check general forbidden patterns
    for pattern, message, file_pattern in FORBIDDEN_PATTERNS:
        if not re.search(file_pattern, rel_path):
            continue

        regex = re.compile(pattern)
        for i, line in enumerate(lines, 1):
            if regex.search(line):
                # Skip if it's in a comment
                stripped = line.lstrip()
                if stripped.startswith('//') or stripped.startswith('*'):
                    continue
                errors.append((i, line.strip(), message))

    # Check direct gsl_lite:: usage (excluding bridge header)
    pattern, message, file_pattern = DIRECT_GSL_LITE_PATTERN
    is_bridge_header = rel_path.replace('\\', '/').endswith(BRIDGE_HEADER_PATH)
    if re.search(file_pattern, rel_path) and not is_bridge_header:
        regex = re.compile(pattern)
        for i, line in enumerate(lines, 1):
            if regex.search(line):
                stripped = line.lstrip()
                if stripped.startswith('//') or stripped.startswith('*'):
                    continue
                errors.append((i, line.strip(), message))

    # Check public header restrictions
    for pattern, message, file_patterns in GSL_TYPES_IN_PUBLIC_HEADERS:
        is_public_header = any(
            re.search(fp, rel_path.replace('\\', '/'))
            for fp in file_patterns
        )
        if not is_public_header:
            continue

        regex = re.compile(pattern)
        for i, line in enumerate(lines, 1):
            if regex.search(line):
                stripped = line.lstrip()
                if stripped.startswith('//') or stripped.startswith('*'):
                    continue
                errors.append((i, line.strip(), message))

    return errors


def check_directory(root: Path) -> int:
    """Check all source files in directory.

    Returns number of errors found.
    """
    total_errors = 0

    # Find all source files
    patterns = ['**/*.cpp', '**/*.hpp', '**/*.h', '**/*.cmake', '**/CMakeLists.txt']
    files = []
    for pattern in patterns:
        files.extend(root.glob(pattern))

    # Exclude third-party/vendor directories
    exclude_dirs = ['build', 'cmake-build', 'third_party', 'vendor', 'external']
    files = [
        f for f in files
        if not any(excl in f.parts for excl in exclude_dirs)
    ]

    # Check each file
    for filepath in sorted(files):
        errors = check_file(filepath)
        if errors:
            print(f"\n{filepath}:")
            for line_num, line_content, message in errors:
                print(f"  Line {line_num}: {message}")
                print(f"    > {line_content[:80]}...")
                total_errors += 1

    return total_errors


# ═══════════════════════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(
        description='Check gsl-lite usage follows library contract'
    )
    parser.add_argument(
        '--path', '-p',
        type=Path,
        default=Path('.'),
        help='Root directory to check (default: current directory)'
    )
    args = parser.parse_args()

    root = args.path.resolve()
    if not root.exists():
        print(f"Error: Path does not exist: {root}")
        return 1

    print(f"Checking gsl-lite usage in {root}...")
    print("=" * 60)

    errors = check_directory(root)

    print("\n" + "=" * 60)
    if errors == 0:
        print("OK: No forbidden gsl-lite patterns found")
        return 0
    else:
        print(f"FAIL: Found {errors} violation(s)")
        return 1


if __name__ == '__main__':
    sys.exit(main())
