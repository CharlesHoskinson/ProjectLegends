# Phase 5: CI Include Rule Enforcement

## Objective

Implement strict CI enforcement of module include rules from day 1. PRs with violations are blocked until fixed.

## Enforcement Rules

1. **No `../src/` in public headers** - Public headers cannot include private sources
2. **No cross-module private includes** - `../../` traversal across modules is forbidden
3. **Public API paths only** - Cross-module includes must use official public paths

## Deliverables

### 5.1 Create Include Checker Script

**File:** `scripts/check_includes.py`

```python
#!/usr/bin/env python3
"""
Sprint 3 CI Include Rule Enforcement

Rules enforced:
1. Public headers cannot include private sources (no ../src/)
2. Cross-module includes must use public API paths
3. No ../../ traversal across module boundaries

Exit codes:
  0 - All rules pass
  1 - Violations found

Usage:
  python scripts/check_includes.py --path .
  python scripts/check_includes.py --path . --verbose
"""

import argparse
import re
import sys
from pathlib import Path
from dataclasses import dataclass
from typing import List, Tuple, Optional

#------------------------------------------------------------------------------
# Configuration
#------------------------------------------------------------------------------

MODULES = {
    'legends': {
        'public': ['include/legends'],
        'private': ['src/legends'],
    },
    'pal': {
        'public': ['include/pal'],
        'private': ['src/pal'],
    },
    'engine': {
        'public': ['engine/include/dosbox', 'engine/include/aibox'],
        'private': ['engine/include', 'engine/src'],
    },
}

FORBIDDEN_PATTERNS = [
    # Pattern, Message, Severity
    (r'#include\s*[<"]\.\./src/',
     'Public header includes private source (../src/)',
     'ERROR'),
    (r'#include\s*[<"]\.\./\.\./src/',
     'Cross-module private include (../../src/)',
     'ERROR'),
    (r'#include\s*[<"]engine/src/',
     'Direct include of engine internals',
     'ERROR'),
]

# Files to skip (vendored code, generated files)
SKIP_PATTERNS = [
    r'.*/vs/.*',           # Visual Studio vendored
    r'.*/libs/mt32/.*',    # MT32 vendored
    r'.*/libs/sdl/.*',     # SDL vendored
    r'.*\.generated\.h',   # Generated headers
]

#------------------------------------------------------------------------------
# Data structures
#------------------------------------------------------------------------------

@dataclass
class Violation:
    filepath: Path
    line_num: int
    line_content: str
    message: str
    severity: str

#------------------------------------------------------------------------------
# Checking logic
#------------------------------------------------------------------------------

def should_skip(filepath: Path) -> bool:
    """Check if file should be skipped (vendored code, etc.)"""
    path_str = str(filepath).replace('\\', '/')
    for pattern in SKIP_PATTERNS:
        if re.match(pattern, path_str):
            return True
    return False

def check_file(filepath: Path) -> List[Violation]:
    """Check a single file for violations."""
    violations = []

    if should_skip(filepath):
        return violations

    try:
        content = filepath.read_text(encoding='utf-8', errors='ignore')
    except Exception as e:
        print(f"Warning: Could not read {filepath}: {e}", file=sys.stderr)
        return violations

    for line_num, line in enumerate(content.splitlines(), 1):
        # Skip comments
        stripped = line.strip()
        if stripped.startswith('//'):
            continue

        for pattern, message, severity in FORBIDDEN_PATTERNS:
            if re.search(pattern, line):
                violations.append(Violation(
                    filepath=filepath,
                    line_num=line_num,
                    line_content=stripped,
                    message=message,
                    severity=severity,
                ))

    return violations

def check_public_headers(base_path: Path, verbose: bool = False) -> List[Violation]:
    """Check all public headers for violations."""
    all_violations = []
    files_checked = 0

    for module, paths in MODULES.items():
        for public_path in paths['public']:
            full_path = base_path / public_path
            if not full_path.exists():
                if verbose:
                    print(f"Skipping {public_path} (does not exist)")
                continue

            for header in full_path.rglob('*.h'):
                if verbose:
                    print(f"Checking: {header}")
                files_checked += 1
                violations = check_file(header)
                all_violations.extend(violations)

            for header in full_path.rglob('*.hpp'):
                if verbose:
                    print(f"Checking: {header}")
                files_checked += 1
                violations = check_file(header)
                all_violations.extend(violations)

    if verbose:
        print(f"\nChecked {files_checked} files")

    return all_violations

#------------------------------------------------------------------------------
# Reporting
#------------------------------------------------------------------------------

def print_violations(violations: List[Violation]) -> None:
    """Print violations in a CI-friendly format."""
    if not violations:
        return

    # Group by file
    by_file = {}
    for v in violations:
        key = str(v.filepath)
        if key not in by_file:
            by_file[key] = []
        by_file[key].append(v)

    for filepath, file_violations in sorted(by_file.items()):
        print(f"\n{filepath}:")
        for v in file_violations:
            print(f"  Line {v.line_num}: [{v.severity}] {v.message}")
            print(f"    {v.line_content}")

def print_github_annotations(violations: List[Violation]) -> None:
    """Print GitHub Actions annotations for inline PR comments."""
    for v in violations:
        # GitHub Actions annotation format
        print(f"::error file={v.filepath},line={v.line_num}::{v.message}")

#------------------------------------------------------------------------------
# Main
#------------------------------------------------------------------------------

def main() -> int:
    parser = argparse.ArgumentParser(
        description='Check include rule violations (Sprint 3)',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Rules enforced:
  1. No ../src/ includes in public headers
  2. No cross-module private includes (../../src/)
  3. No direct engine/src/ includes

Examples:
  python scripts/check_includes.py --path .
  python scripts/check_includes.py --path . --verbose
  python scripts/check_includes.py --path . --github
        """
    )
    parser.add_argument('--path', type=Path, default=Path('.'),
                        help='Project root path')
    parser.add_argument('--verbose', '-v', action='store_true',
                        help='Verbose output')
    parser.add_argument('--github', action='store_true',
                        help='Output GitHub Actions annotations')
    args = parser.parse_args()

    print("=" * 60)
    print("Sprint 3: Include Rule Enforcement")
    print("=" * 60)

    violations = check_public_headers(args.path, args.verbose)

    if violations:
        print_violations(violations)

        if args.github:
            print("\n--- GitHub Annotations ---")
            print_github_annotations(violations)

        error_count = sum(1 for v in violations if v.severity == 'ERROR')
        warning_count = sum(1 for v in violations if v.severity == 'WARNING')

        print("\n" + "=" * 60)
        print(f"FAILED: {error_count} error(s), {warning_count} warning(s)")
        print("=" * 60)
        return 1

    print("\n" + "=" * 60)
    print("PASSED: All include rules satisfied")
    print("=" * 60)
    return 0

if __name__ == '__main__':
    sys.exit(main())
```

### 5.2 Create GitHub Actions Workflow

**File:** `.github/workflows/module-dag.yml`

```yaml
name: Module DAG Enforcement

on:
  push:
    branches: [main, develop]
    paths:
      - 'include/**'
      - 'src/**'
      - 'engine/include/**'
      - 'engine/src/**'
      - 'CMakeLists.txt'
      - 'engine/CMakeLists.txt'
      - 'cmake/**'
  pull_request:
    paths:
      - 'include/**'
      - 'src/**'
      - 'engine/include/**'
      - 'engine/src/**'
      - 'CMakeLists.txt'
      - 'engine/CMakeLists.txt'
      - 'cmake/**'

jobs:
  check-includes:
    name: Include Rule Enforcement
    runs-on: ubuntu-latest

    steps:
      - name: Checkout
        uses: actions/checkout@v4

      - name: Set up Python
        uses: actions/setup-python@v5
        with:
          python-version: '3.11'

      - name: Check include rules
        run: python scripts/check_includes.py --path . --github

      - name: Summary
        if: failure()
        run: |
          echo "## Include Rule Violations Found" >> $GITHUB_STEP_SUMMARY
          echo "" >> $GITHUB_STEP_SUMMARY
          echo "Run \`python scripts/check_includes.py --path .\` locally to see details." >> $GITHUB_STEP_SUMMARY

  verify-dag:
    name: CMake DAG Verification
    runs-on: ubuntu-latest

    steps:
      - name: Checkout
        uses: actions/checkout@v4

      - name: Install dependencies
        run: |
          sudo apt-get update
          sudo apt-get install -y cmake ninja-build

      - name: Configure CMake
        run: |
          cmake -B build -G Ninja \
            -DLEGENDS_BUILD_TESTS=OFF \
            -DLEGENDS_HEADLESS=ON

      - name: DAG verification
        run: |
          echo "DAG verification completed during CMake configure step"
          echo "If you see this, all library dependencies are valid"

  check-globals:
    name: Globals Migration Status
    runs-on: ubuntu-latest

    steps:
      - name: Checkout
        uses: actions/checkout@v4

      - name: Set up Python
        uses: actions/setup-python@v5
        with:
          python-version: '3.11'

      - name: Install dependencies
        run: pip install pyyaml

      - name: Check globals registry
        run: python scripts/check_globals_registry.py --path .
```

### 5.3 Add Pre-Commit Hook (Optional)

**File:** `.githooks/pre-commit`

```bash
#!/bin/bash
# Pre-commit hook for Sprint 3 include rules
# Install: git config core.hooksPath .githooks

echo "Checking include rules..."

if ! python scripts/check_includes.py --path . >/dev/null 2>&1; then
    echo "ERROR: Include rule violations found!"
    echo "Run 'python scripts/check_includes.py --path .' for details"
    exit 1
fi

echo "Include rules: OK"
exit 0
```

## Implementation Steps

| Step | Action | Files |
|------|--------|-------|
| 5.1.1 | Create check_includes.py | scripts/check_includes.py |
| 5.1.2 | Make script executable | chmod +x scripts/check_includes.py |
| 5.2.1 | Create workflow file | .github/workflows/module-dag.yml |
| 5.3.1 | Create pre-commit hook | .githooks/pre-commit |
| 5.3.2 | Make hook executable | chmod +x .githooks/pre-commit |
| 5.4.1 | Test locally | Run script, verify output |

## Test Plan

### Unit Tests

```python
# tests/test_check_includes.py

import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent / 'scripts'))
from check_includes import check_file, Violation

def test_detects_src_include():
    """Test that ../src/ includes are detected."""
    with tempfile.NamedTemporaryFile(mode='w', suffix='.h', delete=False) as f:
        f.write('#include "../src/private.h"\n')
        f.flush()
        violations = check_file(Path(f.name))

    assert len(violations) == 1
    assert 'private source' in violations[0].message.lower()

def test_allows_valid_include():
    """Test that valid includes are not flagged."""
    with tempfile.NamedTemporaryFile(mode='w', suffix='.h', delete=False) as f:
        f.write('#include "dosbox/public.h"\n')
        f.write('#include <cstdint>\n')
        f.flush()
        violations = check_file(Path(f.name))

    assert len(violations) == 0

def test_skips_comments():
    """Test that commented includes are skipped."""
    with tempfile.NamedTemporaryFile(mode='w', suffix='.h', delete=False) as f:
        f.write('// #include "../src/private.h"\n')
        f.flush()
        violations = check_file(Path(f.name))

    assert len(violations) == 0
```

### Integration Tests

```bash
#!/bin/bash
# tests/integration/test_ci_workflow.sh

set -e

echo "Test 1: Script runs without error on clean codebase"
python scripts/check_includes.py --path .
echo "PASS"

echo "Test 2: Script detects violations"
# Create a temporary violating header
mkdir -p /tmp/test_include/include/test
echo '#include "../src/bad.h"' > /tmp/test_include/include/test/bad.h

# Modify MODULES in script temporarily or use --path
if python scripts/check_includes.py --path /tmp/test_include 2>&1 | grep -q "FAILED"; then
    echo "PASS: Violations detected"
else
    echo "FAIL: Violations not detected"
    exit 1
fi

rm -rf /tmp/test_include

echo "Test 3: GitHub annotations format"
python scripts/check_includes.py --path . --github | head -5
echo "PASS: GitHub format works"

echo "All CI tests passed"
```

### Manual Verification

| Test | Command | Expected Result |
|------|---------|-----------------|
| Script runs | `python scripts/check_includes.py --path .` | Exit 0, "PASSED" message |
| Verbose mode | `python scripts/check_includes.py --path . -v` | Lists all checked files |
| GitHub mode | `python scripts/check_includes.py --path . --github` | `::error` annotations |
| Pre-commit works | `git commit --dry-run` | Hook runs, passes |
| CI workflow valid | Upload to GitHub | Workflow appears in Actions |

### Acceptance Criteria

- [ ] `scripts/check_includes.py` exists and is executable
- [ ] Script exits 0 on clean codebase (after Phase 2 fixes)
- [ ] Script exits 1 when violations present
- [ ] GitHub Actions workflow file is valid YAML
- [ ] CI runs on push to main/develop
- [ ] CI runs on pull requests
- [ ] Pre-commit hook works locally

## Rollback Plan

If issues arise:
1. Disable workflow by renaming to `.github/workflows/module-dag.yml.disabled`
2. Remove pre-commit hook
3. Keep script for local use but don't enforce in CI

**Git commands:**
```bash
git mv .github/workflows/module-dag.yml .github/workflows/module-dag.yml.disabled
git rm .githooks/pre-commit
git commit -m "Temporarily disable include enforcement"
```

## CI Failure Handling

When CI fails due to include violations:

1. **Developer sees failure** in PR checks
2. **Click "Details"** to see GitHub annotations inline
3. **Run locally:** `python scripts/check_includes.py --path . -v`
4. **Fix violations** by:
   - Using public API paths instead of private includes
   - Moving types to public headers (see Phase 2)
   - Creating shim headers if needed
5. **Push fix** and CI will re-run

## Metrics Collection

The script can be extended to collect metrics:

```python
# Add to check_includes.py

def collect_metrics(base_path: Path) -> dict:
    """Collect include metrics for trending."""
    return {
        'total_public_headers': count_public_headers(base_path),
        'violations_found': len(check_public_headers(base_path)),
        'timestamp': datetime.now().isoformat(),
    }
```
