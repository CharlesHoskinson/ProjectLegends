#!/usr/bin/env python3
"""
Check that migration status only improves, never regresses.

This script compares the current globals_registry.yaml against a baseline
to ensure migration status doesn't regress (e.g., migrated -> pending).

Exit codes:
  0 - No regressions found (or no baseline to compare)
  1 - Regressions found or error
"""

import argparse
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    print("ERROR: pyyaml is required. Install with: pip install pyyaml")
    sys.exit(1)

# Status ordering: higher number = more progress
STATUS_ORDER = {
    'pending': 0,
    'in_progress': 1,
    'partial': 1,
    'migrated': 2,
    'deferred': 2,
}


def find_registry(start_path: Path) -> Path:
    """Find globals_registry.yaml."""
    candidates = [
        start_path / 'engine' / 'globals_registry.yaml',
        Path('engine/globals_registry.yaml'),
        Path('globals_registry.yaml'),
    ]
    for candidate in candidates:
        if candidate.exists():
            return candidate
    return Path('engine/globals_registry.yaml')


def find_baseline(start_path: Path) -> Path:
    """Find baseline_globals.yaml."""
    candidates = [
        start_path / '.github' / 'baseline_globals.yaml',
        Path('.github/baseline_globals.yaml'),
    ]
    for candidate in candidates:
        if candidate.exists():
            return candidate
    return Path('.github/baseline_globals.yaml')


def load_registry(path: Path) -> dict:
    """Load a YAML registry file."""
    with open(path, 'r', encoding='utf-8') as f:
        return yaml.safe_load(f) or {}


def get_status_map(registry: dict) -> dict:
    """Extract name -> status mapping from registry."""
    globals_list = registry.get('globals', [])
    return {
        g['name']: g.get('migration_status', 'pending')
        for g in globals_list
        if 'name' in g
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description='Check for migration status regressions'
    )
    parser.add_argument(
        '--path',
        type=Path,
        default=Path('.'),
        help='Root path to search from (default: current directory)'
    )
    parser.add_argument(
        '--registry',
        type=Path,
        help='Path to current globals_registry.yaml'
    )
    parser.add_argument(
        '--baseline',
        type=Path,
        help='Path to baseline_globals.yaml'
    )
    parser.add_argument(
        '-v', '--verbose',
        action='store_true',
        help='Show detailed comparison'
    )
    args = parser.parse_args()

    # Find files
    registry_path = args.registry or find_registry(args.path)
    baseline_path = args.baseline or find_baseline(args.path)

    # Check registry exists
    if not registry_path.exists():
        print(f"ERROR: Registry not found: {registry_path}")
        return 1

    # Check baseline exists
    if not baseline_path.exists():
        print(f"INFO: No baseline file found at: {baseline_path}")
        print("Skipping regression check. Create baseline with:")
        print(f"  cp {registry_path} {baseline_path}")
        print()
        print("OK: No baseline to compare against")
        return 0

    # Load both files
    try:
        current = load_registry(registry_path)
        baseline = load_registry(baseline_path)
    except Exception as e:
        print(f"ERROR: Failed to load YAML files: {e}")
        return 1

    # Get status maps
    current_status = get_status_map(current)
    baseline_status = get_status_map(baseline)

    # Check for regressions
    regressions = []
    improvements = []

    for name, old_status in baseline_status.items():
        new_status = current_status.get(name)

        if new_status is None:
            # Global was removed - this is OK
            if args.verbose:
                print(f"  [REMOVED] {name}")
            continue

        old_order = STATUS_ORDER.get(old_status, 0)
        new_order = STATUS_ORDER.get(new_status, 0)

        if new_order < old_order:
            regressions.append((name, old_status, new_status))
        elif new_order > old_order and args.verbose:
            improvements.append((name, old_status, new_status))

    # Check for new globals
    new_globals = []
    for name in current_status:
        if name not in baseline_status:
            new_globals.append(name)
            if args.verbose:
                print(f"  [NEW] {name}: {current_status[name]}")

    # Report improvements
    if args.verbose and improvements:
        print("\nImprovements:")
        for name, old, new in improvements:
            print(f"  {name}: {old} -> {new}")

    # Report regressions
    if regressions:
        print("ERROR: Migration status regressions detected!")
        print()
        print("Regressions:")
        for name, old, new in regressions:
            print(f"  - {name}: {old} -> {new}")
        print()
        print(f"Total: {len(regressions)} regressions")
        print()
        print("To fix:")
        print("  1. Restore the migration status to its previous value")
        print("  2. Or complete the migration work that was reverted")
        return 1

    # Success
    print(f"OK: No migration status regressions")
    print(f"    Baseline: {len(baseline_status)} globals")
    print(f"    Current:  {len(current_status)} globals")
    if new_globals:
        print(f"    New:      {len(new_globals)} globals added")
    return 0


if __name__ == '__main__':
    sys.exit(main())
