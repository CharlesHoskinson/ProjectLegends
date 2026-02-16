#!/usr/bin/env python3
"""
Validate globals_registry.yaml and enforce baseline.

This script:
1. Verifies the statistics section matches actual counts
2. Compares against baseline to prevent regressions and unapproved additions
3. Reports migration progress

Exit codes:
  0 - Registry valid, no regressions
  1 - Statistics mismatch, regression, or unapproved addition
"""

import argparse
import sys
from pathlib import Path
from collections import Counter

try:
    import yaml
except ImportError:
    print("ERROR: pyyaml is required. Install with: pip install pyyaml")
    sys.exit(1)


def find_file(start_path: Path, *candidates: str) -> Path:
    """Find a file by trying multiple candidate paths."""
    for candidate in candidates:
        path = start_path / candidate
        if path.exists():
            return path
    # Try relative to script
    script_dir = Path(__file__).parent
    for candidate in candidates:
        path = script_dir.parent / candidate
        if path.exists():
            return path
    return start_path / candidates[0]


def load_registry(path: Path) -> dict:
    """Load a YAML registry file."""
    with open(path, 'r', encoding='utf-8') as f:
        return yaml.safe_load(f) or {}


def extract_globals_info(registry: dict) -> dict:
    """Extract name -> status mapping from registry."""
    result = {}
    for g in registry.get('globals', []):
        name = g.get('name', '')
        status = g.get('migration_status', 'pending')
        result[name] = status
    return result


# Status ordering: higher = more migrated
STATUS_ORDER = {
    'pending': 0,
    'in_progress': 1,
    'partial': 2,
    'deferred': 3,  # Intentionally left as global — acceptable endpoint
    'migrated': 4,
}


def main() -> int:
    parser = argparse.ArgumentParser(
        description='Validate globals registry and enforce baseline'
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
        help='Path to globals_registry.yaml'
    )
    parser.add_argument(
        '--baseline',
        type=Path,
        help='Path to baseline_globals.yaml'
    )
    parser.add_argument(
        '-v', '--verbose',
        action='store_true',
        help='Show detailed breakdown'
    )
    args = parser.parse_args()

    # Find registry
    registry_path = args.registry or find_file(
        args.path,
        'engine/globals_registry.yaml',
        'globals_registry.yaml',
    )

    if not registry_path.exists():
        print(f"ERROR: Registry not found: {registry_path}")
        return 1

    # Load registry
    try:
        registry = load_registry(registry_path)
    except Exception as e:
        print(f"ERROR: Failed to load registry: {e}")
        return 1

    globals_list = registry.get('globals', [])
    statistics = registry.get('statistics', {})

    # Count actual status values
    actual_counts = Counter()
    subsystem_counts = Counter()
    priority_counts = Counter()

    for g in globals_list:
        status = g.get('migration_status', 'pending')
        subsystem = g.get('subsystem', 'unknown')
        priority = g.get('priority', 'medium')

        actual_counts[status] += 1
        subsystem_counts[subsystem] += 1
        priority_counts[priority] += 1

    total_globals = len(globals_list)

    # ─────────────────────────────────────────────────────────────────────
    # Step 1: Verify statistics match actual counts
    # ─────────────────────────────────────────────────────────────────────
    errors = []
    if statistics:
        stated_total = statistics.get('total_globals', 0)
        if stated_total != total_globals:
            errors.append(f"total_globals: stated {stated_total}, actual {total_globals}")

        for status in ['migrated', 'pending', 'deferred', 'in_progress', 'partial']:
            stated = statistics.get(status, 0)
            actual = actual_counts.get(status, 0)
            if stated != actual:
                errors.append(f"{status}: stated {stated}, actual {actual}")

    # ─────────────────────────────────────────────────────────────────────
    # Step 2: Baseline comparison (prevent regressions and unapproved adds)
    # ─────────────────────────────────────────────────────────────────────
    baseline_path = args.baseline or find_file(
        args.path,
        '.github/baseline_globals.yaml',
        'baseline_globals.yaml',
    )

    baseline_errors = []
    if baseline_path.exists():
        try:
            baseline = load_registry(baseline_path)
            baseline_info = extract_globals_info(baseline)
            current_info = extract_globals_info(registry)

            # Check for new globals added without baseline update
            new_globals = set(current_info.keys()) - set(baseline_info.keys())
            if new_globals:
                baseline_errors.append(
                    f"New globals added without baseline review: {sorted(new_globals)}"
                )

            # Check for regressions (status going backwards)
            for name, current_status in current_info.items():
                if name in baseline_info:
                    baseline_status = baseline_info[name]
                    current_order = STATUS_ORDER.get(current_status, 0)
                    baseline_order = STATUS_ORDER.get(baseline_status, 0)
                    if current_order < baseline_order:
                        baseline_errors.append(
                            f"Regression: {name} went from '{baseline_status}' "
                            f"to '{current_status}'"
                        )

            # Check for removed globals
            removed_globals = set(baseline_info.keys()) - set(current_info.keys())
            if removed_globals:
                baseline_errors.append(
                    f"Globals removed without baseline update: {sorted(removed_globals)}"
                )

        except Exception as e:
            print(f"Warning: Could not load baseline: {e}", file=sys.stderr)
    else:
        if args.verbose:
            print(f"Note: No baseline found at {baseline_path}")

    # ─────────────────────────────────────────────────────────────────────
    # Report results
    # ─────────────────────────────────────────────────────────────────────
    print("Globals Registry Status")
    print("=" * 50)
    print()
    print(f"Registry: {registry_path}")
    print(f"Total globals tracked: {total_globals}")
    print()

    # Status breakdown
    print("Migration Status:")
    for status in ['migrated', 'in_progress', 'partial', 'pending', 'deferred']:
        count = actual_counts.get(status, 0)
        pct = (count / total_globals * 100) if total_globals > 0 else 0
        bar = '#' * int(pct / 5)
        print(f"  {status:12}: {count:3} ({pct:5.1f}%) {bar}")

    # Subsystem breakdown if verbose
    if args.verbose:
        print()
        print("By Subsystem:")
        for subsystem, count in sorted(subsystem_counts.items(), key=lambda x: -x[1]):
            print(f"  {subsystem:15}: {count}")

        print()
        print("By Priority:")
        for priority in ['critical', 'high', 'medium', 'low']:
            count = priority_counts.get(priority, 0)
            print(f"  {priority:10}: {count}")

    # Report errors
    all_errors = errors + baseline_errors
    if all_errors:
        print()
        if errors:
            print("ERROR: Statistics mismatch!")
            for error in errors:
                print(f"  - {error}")
            print()
            print("To fix: Update the statistics section in globals_registry.yaml")

        if baseline_errors:
            print("ERROR: Baseline violations!")
            for error in baseline_errors:
                print(f"  - {error}")
            print()
            print("To fix: Update .github/baseline_globals.yaml after review")

        return 1

    print()
    print("OK: Globals registry validation complete (no regressions)")
    return 0


if __name__ == '__main__':
    sys.exit(main())
