#!/usr/bin/env python3
"""
Validate globals_registry.yaml statistics and report status.

This script verifies that the statistics section matches the actual
counts in the registry and provides a summary of migration progress.

Exit codes:
  0 - Registry valid
  1 - Statistics mismatch or error
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


def load_registry(path: Path) -> dict:
    """Load a YAML registry file."""
    with open(path, 'r', encoding='utf-8') as f:
        return yaml.safe_load(f) or {}


def main() -> int:
    parser = argparse.ArgumentParser(
        description='Validate globals registry statistics'
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
        '-v', '--verbose',
        action='store_true',
        help='Show detailed breakdown'
    )
    args = parser.parse_args()

    # Find registry
    registry_path = args.registry or find_registry(args.path)

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

    # Verify statistics if present
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

    # Report results
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
    if errors:
        print()
        print("ERROR: Statistics mismatch!")
        print()
        for error in errors:
            print(f"  - {error}")
        print()
        print("To fix: Update the statistics section in globals_registry.yaml")
        return 1

    print()
    print("OK: Globals registry validation complete")
    return 0


if __name__ == '__main__':
    sys.exit(main())
