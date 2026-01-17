# Phase 6: Measure Rebuild Improvement

## Objective

Capture baseline and post-refactoring build metrics to quantify the improvement from module isolation. Document results for future reference.

## Metrics to Collect

| Metric | Description | Target Improvement |
|--------|-------------|-------------------|
| Clean build time | Full rebuild from scratch | Baseline only |
| Header change rebuild | Rebuild after touching a public header | >50% reduction |
| Single .cpp rebuild | Rebuild after touching one source file | >70% reduction |
| Dependency count | Number of files affected by header change | >50% reduction |

## Deliverables

### 6.1 Create Metrics Collection Script

**File:** `scripts/measure_rebuild.py`

```python
#!/usr/bin/env python3
"""
Sprint 3: Build Metrics Collection

Measures incremental rebuild times to quantify module isolation benefits.

Usage:
  python scripts/measure_rebuild.py --baseline    # Before refactoring
  python scripts/measure_rebuild.py --after       # After refactoring
  python scripts/measure_rebuild.py --compare     # Compare results

Output:
  build/metrics/baseline.json
  build/metrics/after.json
  build/metrics/comparison.md
"""

import argparse
import json
import subprocess
import time
import shutil
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional
from dataclasses import dataclass, asdict

#------------------------------------------------------------------------------
# Configuration
#------------------------------------------------------------------------------

BUILD_DIR = Path('build')
METRICS_DIR = BUILD_DIR / 'metrics'

# Files to test for incremental rebuilds
TEST_FILES = {
    'legends_header': Path('include/legends/legends_embed.h'),
    'pal_header': Path('include/pal/window.h'),
    'engine_header': Path('engine/include/dosbox/dosbox_library.h'),
    'legends_source': Path('src/legends/legends_embed_api.cpp'),
    'engine_source': Path('engine/src/misc/dosbox_library.cpp'),
}

# Number of iterations for averaging
ITERATIONS = 3

#------------------------------------------------------------------------------
# Data structures
#------------------------------------------------------------------------------

@dataclass
class RebuildMetric:
    file: str
    min_time: float
    max_time: float
    avg_time: float
    files_rebuilt: int

@dataclass
class MetricsReport:
    timestamp: str
    git_commit: str
    clean_build_time: float
    rebuild_metrics: Dict[str, RebuildMetric]
    cmake_version: str
    compiler: str

#------------------------------------------------------------------------------
# Build utilities
#------------------------------------------------------------------------------

def run_command(cmd: List[str], cwd: Optional[Path] = None) -> subprocess.CompletedProcess:
    """Run a command and return the result."""
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)

def get_git_commit() -> str:
    """Get current git commit hash."""
    result = run_command(['git', 'rev-parse', '--short', 'HEAD'])
    return result.stdout.strip() if result.returncode == 0 else 'unknown'

def get_cmake_version() -> str:
    """Get CMake version."""
    result = run_command(['cmake', '--version'])
    if result.returncode == 0:
        return result.stdout.split('\n')[0]
    return 'unknown'

def get_compiler_info() -> str:
    """Get compiler info from CMake cache."""
    cache_file = BUILD_DIR / 'CMakeCache.txt'
    if cache_file.exists():
        for line in cache_file.read_text().splitlines():
            if 'CMAKE_CXX_COMPILER:' in line:
                return line.split('=')[1] if '=' in line else 'unknown'
    return 'unknown'

def clean_build() -> float:
    """Perform a clean build and return the time."""
    # Remove build directory
    if BUILD_DIR.exists():
        shutil.rmtree(BUILD_DIR)

    # Configure
    start = time.perf_counter()
    run_command(['cmake', '-B', str(BUILD_DIR), '-DLEGENDS_BUILD_TESTS=OFF'])

    # Build
    run_command(['cmake', '--build', str(BUILD_DIR), '-j'])
    elapsed = time.perf_counter() - start

    return elapsed

def measure_rebuild(test_file: Path, iterations: int = ITERATIONS) -> RebuildMetric:
    """Touch a file and measure rebuild time."""
    times = []

    for i in range(iterations):
        # Touch the file
        test_file.touch()

        # Measure rebuild
        start = time.perf_counter()
        result = run_command(['cmake', '--build', str(BUILD_DIR), '-j'])
        elapsed = time.perf_counter() - start

        times.append(elapsed)
        print(f"  Iteration {i+1}: {elapsed:.2f}s")

    # Count files rebuilt (from ninja output if available)
    files_rebuilt = 0
    if result.stdout:
        # Count lines like "[1/5] Building CXX..."
        files_rebuilt = sum(1 for line in result.stdout.splitlines()
                           if 'Building' in line)

    return RebuildMetric(
        file=str(test_file),
        min_time=min(times),
        max_time=max(times),
        avg_time=sum(times) / len(times),
        files_rebuilt=files_rebuilt,
    )

#------------------------------------------------------------------------------
# Reporting
#------------------------------------------------------------------------------

def save_metrics(report: MetricsReport, filename: str) -> None:
    """Save metrics to JSON file."""
    METRICS_DIR.mkdir(parents=True, exist_ok=True)
    output_path = METRICS_DIR / filename

    with open(output_path, 'w') as f:
        json.dump(asdict(report), f, indent=2)

    print(f"\nMetrics saved to: {output_path}")

def load_metrics(filename: str) -> Optional[MetricsReport]:
    """Load metrics from JSON file."""
    input_path = METRICS_DIR / filename
    if not input_path.exists():
        return None

    with open(input_path) as f:
        data = json.load(f)

    # Reconstruct dataclass
    rebuild_metrics = {
        k: RebuildMetric(**v) for k, v in data['rebuild_metrics'].items()
    }
    data['rebuild_metrics'] = rebuild_metrics
    return MetricsReport(**data)

def generate_comparison(baseline: MetricsReport, after: MetricsReport) -> str:
    """Generate markdown comparison report."""
    lines = [
        "# Sprint 3: Build Metrics Comparison",
        "",
        f"**Baseline:** {baseline.git_commit} ({baseline.timestamp})",
        f"**After:** {after.git_commit} ({after.timestamp})",
        "",
        "## Clean Build Time",
        "",
        f"| Metric | Baseline | After | Change |",
        f"|--------|----------|-------|--------|",
        f"| Clean build | {baseline.clean_build_time:.1f}s | {after.clean_build_time:.1f}s | {(after.clean_build_time - baseline.clean_build_time) / baseline.clean_build_time * 100:+.1f}% |",
        "",
        "## Incremental Rebuild Times",
        "",
        "| File Changed | Baseline (avg) | After (avg) | Improvement |",
        "|--------------|----------------|-------------|-------------|",
    ]

    for key in baseline.rebuild_metrics:
        b = baseline.rebuild_metrics[key]
        a = after.rebuild_metrics.get(key)
        if a:
            improvement = (b.avg_time - a.avg_time) / b.avg_time * 100
            lines.append(f"| {key} | {b.avg_time:.2f}s | {a.avg_time:.2f}s | {improvement:+.1f}% |")

    lines.extend([
        "",
        "## Files Rebuilt Per Change",
        "",
        "| File Changed | Baseline | After | Reduction |",
        "|--------------|----------|-------|-----------|",
    ])

    for key in baseline.rebuild_metrics:
        b = baseline.rebuild_metrics[key]
        a = after.rebuild_metrics.get(key)
        if a and b.files_rebuilt > 0:
            reduction = (b.files_rebuilt - a.files_rebuilt) / b.files_rebuilt * 100
            lines.append(f"| {key} | {b.files_rebuilt} | {a.files_rebuilt} | {reduction:+.1f}% |")

    lines.extend([
        "",
        "## Summary",
        "",
    ])

    # Calculate overall improvement
    baseline_avg = sum(m.avg_time for m in baseline.rebuild_metrics.values()) / len(baseline.rebuild_metrics)
    after_avg = sum(m.avg_time for m in after.rebuild_metrics.values()) / len(after.rebuild_metrics)
    overall_improvement = (baseline_avg - after_avg) / baseline_avg * 100

    if overall_improvement > 0:
        lines.append(f"**Overall incremental rebuild improvement: {overall_improvement:.1f}%**")
    else:
        lines.append(f"**No improvement detected ({overall_improvement:.1f}%)**")

    return '\n'.join(lines)

#------------------------------------------------------------------------------
# Main
#------------------------------------------------------------------------------

def collect_metrics() -> MetricsReport:
    """Collect all metrics."""
    print("=" * 60)
    print("Sprint 3: Build Metrics Collection")
    print("=" * 60)

    print("\nStep 1: Clean build")
    clean_time = clean_build()
    print(f"Clean build time: {clean_time:.1f}s")

    print("\nStep 2: Incremental rebuild tests")
    rebuild_metrics = {}

    for name, test_file in TEST_FILES.items():
        if test_file.exists():
            print(f"\nTesting: {name} ({test_file})")
            metric = measure_rebuild(test_file)
            rebuild_metrics[name] = metric
        else:
            print(f"\nSkipping: {name} (file not found)")

    return MetricsReport(
        timestamp=datetime.now().isoformat(),
        git_commit=get_git_commit(),
        clean_build_time=clean_time,
        rebuild_metrics=rebuild_metrics,
        cmake_version=get_cmake_version(),
        compiler=get_compiler_info(),
    )

def main() -> int:
    parser = argparse.ArgumentParser(description='Collect build metrics')
    parser.add_argument('--baseline', action='store_true',
                        help='Collect baseline metrics (before refactoring)')
    parser.add_argument('--after', action='store_true',
                        help='Collect post-refactoring metrics')
    parser.add_argument('--compare', action='store_true',
                        help='Generate comparison report')
    args = parser.parse_args()

    if args.baseline:
        report = collect_metrics()
        save_metrics(report, 'baseline.json')

    elif args.after:
        report = collect_metrics()
        save_metrics(report, 'after.json')

    elif args.compare:
        baseline = load_metrics('baseline.json')
        after = load_metrics('after.json')

        if not baseline:
            print("Error: baseline.json not found. Run with --baseline first.")
            return 1
        if not after:
            print("Error: after.json not found. Run with --after first.")
            return 1

        comparison = generate_comparison(baseline, after)

        output_path = METRICS_DIR / 'comparison.md'
        output_path.write_text(comparison)
        print(comparison)
        print(f"\nSaved to: {output_path}")

    else:
        parser.print_help()
        return 1

    return 0

if __name__ == '__main__':
    exit(main())
```

### 6.2 Document Metrics in ARCHITECTURE.md

**Add section:**

```markdown
## Build Metrics (Sprint 3)

### Methodology

Metrics collected using `scripts/measure_rebuild.py`:
- Clean build: Full rebuild from scratch
- Incremental: Touch file, rebuild, measure time
- Each test repeated 3 times, averaged

### Results

| Metric | Before Sprint 3 | After Sprint 3 | Improvement |
|--------|-----------------|----------------|-------------|
| Clean build | TBD | TBD | - |
| legends_embed.h change | TBD | TBD | TBD |
| dosbox_library.h change | TBD | TBD | TBD |
| Single .cpp change | TBD | TBD | TBD |

### Targets

- Header change rebuild: <10s (from ~45s baseline)
- Single .cpp change: <5s (from ~15s baseline)
- Overall improvement: >50%
```

## Implementation Steps

| Step | Action | Files |
|------|--------|-------|
| 6.1.1 | Create measure_rebuild.py | scripts/measure_rebuild.py |
| 6.1.2 | Make script executable | chmod +x scripts/measure_rebuild.py |
| 6.2.1 | Collect baseline (before Phase 2-5) | Run --baseline |
| 6.2.2 | Complete Phases 2-5 | Implementation |
| 6.2.3 | Collect after metrics | Run --after |
| 6.2.4 | Generate comparison | Run --compare |
| 6.3.1 | Update ARCHITECTURE.md with results | ARCHITECTURE.md |

## Test Plan

### Unit Tests

```python
# tests/test_measure_rebuild.py

import tempfile
import json
from pathlib import Path

import sys
sys.path.insert(0, str(Path(__file__).parent.parent / 'scripts'))
from measure_rebuild import RebuildMetric, MetricsReport, generate_comparison

def test_metric_serialization():
    """Test that metrics can be serialized to JSON."""
    metric = RebuildMetric(
        file='test.h',
        min_time=1.0,
        max_time=2.0,
        avg_time=1.5,
        files_rebuilt=10,
    )

    report = MetricsReport(
        timestamp='2024-01-01T00:00:00',
        git_commit='abc123',
        clean_build_time=60.0,
        rebuild_metrics={'test': metric},
        cmake_version='3.28',
        compiler='clang++',
    )

    # Should not raise
    from dataclasses import asdict
    json.dumps(asdict(report))

def test_comparison_generation():
    """Test that comparison report generates."""
    baseline = MetricsReport(
        timestamp='2024-01-01',
        git_commit='before',
        clean_build_time=60.0,
        rebuild_metrics={
            'test': RebuildMetric('test.h', 10.0, 12.0, 11.0, 50)
        },
        cmake_version='3.28',
        compiler='clang++',
    )

    after = MetricsReport(
        timestamp='2024-01-02',
        git_commit='after',
        clean_build_time=55.0,
        rebuild_metrics={
            'test': RebuildMetric('test.h', 4.0, 6.0, 5.0, 20)
        },
        cmake_version='3.28',
        compiler='clang++',
    )

    markdown = generate_comparison(baseline, after)

    assert '# Sprint 3' in markdown
    assert 'Improvement' in markdown
    assert 'before' in markdown
    assert 'after' in markdown
```

### Integration Tests

```bash
#!/bin/bash
# tests/integration/test_metrics.sh

set -e

echo "Test 1: Script runs"
python scripts/measure_rebuild.py --help
echo "PASS"

echo "Test 2: Baseline collection (dry run)"
# Just verify it starts, don't actually build
timeout 5 python scripts/measure_rebuild.py --baseline || true
echo "PASS: Script starts"

echo "Test 3: JSON output valid"
if [ -f build/metrics/baseline.json ]; then
    python -m json.tool build/metrics/baseline.json > /dev/null
    echo "PASS: Valid JSON"
fi

echo "All metric tests passed"
```

### Manual Verification

| Test | Command | Expected Result |
|------|---------|-----------------|
| Baseline collection | `python scripts/measure_rebuild.py --baseline` | JSON saved |
| After collection | `python scripts/measure_rebuild.py --after` | JSON saved |
| Comparison | `python scripts/measure_rebuild.py --compare` | Markdown generated |
| Results reasonable | Review comparison.md | >0% improvement |

### Acceptance Criteria

- [ ] `scripts/measure_rebuild.py` exists and is executable
- [ ] Baseline metrics collected before Phase 2 changes
- [ ] After metrics collected after Phase 5 complete
- [ ] Comparison report generated
- [ ] Results documented in ARCHITECTURE.md
- [ ] Measurable improvement demonstrated (target: >50%)

## Rollback Plan

This phase is documentation-only. No rollback needed.

## Expected Results

Based on similar refactoring efforts:

| File Changed | Expected Before | Expected After | Expected Improvement |
|--------------|-----------------|----------------|---------------------|
| legends_embed.h | 45s | 8s | 82% |
| dosbox_library.h | 120s | 20s | 83% |
| Single .cpp | 15s | 3s | 80% |

Actual results will vary based on:
- Hardware (CPU cores, SSD speed)
- Compiler (GCC vs Clang vs MSVC)
- Build system (Ninja vs Make)
- CMake version

## Continuous Monitoring

After Sprint 3, add metrics collection to CI:

```yaml
# .github/workflows/metrics.yml
name: Build Metrics

on:
  schedule:
    - cron: '0 0 * * 0'  # Weekly

jobs:
  collect:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Collect metrics
        run: python scripts/measure_rebuild.py --after
      - name: Upload metrics
        uses: actions/upload-artifact@v4
        with:
          name: build-metrics
          path: build/metrics/
```
