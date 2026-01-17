#!/usr/bin/env python3
"""
measure_rebuild.py - Measure incremental rebuild times

This script measures the impact of header changes on build times,
useful for tracking improvements from module boundary refactoring.

Metrics captured:
- Clean build time
- Incremental rebuild after touching header in each module
- Incremental rebuild after touching .cpp in each module

Usage:
    python scripts/measure_rebuild.py --build-dir build
    python scripts/measure_rebuild.py --build-dir build --output metrics.json
    python scripts/measure_rebuild.py --build-dir build --iterations 3

Requirements:
    - Build directory must already be configured
    - CMake and build system (ninja/make) must be available
"""

import argparse
import json
import os
import subprocess
import sys
import time
from dataclasses import dataclass, asdict
from datetime import datetime
from pathlib import Path
from typing import List, Optional, Dict, Any
import tempfile
import shutil


@dataclass
class BuildMetric:
    """Single build timing measurement."""
    name: str
    description: str
    file_touched: Optional[str]
    duration_seconds: float
    files_rebuilt: int
    success: bool
    error_message: Optional[str] = None


@dataclass
class RebuildReport:
    """Complete rebuild metrics report."""
    timestamp: str
    project_root: str
    build_dir: str
    build_type: str
    iterations: int
    metrics: List[BuildMetric]

    def to_dict(self) -> Dict[str, Any]:
        return {
            "timestamp": self.timestamp,
            "project_root": self.project_root,
            "build_dir": self.build_dir,
            "build_type": self.build_type,
            "iterations": self.iterations,
            "metrics": [asdict(m) for m in self.metrics]
        }


def touch_file(path: Path):
    """Touch a file to trigger rebuild."""
    if not path.exists():
        raise FileNotFoundError(f"Cannot touch: {path}")
    path.touch()


def count_rebuilt_files(output: str) -> int:
    """Count files rebuilt from build output."""
    # Ninja format: [N/M] Building CXX object...
    # Make format: [  N%] Building CXX object...
    count = 0
    for line in output.split('\n'):
        if 'Building' in line or 'Compiling' in line:
            count += 1
    return count


def run_build(build_dir: Path, verbose: bool = False) -> tuple[float, int, bool, str]:
    """
    Run incremental build and measure time.

    Returns:
        (duration_seconds, files_rebuilt, success, error_message)
    """
    start = time.perf_counter()

    try:
        result = subprocess.run(
            ["cmake", "--build", str(build_dir), "--parallel"],
            capture_output=True,
            text=True,
            cwd=build_dir
        )
        end = time.perf_counter()

        duration = end - start
        output = result.stdout + result.stderr
        files_rebuilt = count_rebuilt_files(output)
        success = result.returncode == 0
        error = None if success else result.stderr[:500]

        if verbose:
            print(f"  Duration: {duration:.2f}s, Files: {files_rebuilt}, Success: {success}")

        return duration, files_rebuilt, success, error

    except Exception as e:
        end = time.perf_counter()
        return end - start, 0, False, str(e)


def measure_clean_build(build_dir: Path, verbose: bool) -> BuildMetric:
    """Measure clean build time."""
    print("Measuring clean build...")

    # Clean
    subprocess.run(
        ["cmake", "--build", str(build_dir), "--target", "clean"],
        capture_output=True
    )

    duration, files, success, error = run_build(build_dir, verbose)

    return BuildMetric(
        name="clean_build",
        description="Full clean build",
        file_touched=None,
        duration_seconds=duration,
        files_rebuilt=files,
        success=success,
        error_message=error
    )


def measure_header_touch(
    build_dir: Path,
    project_root: Path,
    header_path: str,
    metric_name: str,
    description: str,
    verbose: bool
) -> BuildMetric:
    """Measure rebuild after touching a header file."""
    full_path = project_root / header_path

    if not full_path.exists():
        return BuildMetric(
            name=metric_name,
            description=description,
            file_touched=header_path,
            duration_seconds=0,
            files_rebuilt=0,
            success=False,
            error_message=f"File not found: {header_path}"
        )

    print(f"Measuring: {description}...")

    # Ensure we have a complete build first
    subprocess.run(
        ["cmake", "--build", str(build_dir), "--parallel"],
        capture_output=True
    )

    # Touch the header
    touch_file(full_path)

    # Measure rebuild
    duration, files, success, error = run_build(build_dir, verbose)

    return BuildMetric(
        name=metric_name,
        description=description,
        file_touched=header_path,
        duration_seconds=duration,
        files_rebuilt=files,
        success=success,
        error_message=error
    )


def measure_cpp_touch(
    build_dir: Path,
    project_root: Path,
    cpp_path: str,
    metric_name: str,
    description: str,
    verbose: bool
) -> BuildMetric:
    """Measure rebuild after touching a .cpp file."""
    full_path = project_root / cpp_path

    if not full_path.exists():
        return BuildMetric(
            name=metric_name,
            description=description,
            file_touched=cpp_path,
            duration_seconds=0,
            files_rebuilt=0,
            success=False,
            error_message=f"File not found: {cpp_path}"
        )

    print(f"Measuring: {description}...")

    # Ensure we have a complete build first
    subprocess.run(
        ["cmake", "--build", str(build_dir), "--parallel"],
        capture_output=True
    )

    # Touch the cpp
    touch_file(full_path)

    # Measure rebuild
    duration, files, success, error = run_build(build_dir, verbose)

    return BuildMetric(
        name=metric_name,
        description=description,
        file_touched=cpp_path,
        duration_seconds=duration,
        files_rebuilt=files,
        success=success,
        error_message=error
    )


def get_build_type(build_dir: Path) -> str:
    """Get build type from CMakeCache."""
    cache_file = build_dir / "CMakeCache.txt"
    if cache_file.exists():
        with open(cache_file) as f:
            for line in f:
                if line.startswith("CMAKE_BUILD_TYPE:"):
                    return line.split("=")[1].strip()
    return "Unknown"


def run_metrics(
    project_root: Path,
    build_dir: Path,
    iterations: int,
    verbose: bool
) -> RebuildReport:
    """Run all metrics measurements."""

    metrics = []

    # Test files to measure
    test_files = [
        # Headers - legends module
        ("include/legends/legends_embed.h", "legends_embed_h",
         "Touch legends_embed.h (public API)"),

        # Headers - engine module
        ("engine/include/dosbox/dosbox_library.h", "dosbox_library_h",
         "Touch dosbox_library.h (engine public API)"),

        # Headers - refactored public headers
        ("engine/include/dosbox/builtin_types.h", "builtin_types_h",
         "Touch builtin_types.h (new public header)"),
        ("engine/include/dosbox/cdrom_interface.h", "cdrom_interface_h",
         "Touch cdrom_interface.h (new public header)"),
        ("engine/include/dosbox/render_types.h", "render_types_h",
         "Touch render_types.h (new public header)"),

        # Headers - previously problematic
        ("engine/include/builtin.h", "builtin_h",
         "Touch builtin.h (refactored)"),
        ("engine/include/bios_disk.h", "bios_disk_h",
         "Touch bios_disk.h (refactored)"),
        ("engine/include/render.h", "render_h",
         "Touch render.h (refactored)"),

        # CPP files - legends module
        ("src/legends/legends_embed_api.cpp", "legends_embed_api_cpp",
         "Touch legends_embed_api.cpp"),
    ]

    for _ in range(iterations):
        # Measure clean build once per iteration
        metrics.append(measure_clean_build(build_dir, verbose))

        # Measure header touches
        for file_path, name, desc in test_files:
            if file_path.endswith('.h'):
                metrics.append(measure_header_touch(
                    build_dir, project_root, file_path, name, desc, verbose
                ))
            else:
                metrics.append(measure_cpp_touch(
                    build_dir, project_root, file_path, name, desc, verbose
                ))

    return RebuildReport(
        timestamp=datetime.now().isoformat(),
        project_root=str(project_root),
        build_dir=str(build_dir),
        build_type=get_build_type(build_dir),
        iterations=iterations,
        metrics=metrics
    )


def print_summary(report: RebuildReport):
    """Print a summary of the metrics."""
    print()
    print("=" * 70)
    print("Rebuild Metrics Summary")
    print("=" * 70)
    print(f"Project: {report.project_root}")
    print(f"Build:   {report.build_dir}")
    print(f"Type:    {report.build_type}")
    print(f"Time:    {report.timestamp}")
    print()

    # Group by metric name
    by_name: Dict[str, List[BuildMetric]] = {}
    for m in report.metrics:
        if m.name not in by_name:
            by_name[m.name] = []
        by_name[m.name].append(m)

    print(f"{'Metric':<30} {'Avg Time':<12} {'Files':<8} {'Status'}")
    print("-" * 70)

    for name, measurements in by_name.items():
        successful = [m for m in measurements if m.success]
        if successful:
            avg_time = sum(m.duration_seconds for m in successful) / len(successful)
            avg_files = sum(m.files_rebuilt for m in successful) // len(successful)
            status = "OK"
        else:
            avg_time = 0
            avg_files = 0
            status = "FAILED"

        desc = measurements[0].description[:28]
        print(f"{desc:<30} {avg_time:>8.2f}s    {avg_files:<8} {status}")

    print("=" * 70)


def main():
    parser = argparse.ArgumentParser(
        description="Measure incremental rebuild times"
    )
    parser.add_argument(
        "--build-dir", "-b",
        type=Path,
        default=Path("build"),
        help="Build directory (default: build)"
    )
    parser.add_argument(
        "--project-root", "-p",
        type=Path,
        default=None,
        help="Project root (default: parent of build dir or current dir)"
    )
    parser.add_argument(
        "--output", "-o",
        type=Path,
        default=None,
        help="Output JSON file (default: print to stdout)"
    )
    parser.add_argument(
        "--iterations", "-n",
        type=int,
        default=1,
        help="Number of iterations per metric (default: 1)"
    )
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Verbose output"
    )

    args = parser.parse_args()

    build_dir = args.build_dir.resolve()
    if not build_dir.exists():
        print(f"Error: Build directory does not exist: {build_dir}", file=sys.stderr)
        return 2

    if args.project_root:
        project_root = args.project_root.resolve()
    else:
        # Try to find project root from build dir
        if (build_dir.parent / "CMakeLists.txt").exists():
            project_root = build_dir.parent
        else:
            project_root = Path.cwd()

    if not (project_root / "CMakeLists.txt").exists():
        print(f"Error: Cannot find CMakeLists.txt in project root: {project_root}",
              file=sys.stderr)
        return 2

    print(f"Project root: {project_root}")
    print(f"Build dir:    {build_dir}")
    print(f"Iterations:   {args.iterations}")
    print()

    report = run_metrics(project_root, build_dir, args.iterations, args.verbose)

    # Output
    if args.output:
        with open(args.output, 'w') as f:
            json.dump(report.to_dict(), f, indent=2)
        print(f"\nMetrics saved to: {args.output}")
    else:
        print_summary(report)

    return 0


if __name__ == "__main__":
    sys.exit(main())
