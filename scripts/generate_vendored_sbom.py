#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-2.0-or-later
"""Generate docs/ci/vendored-sbom.cdx.json from cmake/dependencies.cmake pins.

Usage:
  python3 scripts/generate_vendored_sbom.py
  python3 scripts/generate_vendored_sbom.py --check   # exit 1 if SBOM stale

Tracks issue #42: reproducible inventory until full CMake SBOM lands.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CMAKE_DEPS = ROOT / "cmake" / "dependencies.cmake"
OUT = ROOT / "docs" / "ci" / "vendored-sbom.cdx.json"

# Map CMake cache pin names → CycloneDX component descriptors.
# Keep in sync with DEPENDENCIES.md / cmake/dependencies.cmake.
PIN_MAP = {
    "LEGENDS_DEP_GSL_LITE_TAG": {
        "name": "gsl-lite",
        "github": "gsl-lite/gsl-lite",
        "tag_to_version": lambda t: t.lstrip("v"),
        "purl_template": "pkg:github/gsl-lite/gsl-lite@{tag}",
    },
    "LEGENDS_DEP_SDL3_TAG": {
        "name": "SDL",
        "github": "libsdl-org/SDL",
        "tag_to_version": lambda t: t.replace("release-", ""),
        "purl_template": "pkg:github/libsdl-org/SDL@{tag}",
    },
    "LEGENDS_DEP_GOOGLETEST_TAG": {
        "name": "googletest",
        "github": "google/googletest",
        "tag_to_version": lambda t: t.lstrip("v"),
        "purl_template": "pkg:github/google/googletest@{tag}",
    },
    "LEGENDS_DEP_BENCHMARK_TAG": {
        "name": "benchmark",
        "github": "google/benchmark",
        "tag_to_version": lambda t: t.lstrip("v"),
        "purl_template": "pkg:github/google/benchmark@{tag}",
    },
    "LEGENDS_DEP_FLUIDSYNTH_TAG": {
        "name": "fluidsynth",
        "github": "FluidSynth/fluidsynth",
        "tag_to_version": lambda t: t.lstrip("v"),
        "purl_template": "pkg:github/FluidSynth/fluidsynth@{tag}",
    },
    "LEGENDS_DEP_MT32EMU_TAG": {
        "name": "munt",
        "github": "munt/munt",
        "tag_to_version": lambda t: t.lstrip("v"),
        "purl_template": "pkg:github/munt/munt@{tag}",
    },
}

PIN_RE = re.compile(
    r'set\((LEGENDS_DEP_\w+_TAG)\s+"([^"]+)"',
    re.MULTILINE,
)


def parse_pins(text: str) -> dict[str, str]:
    return {m.group(1): m.group(2) for m in PIN_RE.finditer(text)}


def build_sbom(pins: dict[str, str]) -> dict:
    components = []
    for pin_name, meta in PIN_MAP.items():
        if pin_name not in pins:
            continue
        tag = pins[pin_name]
        version = meta["tag_to_version"](tag)
        purl = meta["purl_template"].format(tag=tag)
        components.append(
            {
                "type": "library",
                "name": meta["name"],
                "version": version,
                "bom-ref": purl,
                "purl": purl,
                "description": f"Pin {pin_name}={tag} from cmake/dependencies.cmake",
            }
        )

    return {
        "bomFormat": "CycloneDX",
        "specVersion": "1.5",
        "version": 1,
        "metadata": {
            "timestamp": datetime.now(timezone.utc)
            .replace(microsecond=0)
            .isoformat()
            .replace("+00:00", "Z"),
            "component": {
                "type": "application",
                "name": "ProjectLegends",
                "version": "0.0.0-dev",
            },
            "properties": [
                {
                    "name": "legends:sbom-generator",
                    "value": "scripts/generate_vendored_sbom.py",
                },
                {
                    "name": "legends:sbom-note",
                    "value": (
                        "Generated from cmake/dependencies.cmake pins (#42). "
                        "Vendored tree snapshots may lag FetchContent pins."
                    ),
                },
            ],
        },
        "components": components,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--check",
        action="store_true",
        help="Exit 1 if on-disk SBOM components/pins differ from generator",
    )
    args = ap.parse_args()

    pins = parse_pins(CMAKE_DEPS.read_text(encoding="utf-8"))
    sbom = build_sbom(pins)

    if args.check:
        if not OUT.exists():
            print(f"MISSING {OUT}", file=sys.stderr)
            return 1
        existing = json.loads(OUT.read_text(encoding="utf-8"))
        # Compare component name/version/purl only (ignore timestamp noise).
        def keyset(doc: dict) -> list:
            return sorted(
                (
                    c.get("name"),
                    c.get("version"),
                    c.get("purl"),
                )
                for c in doc.get("components", [])
            )

        if keyset(existing) != keyset(sbom):
            print("STALE vendored-sbom.cdx.json — run scripts/generate_vendored_sbom.py", file=sys.stderr)
            print("expected:", keyset(sbom), file=sys.stderr)
            print("actual:  ", keyset(existing), file=sys.stderr)
            return 1
        if len(existing.get("components", [])) < 4:
            print("ERROR: SBOM has fewer than 4 components", file=sys.stderr)
            return 1
        print(f"OK {OUT} ({len(existing['components'])} components)")
        return 0

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(sbom, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {OUT} ({len(sbom['components'])} components)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
