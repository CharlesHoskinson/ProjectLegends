#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-2.0-or-later
"""Generate docs/ci/vendored-sbom.cdx.json from real dependency identities.

Sources:
  1. cmake/dependencies.cmake pins that are actually consumed by FetchContent
  2. In-tree vendored version headers (authoritative for compiled code)

Usage:
  python3 scripts/generate_vendored_sbom.py
  python3 scripts/generate_vendored_sbom.py --check

Tracks issue #42 / audit F015: never inventory a CMake pin that is not used
to select the binary that actually ships.
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
FLUID_VERSION_H = ROOT / "engine" / "include" / "fluidsynth" / "version.h"

# Pins that FetchContent / hermetic builds actually consume.
# LEGENDS_DEP_FLUIDSYNTH_TAG is declared but unused (vendored tree is built).
ACTIVE_PIN_MAP = {
    "LEGENDS_DEP_GSL_LITE_TAG": {
        "name": "gsl-lite",
        "tag_to_version": lambda t: t.lstrip("v"),
        "purl_template": "pkg:github/gsl-lite/gsl-lite@{tag}",
    },
    "LEGENDS_DEP_SDL3_TAG": {
        "name": "SDL",
        "tag_to_version": lambda t: t.replace("release-", ""),
        "purl_template": "pkg:github/libsdl-org/SDL@{tag}",
    },
    "LEGENDS_DEP_GOOGLETEST_TAG": {
        "name": "googletest",
        "tag_to_version": lambda t: t.lstrip("v"),
        "purl_template": "pkg:github/google/googletest@{tag}",
    },
    "LEGENDS_DEP_BENCHMARK_TAG": {
        "name": "benchmark",
        "tag_to_version": lambda t: t.lstrip("v"),
        "purl_template": "pkg:github/google/benchmark@{tag}",
    },
}

PIN_RE = re.compile(
    r'set\((LEGENDS_DEP_\w+_TAG)\s+"([^"]+)"',
    re.MULTILINE,
)
FLUID_VER_RE = re.compile(
    r'#define\s+FLUIDSYNTH_VERSION\s+"([^"]+)"'
)


def parse_pins(text: str) -> dict[str, str]:
    return {m.group(1): m.group(2) for m in PIN_RE.finditer(text)}


def fluidsynth_runtime_component() -> dict:
    text = FLUID_VERSION_H.read_text(encoding="utf-8", errors="replace")
    m = FLUID_VER_RE.search(text)
    if not m:
        raise SystemExit(f"Cannot parse FLUIDSYNTH_VERSION from {FLUID_VERSION_H}")
    version = m.group(1)  # e.g. 1.1.6-noglib
    # OSV / purl: use numeric triple for ecosystem matching when possible.
    numeric = version.split("-")[0]
    purl = f"pkg:generic/fluidsynth@{numeric}"
    return {
        "type": "library",
        "name": "fluidsynth",
        "version": version,
        "bom-ref": f"pkg:generic/fluidsynth@{version}",
        "purl": purl,
        "description": (
            "Vendored runtime at engine/src/libs/fluidsynth; version from "
            f"engine/include/fluidsynth/version.h ({version}). "
            "NOT the unused LEGENDS_DEP_FLUIDSYNTH_TAG CMake pin. Tracked #43."
        ),
    }


def build_sbom(pins: dict[str, str]) -> dict:
    components: list[dict] = []
    for pin_name, meta in ACTIVE_PIN_MAP.items():
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
                "description": f"Active FetchContent pin {pin_name}={tag}",
            }
        )

    components.append(fluidsynth_runtime_component())

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
                        "Active CMake pins + in-tree FluidSynth version.h "
                        "(audit F015). Unused LEGENDS_DEP_FLUIDSYNTH_TAG is not inventoried."
                    ),
                },
            ],
        },
        "components": components,
    }


def keyset(doc: dict) -> list:
    return sorted(
        (c.get("name"), c.get("version"), c.get("purl"))
        for c in doc.get("components", [])
    )


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--check",
        action="store_true",
        help="Exit 1 if on-disk SBOM differs from generator",
    )
    args = ap.parse_args()

    pins = parse_pins(CMAKE_DEPS.read_text(encoding="utf-8"))
    sbom = build_sbom(pins)

    # Hard honesty: FluidSynth must match version.h, never 2.3.x phantom pin.
    fluid = next(c for c in sbom["components"] if c["name"] == "fluidsynth")
    if fluid["version"].startswith("2."):
        print("ERROR: fluidsynth version looks like a FetchContent pin, not vendored", file=sys.stderr)
        return 1
    if "1.1.6" not in fluid["version"]:
        # Still allow future upgrades of the vendored tree.
        pass

    if args.check:
        if not OUT.exists():
            print(f"MISSING {OUT}", file=sys.stderr)
            return 1
        existing = json.loads(OUT.read_text(encoding="utf-8"))
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
    for c in sbom["components"]:
        print(f"  - {c['name']}@{c['version']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
