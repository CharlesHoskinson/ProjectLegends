#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-2.0-or-later
"""Generate docs/ci/vendored-sbom.cdx.json from real dependency identities.

Sources:
  1. cmake/dependencies.cmake pins consumed by FetchContent
  2. In-tree vendored FluidSynth version.h (authoritative for linked code)

FluidSynth purl uses Debian ecosystem coordinates so OSV can match
CVE/DEBIAN-CVE records for 1.1.6 (audit F017). Generic purls return empty.

Usage:
  python3 scripts/generate_vendored_sbom.py
  python3 scripts/generate_vendored_sbom.py --check
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

# Pins that have a FetchContent_Declare / MakeAvailable path in dependencies.cmake.
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
    # Optional feature pin (LEGENDS_ENABLE_MT32) but FetchContent path is real.
    "LEGENDS_DEP_MT32EMU_TAG": {
        "name": "mt32emu",
        "tag_to_version": lambda t: t.lstrip("v"),
        "purl_template": "pkg:github/munt/munt@{tag}",
    },
}

PIN_RE = re.compile(
    r'set\((LEGENDS_DEP_\w+_TAG)\s+"([^"]+)"',
    re.MULTILINE,
)
FLUID_VER_RE = re.compile(r'#define\s+FLUIDSYNTH_VERSION\s+"([^"]+)"')


def parse_pins(text: str) -> dict[str, str]:
    return {m.group(1): m.group(2) for m in PIN_RE.finditer(text)}


def fluidsynth_runtime_component() -> dict:
    """Inventory the *vendored* Fluidsynth, with OSV-matchable coordinates.

    version.h string is e.g. 1.1.6-noglib. OSV Debian data keys on 1.1.6.
    Use pkg:deb/debian/fluidsynth@1.1.6 so osv-scanner returns DEBIAN-CVE-*
    (which we baseline via osv-scanner.toml / #43). Do not use pkg:generic —
    that returns empty results (audit F017).
    """
    text = FLUID_VERSION_H.read_text(encoding="utf-8", errors="replace")
    m = FLUID_VER_RE.search(text)
    if not m:
        raise SystemExit(f"Cannot parse FLUIDSYNTH_VERSION from {FLUID_VERSION_H}")
    header_version = m.group(1)  # 1.1.6-noglib
    numeric = header_version.split("-")[0]
    purl = f"pkg:deb/debian/fluidsynth@{numeric}"
    return {
        "type": "library",
        "name": "fluidsynth",
        "version": numeric,
        "bom-ref": purl,
        "purl": purl,
        "description": (
            f"Vendored runtime engine/src/libs/fluidsynth; header version "
            f"'{header_version}' from engine/include/fluidsynth/version.h. "
            f"PURL uses Debian ecosystem @{numeric} so OSV can match CVE "
            f"records for the baseline (#43). Not LEGENDS_DEP_FLUIDSYNTH_TAG."
        ),
        "properties": [
            {
                "name": "legends:header-version",
                "value": header_version,
            },
            {
                "name": "legends:source-path",
                "value": "engine/src/libs/fluidsynth",
            },
        ],
    }


def build_sbom(pins: dict[str, str]) -> dict:
    components: list[dict] = []
    for pin_name, meta in ACTIVE_PIN_MAP.items():
        if pin_name not in pins:
            raise SystemExit(f"Missing expected pin {pin_name} in dependencies.cmake")
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

    # Fail closed: every LEGENDS_DEP_*_TAG must either be inventoried or
    # explicitly listed as dead/unused (not silently dropped).
    known_dead = {"LEGENDS_DEP_FLUIDSYNTH_TAG"}  # declared, never FetchContent'd
    for pin_name in pins:
        if pin_name in ACTIVE_PIN_MAP or pin_name in known_dead:
            continue
        raise SystemExit(
            f"Unmapped active pin {pin_name} — add to ACTIVE_PIN_MAP or known_dead"
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
                        "FetchContent pins + vendored FluidSynth via version.h. "
                        "FluidSynth uses deb purl for OSV match (F017). "
                        "LEGENDS_DEP_FLUIDSYNTH_TAG is dead/unused."
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
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()

    pins = parse_pins(CMAKE_DEPS.read_text(encoding="utf-8"))
    sbom = build_sbom(pins)

    fluid = next(c for c in sbom["components"] if c["name"] == "fluidsynth")
    if not fluid["purl"].startswith("pkg:deb/debian/fluidsynth@"):
        print("ERROR: fluidsynth purl must be Debian for OSV match", file=sys.stderr)
        return 1
    if "mt32emu" not in {c["name"] for c in sbom["components"]}:
        print("ERROR: mt32emu pin missing from SBOM", file=sys.stderr)
        return 1

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
        if len(existing.get("components", [])) < 5:
            print("ERROR: expected >= 5 components", file=sys.stderr)
            return 1
        print(f"OK {OUT} ({len(existing['components'])} components)")
        return 0

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(sbom, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {OUT} ({len(sbom['components'])} components)")
    for c in sbom["components"]:
        print(f"  - {c['name']}@{c['version']}  {c['purl']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
