#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-2.0-or-later
"""Generate docs/ci/vendored-sbom.cdx.json for OSV scanning.

Inventory rules (#42 / F017):
  1. Every LEGENDS_DEP_*_TAG that is used by FetchContent, or is an optional
     feature pin with a real FetchContent path.
  2. In-tree libraries under engine/src/libs that are **linked** by default CI
     targets (headless legends/aibox), with explicit version sources.
  3. Never inventory deleted/unlinked FluidSynth 1.1.6.

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
ZMBV_H = ROOT / "engine" / "src" / "libs" / "zmbv" / "zmbv.h"
PHYSFS_H = ROOT / "engine" / "src" / "libs" / "physfs" / "physfs.h"
TINYFD_H = ROOT / "engine" / "src" / "libs" / "tinyfiledialogs" / "tinyfiledialogs.h"
XBRZ_CHANGELOG = ROOT / "engine" / "src" / "libs" / "xBRZ" / "Changelog.txt"

# Pins with FetchContent paths in dependencies.cmake (optional features included).
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
    "LEGENDS_DEP_MT32EMU_TAG": {
        "name": "mt32emu",
        "tag_to_version": lambda t: t.lstrip("v"),
        "purl_template": "pkg:github/munt/munt@{tag}",
    },
    # Only when LEGENDS_ENABLE_FLUIDSYNTH=ON; still inventoriable as the
    # only supported Fluidsynth identity after vendored-tree removal.
    "LEGENDS_DEP_FLUIDSYNTH_TAG": {
        "name": "fluidsynth",
        "tag_to_version": lambda t: t.lstrip("v"),
        "purl_template": "pkg:github/FluidSynth/fluidsynth@{tag}",
        "optional_feature": True,
    },
}

PIN_RE = re.compile(r'set\((LEGENDS_DEP_\w+_TAG)\s+"([^"]+)"', re.MULTILINE)


def parse_pins(text: str) -> dict[str, str]:
    return {m.group(1): m.group(2) for m in PIN_RE.finditer(text)}


def linked_tree_components() -> list[dict]:
    """In-tree libs linked by default CI (see CMakeLists legends_app sources)."""
    comps: list[dict] = []

    # ZMBV video codec — compiled into legends_app always.
    zmbv_ver = "unknown"
    if ZMBV_H.exists():
        # No stable #define; use path-local identity for honesty.
        zmbv_ver = "dosbox-x-vendored"
    comps.append(
        {
            "type": "library",
            "name": "zmbv",
            "version": zmbv_ver,
            "bom-ref": f"pkg:generic/zmbv@{zmbv_ver}",
            "purl": f"pkg:generic/zmbv@{zmbv_ver}",
            "description": "Linked in legends_app (engine/src/libs/zmbv). DOSBox-X vendored codec.",
            "properties": [
                {"name": "legends:source-path", "value": "engine/src/libs/zmbv"},
                {"name": "legends:linked-default", "value": "true"},
            ],
        }
    )

    # Optional trees present but not linked by default headless CI — inventory
    # with linked-default=false so SBOM is complete for #42 without claiming
    # they are in the default binary.
    for name, path, ver, purl, note in (
        (
            "physfs",
            "engine/src/libs/physfs",
            "vendored",
            "pkg:generic/physfs@vendored",
            "PhysicsFS tree; not in aibox_core default sources",
        ),
        (
            "libchdr",
            "engine/src/libs/libchdr",
            "vendored",
            "pkg:generic/libchdr@vendored",
            "CHD library + nested lzma/zstd; not default-linked",
        ),
        (
            "mt32-vendored",
            "engine/src/libs/mt32",
            "vendored",
            "pkg:generic/mt32emu-vendored@vendored",
            "In-tree munt snapshot; optional FetchContent pin is separate (mt32emu)",
        ),
        (
            "tinyfiledialogs",
            "engine/src/libs/tinyfiledialogs",
            "vendored",
            "pkg:generic/tinyfiledialogs@vendored",
            "Optional dialogs helper",
        ),
        (
            "xbrz",
            "engine/src/libs/xBRZ",
            "vendored",
            "pkg:generic/xbrz@vendored",
            "Scaler; optional video path",
        ),
        (
            "decoders",
            "engine/src/libs/decoders",
            "vendored-bundle",
            "pkg:generic/dosbox-decoders@vendored-bundle",
            "Audio decoder bundle (dr_*, stb, opus, ogg, speexdsp)",
        ),
        (
            "gui_tk",
            "engine/src/libs/gui_tk",
            "vendored",
            "pkg:generic/gui_tk@vendored",
            "Legacy GUI toolkit remnant",
        ),
        (
            "passthroughio",
            "engine/src/libs/passthroughio",
            "vendored",
            "pkg:generic/passthroughio@vendored",
            "Local I/O helper",
        ),
    ):
        if not (ROOT / path).exists():
            continue
        comps.append(
            {
                "type": "library",
                "name": name,
                "version": ver,
                "bom-ref": purl,
                "purl": purl,
                "description": note,
                "properties": [
                    {"name": "legends:source-path", "value": path},
                    {"name": "legends:linked-default", "value": "false"},
                ],
            }
        )

    return comps


def build_sbom(pins: dict[str, str]) -> dict:
    components: list[dict] = []

    for pin_name, meta in ACTIVE_PIN_MAP.items():
        if pin_name not in pins:
            raise SystemExit(f"Missing pin {pin_name} in dependencies.cmake")
        tag = pins[pin_name]
        version = meta["tag_to_version"](tag)
        purl = meta["purl_template"].format(tag=tag)
        desc = f"FetchContent pin {pin_name}={tag}"
        if meta.get("optional_feature"):
            desc += " (optional LEGENDS_ENABLE_FLUIDSYNTH; no in-tree 1.1.6 copy)"
        components.append(
            {
                "type": "library",
                "name": meta["name"],
                "version": version,
                "bom-ref": purl,
                "purl": purl,
                "description": desc,
            }
        )

    # Fail closed: every pin must be mapped.
    for pin_name in pins:
        if pin_name not in ACTIVE_PIN_MAP:
            raise SystemExit(f"Unmapped pin {pin_name} — update ACTIVE_PIN_MAP")

    # Fail closed: vendored 1.1.6 must not exist.
    if FLUID_VERSION_H.exists():
        raise SystemExit(
            f"Refusing SBOM generation: {FLUID_VERSION_H} still exists. "
            "Vulnerable vendored FluidSynth must stay deleted (#43)."
        )

    components.extend(linked_tree_components())

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
                        "FetchContent pins + engine/src/libs inventory. "
                        "Vendored FluidSynth 1.1.6 removed (#43). "
                        "linked-default property marks CI default link graph."
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

    names = {c["name"] for c in sbom["components"]}
    if "fluidsynth" in names:
        fluid = next(c for c in sbom["components"] if c["name"] == "fluidsynth")
        if fluid["version"].startswith("1.1"):
            print("ERROR: must not inventory FluidSynth 1.1.x", file=sys.stderr)
            return 1
    if "zmbv" not in names or "mt32emu" not in names:
        print("ERROR: zmbv and mt32emu required", file=sys.stderr)
        return 1

    if args.check:
        if not OUT.exists():
            print(f"MISSING {OUT}", file=sys.stderr)
            return 1
        existing = json.loads(OUT.read_text(encoding="utf-8"))
        if keyset(existing) != keyset(sbom):
            print("STALE vendored-sbom.cdx.json — regenerate", file=sys.stderr)
            print("expected:", keyset(sbom), file=sys.stderr)
            print("actual:  ", keyset(existing), file=sys.stderr)
            return 1
        if FLUID_VERSION_H.exists():
            print("ERROR: vendored fluidsynth version.h still present", file=sys.stderr)
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
