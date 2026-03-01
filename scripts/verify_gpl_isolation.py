#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
#
# verify_gpl_isolation.py
#
# Reads MSVC .map or GCC/ld linker map files and fails if any GPL-licensed
# symbols are found in the application shell binary. This ensures that when
# LEGENDS_USE_IPC is ON, the shell contains zero GPL object code.

import argparse
import re
import sys
from pathlib import Path

# GPL-licensed object files and symbols that must NOT appear in the shell binary.
# These patterns match module names, object files, and known GPL symbol prefixes.
GPL_PATTERNS = [
    # Object files from GPL modules
    r"aibox_core",
    r"legends_core",
    r"dosbox",
    # Known GPL symbol prefixes from engine
    r"DOSBox_",
    r"DOSBOX_",
    r"dosbox_",
    r"CPU_Core_",
    r"GFX_",
    r"RENDER_",
    r"MIXER_",
    r"DOS_",
    r"BIOS_",
    r"IO_",
    r"PIC_",
    r"TIMER_",
    r"DMA_",
    r"INT10_",
    r"VOODOO_",
    # Engine host should not be in shell either
    r"legends_engine_host",
    r"engine_dispatcher",
]

# Symbols that are false positives (MIT-licensed code that happens to match)
ALLOWLIST_PATTERNS = [
    r"legends_ipc",
    r"legends_proxy",
    r"legends_pal",
    r"IpcError",
    r"MessageCodec",
    r"ControlChannel",
    r"SharedMemory",
    r"FramebufferShm",
    r"AudioRing",
    r"EngineSpawner",
    r"ProxyConnection",
    r"CrashHandler",
    r"HeartbeatMonitor",
]


def compile_patterns(patterns: list[str]) -> re.Pattern:
    combined = "|".join(f"(?:{p})" for p in patterns)
    return re.compile(combined)


def parse_msvc_map(path: Path) -> list[str]:
    """Parse MSVC linker .map file and return all symbol/object references."""
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    entries = []
    for line in lines:
        stripped = line.strip()
        if not stripped or stripped.startswith("Timestamp"):
            continue
        entries.append(stripped)
    return entries


def parse_gcc_map(path: Path) -> list[str]:
    """Parse GCC/ld linker map file and return all symbol/object references."""
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    entries = []
    for line in lines:
        stripped = line.strip()
        if not stripped:
            continue
        entries.append(stripped)
    return entries


def detect_format(path: Path) -> str:
    """Detect whether map file is MSVC or GCC format."""
    text = path.read_text(encoding="utf-8", errors="replace")
    # MSVC maps typically start with module name and timestamp
    if "Timestamp is" in text or "Preferred load address" in text:
        return "msvc"
    # GCC ld maps have "Linker script and memory map" or ".text" sections
    if "Linker script" in text or "LOAD " in text:
        return "gcc"
    # Default to generic line-based scan
    return "generic"


def scan_for_gpl_symbols(
    entries: list[str],
    gpl_re: re.Pattern,
    allow_re: re.Pattern,
) -> list[tuple[int, str, str]]:
    """Scan entries for GPL symbols, returning (line_num, match, line) tuples."""
    violations = []
    for i, entry in enumerate(entries, 1):
        # Skip if entry matches allowlist
        if allow_re.search(entry):
            continue
        match = gpl_re.search(entry)
        if match:
            violations.append((i, match.group(0), entry))
    return violations


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Verify GPL isolation in linker map files"
    )
    parser.add_argument(
        "map_file",
        type=Path,
        help="Path to linker .map file to scan",
    )
    parser.add_argument(
        "--format",
        choices=["msvc", "gcc", "auto"],
        default="auto",
        help="Map file format (default: auto-detect)",
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Print all scanned entries",
    )
    args = parser.parse_args()

    map_path: Path = args.map_file
    if not map_path.exists():
        print(f"ERROR: Map file not found: {map_path}", file=sys.stderr)
        return 2

    fmt = args.format
    if fmt == "auto":
        fmt = detect_format(map_path)

    if fmt == "msvc":
        entries = parse_msvc_map(map_path)
    elif fmt == "gcc":
        entries = parse_gcc_map(map_path)
    else:
        entries = map_path.read_text(encoding="utf-8", errors="replace").splitlines()

    if args.verbose:
        print(f"Scanned {len(entries)} entries from {map_path} (format: {fmt})")

    gpl_re = compile_patterns(GPL_PATTERNS)
    allow_re = compile_patterns(ALLOWLIST_PATTERNS)

    violations = scan_for_gpl_symbols(entries, gpl_re, allow_re)

    if violations:
        print(f"FAIL: Found {len(violations)} GPL symbol(s) in shell binary map:")
        for line_num, match_text, line in violations[:20]:
            print(f"  Line {line_num}: [{match_text}] {line[:120]}")
        if len(violations) > 20:
            print(f"  ... and {len(violations) - 20} more")
        return 1

    print(f"PASS: No GPL symbols found in {map_path.name} ({len(entries)} entries scanned)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
