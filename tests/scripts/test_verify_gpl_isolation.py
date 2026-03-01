#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
#
# Tests for verify_gpl_isolation.py
# Generates known-good and known-bad map files, then verifies exit codes.

import subprocess
import sys
import tempfile
from pathlib import Path

SCRIPT_PATH = Path(__file__).parent.parent.parent / "scripts" / "verify_gpl_isolation.py"

def run_verify(map_content: str, fmt: str = "auto") -> int:
    """Write map content to a temp file and run the verification script."""
    with tempfile.NamedTemporaryFile(mode="w", suffix=".map", delete=False) as f:
        f.write(map_content)
        f.flush()
        tmp_path = f.name

    try:
        result = subprocess.run(
            [sys.executable, str(SCRIPT_PATH), tmp_path, "--format", fmt],
            capture_output=True,
            text=True,
        )
        return result.returncode
    finally:
        Path(tmp_path).unlink(missing_ok=True)


def test_clean_map_passes():
    """A map file with only MIT symbols should pass (exit 0)."""
    clean_map = """
 Timestamp is 64a1b2c3 (Mon Jul  1 12:00:00 2024)
 Preferred load address is 00400000

 Start         Length     Name                   Class
 0001:00000000 0000abcdH .text                   CODE

  Address         Publics by Value              Rva+Base       Lib:Object
 0001:00000100       legends_proxy_init          00401100     legends_proxy.lib:proxy_api.obj
 0001:00000200       legends_ipc_connect         00401200     legends_ipc.lib:control_channel.obj
 0001:00000300       MessageCodec_encode         00401300     legends_ipc.lib:message_codec.obj
 0001:00000400       ProxyConnection_request     00401400     legends_proxy.lib:proxy_connection.obj
 0001:00000500       FramebufferShm_read         00401500     legends_ipc.lib:framebuffer_shm.obj
 0001:00000600       AudioRingBuffer_pop         00401600     legends_ipc.lib:audio_ring.obj
 0001:00000700       HeartbeatMonitor_start      00401700     legends_proxy.lib:heartbeat.obj
    """
    code = run_verify(clean_map)
    assert code == 0, f"Clean map should pass, got exit code {code}"
    print("PASS: clean map -> exit 0")


def test_gpl_aibox_core_fails():
    """A map file referencing aibox_core should fail (exit 1)."""
    bad_map = """
 Timestamp is 64a1b2c3 (Mon Jul  1 12:00:00 2024)
 Preferred load address is 00400000

  Address         Publics by Value              Rva+Base       Lib:Object
 0001:00000100       legends_proxy_init          00401100     legends_proxy.lib:proxy_api.obj
 0001:00000200       CPU_Core_Normal_Run         00401200     aibox_core.lib:cpu_core.obj
 0001:00000300       DOSBox_SetSection           00401300     aibox_core.lib:dosbox.obj
    """
    code = run_verify(bad_map)
    assert code == 1, f"Map with aibox_core should fail, got exit code {code}"
    print("PASS: aibox_core map -> exit 1")


def test_gpl_legends_core_fails():
    """A map file referencing legends_core should fail (exit 1)."""
    bad_map = """
 Timestamp is 64a1b2c3 (Mon Jul  1 12:00:00 2024)

  Address         Publics by Value              Rva+Base       Lib:Object
 0001:00000100       legends_proxy_init          00401100     legends_proxy.lib:proxy_api.obj
 0001:00000200       legends_core_create         00401200     legends_core.lib:legends_api.obj
    """
    code = run_verify(bad_map)
    assert code == 1, f"Map with legends_core should fail, got exit code {code}"
    print("PASS: legends_core map -> exit 1")


def test_gpl_dosbox_symbol_fails():
    """A map file with DOSBox_ prefixed symbols should fail."""
    bad_map = """
 Timestamp is 64a1b2c3 (Mon Jul  1 12:00:00 2024)

  Address         Publics by Value              Rva+Base       Lib:Object
 0001:00000100       legends_proxy_init          00401100     legends_proxy.lib:proxy_api.obj
 0001:00000200       DOSBOX_Init                 00401200     unknown.lib:dosbox_init.obj
    """
    code = run_verify(bad_map)
    assert code == 1, f"Map with DOSBOX_ symbol should fail, got exit code {code}"
    print("PASS: DOSBOX_ symbol -> exit 1")


def test_gcc_format_clean_passes():
    """A GCC ld map with only MIT objects should pass."""
    gcc_map = """
Linker script and memory map

LOAD legends_proxy.a(proxy_api.o)
LOAD legends_ipc.a(message_codec.o)
LOAD legends_ipc.a(control_channel.o)
LOAD legends_ipc.a(framebuffer_shm.o)
LOAD legends_ipc.a(audio_ring.o)
LOAD legends_ipc.a(engine_spawner.o)

.text           0x0000000000401000     0x5000
 .text          0x0000000000401000      0x800 legends_proxy.a(proxy_api.o)
 .text          0x0000000000401800      0x400 legends_ipc.a(message_codec.o)
    """
    code = run_verify(gcc_map, fmt="gcc")
    assert code == 0, f"Clean GCC map should pass, got exit code {code}"
    print("PASS: clean GCC map -> exit 0")


def test_gcc_format_gpl_fails():
    """A GCC ld map referencing aibox_core should fail."""
    gcc_map = """
Linker script and memory map

LOAD legends_proxy.a(proxy_api.o)
LOAD aibox_core.a(cpu_core.o)
LOAD aibox_core.a(dosbox.o)

.text           0x0000000000401000     0x5000
 .text          0x0000000000401000      0x800 legends_proxy.a(proxy_api.o)
 .text          0x0000000000401800      0x400 aibox_core.a(cpu_core.o)
    """
    code = run_verify(gcc_map, fmt="gcc")
    assert code == 1, f"GCC map with aibox_core should fail, got exit code {code}"
    print("PASS: GCC map with aibox_core -> exit 1")


def test_nonexistent_file_exits_2():
    """A nonexistent map file should exit with code 2."""
    result = subprocess.run(
        [sys.executable, str(SCRIPT_PATH), "/nonexistent/path/file.map"],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 2, f"Nonexistent file should exit 2, got {result.returncode}"
    print("PASS: nonexistent file -> exit 2")


def test_empty_map_passes():
    """An empty map file should pass (no symbols to violate)."""
    code = run_verify("")
    assert code == 0, f"Empty map should pass, got exit code {code}"
    print("PASS: empty map -> exit 0")


def main() -> int:
    if not SCRIPT_PATH.exists():
        print(f"ERROR: Script not found: {SCRIPT_PATH}", file=sys.stderr)
        return 1

    tests = [
        test_clean_map_passes,
        test_gpl_aibox_core_fails,
        test_gpl_legends_core_fails,
        test_gpl_dosbox_symbol_fails,
        test_gcc_format_clean_passes,
        test_gcc_format_gpl_fails,
        test_nonexistent_file_exits_2,
        test_empty_map_passes,
    ]

    failures = 0
    for test_fn in tests:
        try:
            test_fn()
        except AssertionError as e:
            print(f"FAIL: {test_fn.__name__}: {e}")
            failures += 1
        except Exception as e:
            print(f"ERROR: {test_fn.__name__}: {e}")
            failures += 1

    print(f"\n{len(tests) - failures}/{len(tests)} tests passed")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
