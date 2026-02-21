#!/usr/bin/env python3
"""
check_compiler.py - Detect compilers and probe C++23 feature support.

Outputs JSON with discovered compilers, compile probes for C++23 features,
and suggested upgrade hints.
"""

from __future__ import annotations

import argparse
import json
import platform
import re
import shutil
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Optional


@dataclass(frozen=True)
class Compiler:
    kind: str  # gcc|clang|msvc
    path: str


def _run(cmd: list[str], cwd: Optional[str] = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd, cwd=cwd, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
    )


def _which(names: Iterable[str]) -> list[str]:
    out: list[str] = []
    for n in names:
        p = shutil.which(n)
        if p and p not in out:
            out.append(p)
    return out


def _parse_version(text: str) -> str:
    m = re.search(r"(\d+\.\d+(?:\.\d+)*)", text)
    return m.group(1) if m else "unknown"


def _identify_compiler(path: str) -> Compiler:
    base = Path(path).name.lower()
    if base in ("cl", "cl.exe"):
        return Compiler(kind="msvc", path=path)
    if "clang" in base:
        return Compiler(kind="clang", path=path)
    return Compiler(kind="gcc", path=path)


def _write(p: Path, s: str) -> None:
    p.write_text(s, encoding="utf-8", newline="\n")


def _compile_link_gcc_like(cxx: str, code: str, extra: list[str]) -> tuple[bool, str]:
    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        src = td_path / "t.cpp"
        exe = td_path / ("a.exe" if platform.system() == "Windows" else "a.out")
        _write(src, code)
        cmd = [cxx, "-std=c++23", "-O0", "-g", str(src), "-o", str(exe)] + extra
        r = _run(cmd)
        return r.returncode == 0, (r.stdout + r.stderr).strip()


def _compile_link_msvc(cl: str, code: str, extra: list[str]) -> tuple[bool, str]:
    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        src = td_path / "t.cpp"
        _write(src, code)
        cmd = [cl, "/nologo", "/std:c++latest", "/EHsc", "/W4", "/WX", str(src)] + extra
        r = _run(cmd, cwd=str(td_path))
        return r.returncode == 0, (r.stdout + r.stderr).strip()


def _probe(compiler: Compiler, snippet: str, extra: list[str] | None = None) -> dict[str, Any]:
    extra = extra or []
    if compiler.kind in ("gcc", "clang"):
        ok, out = _compile_link_gcc_like(compiler.path, snippet, extra)
    else:
        ok, out = _compile_link_msvc(compiler.path, snippet, extra)
    return {"ok": ok, "output": out[:4000]}


SNIP_EXPECTED = r"""
#include <expected>
#include <cstdint>
#include <type_traits>

enum class Err : std::uint8_t { bad };

std::expected<int, Err> parse(bool ok) {
    if (!ok) return std::unexpected(Err::bad);
    return 7;
}

int main() {
    auto v = parse(true)
        .and_then([](int x){ return std::expected<int, Err>(x + 1); })
        .transform([](int x){ return x * 2; });
    static_assert(std::is_same_v<decltype(v), std::expected<int, Err>>);
    return v ? 0 : 1;
}
"""

SNIP_PRINT = r"""
#include <print>
int main() { std::println("{}", 123); }
"""

SNIP_DEDUCING_THIS = r"""
struct X {
    void f(this auto&& self) { (void)self; }
};
int main() { X x; x.f(); }
"""

SNIP_IF_CONSTEVAL = r"""
consteval int f() { return 42; }
constexpr int g() {
    if consteval { return f(); }
    else { return 0; }
}
int main() { return g() == 42 ? 0 : 1; }
"""

SNIP_MULTI_SUBSCRIPT = r"""
struct A {
    int operator[](int i, int j) const { return i + j; }
};
int main() { A a; return a[1,2] == 3 ? 0 : 1; }
"""

SNIP_GENERATOR = r"""
#include <generator>
#include <cstdint>

std::generator<std::int32_t> gen() {
    co_yield 1;
    co_yield 2;
}

int main() {
    std::int32_t sum = 0;
    for (auto v : gen()) sum += v;
    return sum == 3 ? 0 : 1;
}
"""

SNIP_MDSPAN = r"""
#include <mdspan>
#include <array>

int main() {
    std::array<int, 6> buf{1,2,3,4,5,6};
    std::mdspan<int, std::extents<std::size_t, 2, 3>> m(buf.data());
    return m(1,2) == 6 ? 0 : 1;
}
"""


def main() -> int:
    ap = argparse.ArgumentParser(description="Detect compilers and probe C++23 feature support.")
    ap.add_argument("--json", action="store_true", help="JSON output (default)")
    _ = ap.parse_args()

    candidates = []
    candidates += _which(["g++", "c++"])
    candidates += _which(["clang++"])
    candidates += _which(["cl"])

    compilers: list[Compiler] = [_identify_compiler(p) for p in candidates]

    report: dict[str, Any] = {
        "platform": {
            "system": platform.system(),
            "release": platform.release(),
            "machine": platform.machine(),
        },
        "compilers": [],
    }

    for c in compilers:
        ver_out = _run([c.path, "--version"]).stdout + _run([c.path, "--version"]).stderr
        version = _parse_version(ver_out)

        entry: dict[str, Any] = {
            "kind": c.kind,
            "path": c.path,
            "version_guess": version,
            "probes": {},
            "notes": [],
        }

        entry["probes"]["deducing_this"] = _probe(c, SNIP_DEDUCING_THIS)
        entry["probes"]["if_consteval"] = _probe(c, SNIP_IF_CONSTEVAL)
        entry["probes"]["multidimensional_subscript"] = _probe(c, SNIP_MULTI_SUBSCRIPT)
        entry["probes"]["std_expected"] = _probe(c, SNIP_EXPECTED)
        entry["probes"]["std_print"] = _probe(c, SNIP_PRINT)
        entry["probes"]["std_generator"] = _probe(c, SNIP_GENERATOR)
        entry["probes"]["std_mdspan"] = _probe(c, SNIP_MDSPAN)

        if not entry["probes"]["std_expected"]["ok"]:
            entry["notes"].append("std::expected failed. Ensure <expected> is available.")
        if not entry["probes"]["std_print"]["ok"]:
            entry["notes"].append("std::print failed. Consider iostream fallback.")

        report["compilers"].append(entry)

    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
