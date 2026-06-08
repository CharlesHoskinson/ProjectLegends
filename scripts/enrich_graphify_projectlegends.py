#!/usr/bin/env python3
"""
Build a ProjectLegends-specific overlay for Graphify output.

The overlay is deterministic and source-derived. It does not mutate
graphify-out/graph.json; it writes a sidecar plus an optional merged graph that
can be regenerated from the Graphify output and ProjectLegends sources.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from check_capability_matrix import (  # noqa: E402
    find_matching_brace,
    parse_header_apis,
    parse_markdown_matrix,
    proxy_request_types,
    read_text,
)


SCHEMA_VERSION = 1
ORIGIN = "projectlegends-enrichment"
DERIVED = "DERIVED"
GRAPHIFY_EXTRACTED = "EXTRACTED"

HEADER_PATH = "include/legends/legends_embed.h"
DIRECT_PATH = "src/legends/legends_embed_api.cpp"
PROXY_PATH = "src/legends_proxy/proxy_api.cpp"
DISPATCHER_PATH = "src/engine_host/engine_dispatcher.cpp"
MSGTYPES_PATH = "include/legends_ipc/message_types.h"
MESSAGES_PATH = "include/legends_ipc/messages.h"
CAPABILITY_PATH = "docs/architecture/capability_truth.json"
MATRIX_PATH = "docs/architecture/2026-06-08-public-capability-truth-matrix.md"
APPLICATION_PATH = "src/app/application.cpp"
APP_ROOT = "src/app"
RUNTIME_HOST_PATH = "include/legends/runtime_host.h"
RUNTIME_HOST_IMPL_PATH = "src/app/runtime_host.cpp"
RUNTIMEHOST_ALLOWLIST_PATH = "docs/architecture/runtimehost-bypass-allowlist.json"
CMAKE_PATH = "CMakeLists.txt"
PRESETS_PATH = "CMakePresets.json"

CRITICAL_INPUTS = [
    HEADER_PATH,
    DIRECT_PATH,
    PROXY_PATH,
    DISPATCHER_PATH,
    MSGTYPES_PATH,
    MESSAGES_PATH,
    CAPABILITY_PATH,
    MATRIX_PATH,
    APPLICATION_PATH,
    RUNTIME_HOST_PATH,
    RUNTIME_HOST_IMPL_PATH,
    RUNTIMEHOST_ALLOWLIST_PATH,
    CMAKE_PATH,
    PRESETS_PATH,
]

SPECIAL_API_ALIASES = {
    "legends_force_destroy": "legends_destroy",
    "legends_key_event_ext": "legends_key_event",
}

CMAKE_KEYWORDS = {
    "PRIVATE",
    "PUBLIC",
    "INTERFACE",
    "STATIC",
    "SHARED",
    "MODULE",
    "OBJECT",
    "EXCLUDE_FROM_ALL",
    "WIN32",
    "MACOSX_BUNDLE",
}

MANDATORY_TARGETS = [
    "legends_core",
    "legends_ipc",
    "legends_proxy",
    "legends_engine_host",
    "legends_app",
    "legends_unit_tests",
    "legends_ipc_integration_tests",
    "legends_abi_test",
    "project_legends",
]


def norm_path(path: str | Path) -> str:
    return str(path).replace("\\", "/")


def rel_path(repo: Path, path: str | Path) -> str:
    path_obj = Path(path)
    if not path_obj.is_absolute():
        return norm_path(path_obj)
    return norm_path(path_obj.resolve().relative_to(repo.resolve()))


def sanitize(value: str) -> str:
    value = norm_path(value)
    value = re.sub(r"[^A-Za-z0-9_]+", "_", value)
    value = re.sub(r"_+", "_", value).strip("_")
    return value or "root"


def source_location(content: str, offset: int) -> str:
    return f"L{content.count(chr(10), 0, offset) + 1}"


def file_hash(path: Path) -> str:
    data = path.read_bytes()
    return hashlib.sha256(data).hexdigest()


def body_hash(body: str) -> str:
    return hashlib.sha256(body.encode("utf-8")).hexdigest()


def normalize_signature(signature: str) -> str:
    return re.sub(r"\s+", " ", signature.strip())


def load_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(payload, indent=2, sort_keys=True)
    path.write_text(text + "\n", encoding="utf-8")


def parse_api_declarations(header_path: Path) -> dict[str, dict[str, Any]]:
    content = read_text(str(header_path))
    declarations: dict[str, dict[str, Any]] = {}
    pattern = re.compile(
        r"\bLEGENDS_API\s+legends_error_t\s+(legends_[a-z0-9_]+)\s*\([^;]*\)\s*;",
        re.DOTALL,
    )
    for match in pattern.finditer(content):
        name = match.group(1)
        declarations[name] = {
            "name": name,
            "signature": normalize_signature(match.group(0)),
            "source_location": source_location(content, match.start()),
        }

    for name in parse_header_apis(str(header_path)):
        declarations.setdefault(
            name,
            {
                "name": name,
                "signature": name,
                "source_location": "L1",
            },
        )
    return declarations


def parse_c_api_functions_detailed(source_path: Path) -> dict[str, dict[str, Any]]:
    content = read_text(str(source_path))
    functions: dict[str, dict[str, Any]] = {}
    pattern = re.compile(r"\blegends_error_t\s+(legends_[a-z0-9_]+)\s*\(")
    for match in pattern.finditer(content):
        func_name = match.group(1)
        brace_start = content.find("{", match.end())
        if brace_start == -1:
            continue
        body_end = find_matching_brace(content, brace_start)
        if body_end is None:
            continue

        prefix_start = content.rfind("LEGENDS_API", 0, match.start())
        if prefix_start == -1:
            prefix_start = match.start()
        signature = normalize_signature(content[prefix_start:brace_start])
        body = content[brace_start:body_end]
        functions[func_name] = {
            "name": func_name,
            "signature": signature,
            "body": body,
            "body_hash": body_hash(body),
            "source_location": source_location(content, match.start()),
            "returns_not_supported": "return LEGENDS_ERR_NOT_SUPPORTED;" in body,
            "requests": sorted(proxy_request_types(body)),
            "aliases": sorted(
                name
                for name in set(re.findall(r"\b(legends_[a-z0-9_]+)\s*\(", body))
                if name != func_name
            ),
        }
    return functions


def parse_msgtypes(path: Path) -> dict[str, dict[str, Any]]:
    content = read_text(str(path))
    msgtypes: dict[str, dict[str, Any]] = {}
    in_enum = False
    category = "unknown"

    for line_number, line in enumerate(content.splitlines(), 1):
        if "enum class MsgType" in line:
            in_enum = True
            continue
        if in_enum and "};" in line:
            break
        if not in_enum:
            continue

        section_match = re.search(r"//\s*(.+)", line)
        if section_match and not re.search(r"\w+\s*=", line):
            raw = section_match.group(1)
            raw = re.sub(r"[^A-Za-z0-9 /_-]+", " ", raw)
            category = re.sub(r"\s+", " ", raw).strip().lower() or "unknown"
            continue

        match = re.search(r"\b([A-Za-z0-9_]+)\s*=\s*(0x[0-9A-Fa-f]+|\d+)", line)
        if not match:
            continue

        name = match.group(1)
        numeric_text = match.group(2)
        direction = "unknown"
        if name.endswith("Req"):
            direction = "request"
        elif name.endswith("Resp") or name.endswith("Ack"):
            direction = "response"
        elif name == "EventNotification":
            direction = "event"
        elif category == "control":
            direction = "control"

        msgtypes[name] = {
            "name": name,
            "numeric_value": int(numeric_text, 0),
            "category": category,
            "direction": direction,
            "source_location": f"L{line_number}",
        }

    return msgtypes


def parse_message_structs(path: Path) -> dict[str, dict[str, Any]]:
    content = read_text(str(path))
    structs: dict[str, dict[str, Any]] = {}
    pattern = re.compile(r"\bstruct\s+([A-Za-z0-9_]+)\s*{")
    for match in pattern.finditer(content):
        struct_name = match.group(1)
        brace_start = content.find("{", match.end() - 1)
        if brace_start == -1:
            continue
        body_end = find_matching_brace(content, brace_start)
        if body_end is None:
            continue
        body = content[brace_start:body_end]
        type_match = re.search(r"static\s+constexpr\s+MsgType\s+type\s*=\s*MsgType::([A-Za-z0-9_]+)", body)
        if not type_match:
            continue
        size_match = re.search(r"static\s+constexpr\s+size_t\s+serialized_size\s*=\s*([^;]+);", body)
        field_lines = []
        for raw_line in body.splitlines():
            line = raw_line.strip()
            if not line or line.startswith("//") or "static constexpr" in line:
                continue
            if line.endswith(";") and "(" not in line and ")" not in line:
                field_lines.append(re.sub(r"\s+", " ", line.rstrip(";")))
        structs[type_match.group(1)] = {
            "name": struct_name,
            "msgtype": type_match.group(1),
            "serialized_size": size_match.group(1).strip() if size_match else None,
            "variable_size": "serialized_size_dynamic" in body,
            "has_serialize": "serialize(" in body,
            "has_deserialize": "deserialize(" in body,
            "fields": field_lines,
            "source_location": source_location(content, match.start()),
        }
    return structs


def parse_dispatcher_cases(path: Path) -> dict[str, dict[str, Any]]:
    content = read_text(str(path))
    cases: dict[str, dict[str, Any]] = {}
    pattern = re.compile(r"\bcase\s+MsgType::([A-Za-z0-9_]+)\s*:\s*{")
    for match in pattern.finditer(content):
        name = match.group(1)
        brace_start = content.find("{", match.end() - 1)
        if brace_start == -1:
            continue
        body_end = find_matching_brace(content, brace_start)
        if body_end is None:
            continue
        body = content[brace_start:body_end]
        responses = re.findall(r"DispatchResult\s*{\s*MsgType::([A-Za-z0-9_]+)", body)
        cases[name] = {
            "msgtype": name,
            "body": body,
            "source_location": source_location(content, match.start()),
            "called_apis": sorted(set(re.findall(r"\b(legends_[a-z0-9_]+)\s*\(", body))),
            "response_msgtype": responses[0] if responses else None,
            "deserialize_calls": sorted(set(re.findall(r"\b([A-Za-z0-9_]+)::deserialize\s*\(", body))),
        }
    return cases


def iter_test_files(repo: Path) -> list[Path]:
    roots = [repo / "tests", repo / "engine" / "tests"]
    files: list[Path] = []
    for root in roots:
        if root.exists():
            files.extend(root.rglob("*.cpp"))
            files.extend(root.rglob("*.c"))
            files.extend(root.rglob("*.h"))
            files.extend(root.rglob("*.hpp"))
    return sorted(set(files))


def parse_tests(repo: Path) -> list[dict[str, Any]]:
    tests: list[dict[str, Any]] = []
    macro_re = re.compile(r"\b(TEST|TEST_F)\s*\(\s*([A-Za-z0-9_]+)\s*,\s*([A-Za-z0-9_]+)\s*\)\s*{")
    for path in iter_test_files(repo):
        content = read_text(str(path))
        for match in macro_re.finditer(content):
            brace_start = content.find("{", match.end() - 1)
            if brace_start == -1:
                continue
            body_end = find_matching_brace(content, brace_start)
            if body_end is None:
                continue
            body = content[brace_start:body_end]
            suite = match.group(2)
            name = match.group(3)
            tests.append(
                {
                    "macro": match.group(1),
                    "suite": suite,
                    "name": name,
                    "full_name": f"{suite}.{name}",
                    "disabled": suite.startswith("DISABLED_") or name.startswith("DISABLED_"),
                    "source_file": rel_path(repo, path),
                    "source_location": source_location(content, match.start()),
                    "apis": sorted(set(re.findall(r"\b(legends_[a-z0-9_]+)\s*\(", body))),
                    "msgtypes": sorted(set(re.findall(r"\bMsgType::([A-Za-z0-9_]+)\b", body))),
                }
            )
    return tests


def strip_cmake_comments(content: str) -> str:
    result = []
    for line in content.splitlines():
        in_quote = False
        cut = len(line)
        for idx, char in enumerate(line):
            if char == '"':
                in_quote = not in_quote
            if char == "#" and not in_quote:
                cut = idx
                break
        result.append(line[:cut])
    return "\n".join(result)


def parse_cmake_commands(path: Path) -> list[dict[str, Any]]:
    content = strip_cmake_comments(read_text(str(path)))
    commands: list[dict[str, Any]] = []
    pattern = re.compile(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*\(")
    pos = 0
    while True:
        match = pattern.search(content, pos)
        if not match:
            break
        depth = 1
        cursor = match.end()
        while cursor < len(content) and depth:
            if content[cursor] == "(":
                depth += 1
            elif content[cursor] == ")":
                depth -= 1
            cursor += 1
        if depth == 0:
            commands.append(
                {
                    "name": match.group(1).lower(),
                    "body": content[match.end():cursor - 1],
                    "source_location": source_location(content, match.start()),
                }
            )
        pos = max(cursor, match.end())
    return commands


def cmake_tokens(body: str) -> list[str]:
    return [
        match.group(1) or match.group(2)
        for match in re.finditer(r'"([^"]*)"|([^\s]+)', body)
        if match.group(1) or match.group(2)
    ]


def source_paths_from_token(token: str) -> list[str]:
    return [
        norm_path(match)
        for match in re.findall(
            r"([A-Za-z0-9_./+\-]+?\.(?:cpp|c|cc|cxx|h|hpp|hh|rc|manifest))",
            token,
        )
    ]


def parse_cmake(repo: Path) -> dict[str, Any]:
    path = repo / CMAKE_PATH
    commands = parse_cmake_commands(path)
    variables: dict[str, list[str]] = {}
    targets: dict[str, dict[str, Any]] = {}

    def expand(tokens: list[str]) -> list[str]:
        expanded: list[str] = []
        for token in tokens:
            var_match = re.fullmatch(r"\$\{([A-Za-z0-9_]+)\}", token)
            if var_match and var_match.group(1) in variables:
                expanded.extend(variables[var_match.group(1)])
            else:
                expanded.append(token)
        return expanded

    def ensure_target(name: str, target_type: str, source_location: str) -> dict[str, Any]:
        target = targets.setdefault(
            name,
            {
                "name": name,
                "target_type": target_type,
                "source_location": source_location,
                "sources": set(),
                "links": set(),
            },
        )
        if target["target_type"] == "unknown" and target_type != "unknown":
            target["target_type"] = target_type
        return target

    for command in commands:
        name = command["name"]
        tokens = cmake_tokens(command["body"])
        if not tokens:
            continue

        if name == "set":
            variables[tokens[0]] = expand(tokens[1:])
            continue

        if name in {"add_library", "add_executable"}:
            target_name = tokens[0]
            target_type = "library" if name == "add_library" else "executable"
            target = ensure_target(target_name, target_type, command["source_location"])
            for token in expand(tokens[1:]):
                for source in source_paths_from_token(token):
                    target["sources"].add(source)
            continue

        if name == "target_sources" and len(tokens) >= 2:
            target = ensure_target(tokens[0], "unknown", command["source_location"])
            for token in expand(tokens[1:]):
                for source in source_paths_from_token(token):
                    target["sources"].add(source)
            continue

        if name == "target_link_libraries" and len(tokens) >= 2:
            target = ensure_target(tokens[0], "unknown", command["source_location"])
            for token in expand(tokens[1:]):
                token = token.strip()
                if not token or token in CMAKE_KEYWORDS:
                    continue
                if token.startswith("$<") or token.startswith("-"):
                    continue
                if "::" in token or re.match(r"^[A-Za-z_][A-Za-z0-9_+-]*$", token):
                    target["links"].add(token)

    for target in targets.values():
        target["sources"] = sorted(target["sources"])
        target["links"] = sorted(target["links"])
    return {"targets": targets, "variables": variables}


def parse_presets(repo: Path) -> dict[str, dict[str, Any]]:
    payload = load_json(repo / PRESETS_PATH)
    presets: dict[str, dict[str, Any]] = {}
    for item in payload.get("configurePresets", []):
        name = item.get("name")
        if not name:
            continue
        presets[name] = {
            "name": name,
            "hidden": bool(item.get("hidden", False)),
            "binary_dir": item.get("binaryDir"),
            "cache_variables": item.get("cacheVariables", {}),
            "inherits": item.get("inherits"),
        }
    return presets


def mask_comments_and_strings(content: str) -> str:
    chars = list(content)
    i = 0
    state = "code"
    while i < len(chars):
        ch = chars[i]
        nxt = chars[i + 1] if i + 1 < len(chars) else ""

        if state == "code":
            if ch == "/" and nxt == "/":
                chars[i] = chars[i + 1] = " "
                i += 2
                state = "line_comment"
                continue
            if ch == "/" and nxt == "*":
                chars[i] = chars[i + 1] = " "
                i += 2
                state = "block_comment"
                continue
            if ch == '"':
                chars[i] = " "
                i += 1
                state = "string"
                continue
            if ch == "'":
                chars[i] = " "
                i += 1
                state = "char"
                continue
            i += 1
            continue

        if state == "line_comment":
            if ch == "\n":
                state = "code"
            else:
                chars[i] = " "
            i += 1
            continue

        if state == "block_comment":
            if ch == "*" and nxt == "/":
                chars[i] = chars[i + 1] = " "
                i += 2
                state = "code"
                continue
            if ch != "\n":
                chars[i] = " "
            i += 1
            continue

        if state in {"string", "char"}:
            quote = '"' if state == "string" else "'"
            if ch == "\\":
                chars[i] = " "
                if i + 1 < len(chars) and chars[i + 1] != "\n":
                    chars[i + 1] = " "
                i += 2
                continue
            if ch == quote:
                chars[i] = " "
                i += 1
                state = "code"
                continue
            if ch != "\n":
                chars[i] = " "
            i += 1

    return "".join(chars)


def normalized_line_at(content: str, offset: int) -> str:
    line_start = content.rfind("\n", 0, offset) + 1
    line_end = content.find("\n", offset)
    if line_end == -1:
        line_end = len(content)
    return re.sub(r"\s+", " ", content[line_start:line_end].strip())


def parse_function_ranges(masked_content: str) -> list[tuple[int, int, str]]:
    ranges: list[tuple[int, int, str]] = []
    control_keywords = {
        "if",
        "for",
        "while",
        "switch",
        "catch",
        "return",
        "sizeof",
        "static_cast",
        "reinterpret_cast",
        "const_cast",
        "dynamic_cast",
    }
    pattern = re.compile(
        r"^[ \t]*(?:[A-Za-z_][A-Za-z0-9_:<>,~*& \t]*[ \t]+)"
        r"([A-Za-z_~][A-Za-z0-9_:~]*)\s*\([^;{}]*\)\s*"
        r"(?:const\s*)?(?:noexcept\s*)?(?:override\s*)?\{",
        re.MULTILINE | re.DOTALL,
    )
    for match in pattern.finditer(masked_content):
        name = match.group(1)
        short_name = name.rsplit("::", 1)[-1]
        if short_name in control_keywords:
            continue
        brace_start = masked_content.find("{", match.end() - 1)
        if brace_start == -1:
            continue
        body_end = find_matching_brace(masked_content, brace_start)
        if body_end is None:
            continue
        ranges.append((match.start(), body_end, name))
    return ranges


def enclosing_function(offset: int, ranges: list[tuple[int, int, str]]) -> str:
    matches = [item for item in ranges if item[0] <= offset <= item[1]]
    if not matches:
        return "file_scope"
    matches.sort(key=lambda item: item[1] - item[0])
    return matches[0][2]


def runtimehost_methods(header_path: Path) -> dict[str, dict[str, Any]]:
    content = read_text(str(header_path))
    masked = mask_comments_and_strings(content)
    methods: dict[str, dict[str, Any]] = {}
    for match in re.finditer(r"\bvirtual\s+legends_error_t\s+([A-Za-z0-9_]+)\s*\(", masked):
        name = match.group(1)
        methods[name] = {
            "name": name,
            "source_location": source_location(content, match.start()),
        }
    factory = re.search(r"\bstd::unique_ptr\s*<\s*RuntimeHost\s*>\s+(create_runtime)\s*\(", masked)
    if factory:
        methods["create_runtime"] = {
            "name": "create_runtime",
            "source_location": source_location(content, factory.start()),
        }
    return methods


def iter_app_files(repo: Path) -> list[Path]:
    root = repo / APP_ROOT
    if not root.exists():
        return []
    exts = {".cpp", ".cc", ".cxx", ".h", ".hh", ".hpp"}
    return sorted(path for path in root.rglob("*") if path.is_file() and path.suffix in exts)


def app_call_key(call: dict[str, Any]) -> str:
    return "|".join(
        [
            norm_path(call["source_file"]),
            call["enclosing_function"],
            call["callee"],
            call["line_text"],
            str(call.get("occurrence_index", 0)),
        ]
    )


def parse_app_call_sites(repo: Path, methods: set[str] | None = None) -> list[dict[str, Any]]:
    method_names = methods or set()
    calls: list[dict[str, Any]] = []
    public_api_re = re.compile(r"\b(legends_[a-z0-9_]+)\s*\(")
    factory_re = re.compile(r"\b(create_runtime)\s*\(")
    runtime_method_re = (
        re.compile(r"\b(?:runtime_|runtime|host|runtime_host_)\s*(?:->|\.)\s*([A-Za-z0-9_]+)\s*\(")
        if method_names
        else None
    )

    for path in iter_app_files(repo):
        source_file = rel_path(repo, path)
        content = read_text(str(path))
        masked = mask_comments_and_strings(content)
        functions = parse_function_ranges(masked)
        source_area = "runtime_host_adapter" if source_file == RUNTIME_HOST_IMPL_PATH else "application_layer"

        for match in public_api_re.finditer(masked):
            callee = match.group(1)
            call = {
                "source_file": source_file,
                "source_location": source_location(content, match.start()),
                "enclosing_function": enclosing_function(match.start(), functions),
                "callee": callee,
                "call_kind": "public_c_api",
                "line_text": normalized_line_at(content, match.start()),
                "source_area": source_area,
            }
            calls.append(call)

        for match in factory_re.finditer(masked):
            callee = match.group(1)
            owner = enclosing_function(match.start(), functions)
            if owner == callee or owner.endswith(f"::{callee}"):
                continue
            call = {
                "source_file": source_file,
                "source_location": source_location(content, match.start()),
                "enclosing_function": owner,
                "callee": callee,
                "call_kind": "runtime_host",
                "line_text": normalized_line_at(content, match.start()),
                "source_area": source_area,
            }
            calls.append(call)

        if runtime_method_re:
            for match in runtime_method_re.finditer(masked):
                callee = match.group(1)
                if callee not in method_names:
                    continue
                call = {
                    "source_file": source_file,
                    "source_location": source_location(content, match.start()),
                    "enclosing_function": enclosing_function(match.start(), functions),
                    "callee": callee,
                    "call_kind": "runtime_host",
                    "line_text": normalized_line_at(content, match.start()),
                    "source_area": source_area,
                }
                calls.append(call)

    calls = sorted(calls, key=lambda item: (item["source_file"], item["source_location"], item["callee"], item["line_text"]))
    occurrences: Counter[tuple[str, str, str, str]] = Counter()
    for call in calls:
        occurrence_key = (
            call["source_file"],
            call["enclosing_function"],
            call["callee"],
            call["line_text"],
        )
        call["occurrence_index"] = occurrences[occurrence_key]
        occurrences[occurrence_key] += 1
        call["key"] = app_call_key(call)
    return calls



def load_runtimehost_allowlist(repo: Path) -> dict[str, Any]:
    path = repo / RUNTIMEHOST_ALLOWLIST_PATH
    if not path.exists():
        return {"schema_version": 1, "allowed_bypasses": []}
    return load_json(path)


class OverlayBuilder:
    def __init__(self, repo: Path) -> None:
        self.repo = repo.resolve()
        self.nodes: dict[str, dict[str, Any]] = {}
        self.links: dict[str, dict[str, Any]] = {}

    def add_node(self, node_id: str, label: str, kind: str, **attrs: Any) -> str:
        payload = {
            "id": node_id,
            "label": label,
            "kind": kind,
            "_origin": ORIGIN,
        }
        payload.update({key: value for key, value in attrs.items() if value is not None})
        if node_id in self.nodes:
            self.nodes[node_id].update(payload)
        else:
            self.nodes[node_id] = payload
        return node_id

    def add_file_node(self, path: str) -> str:
        path = norm_path(path)
        return self.add_node(
            f"pl__file__{sanitize(path)}",
            path,
            "source_file",
            path=path,
            source_file=path,
            source_location="L1",
        )

    def add_link(
        self,
        source: str,
        target: str,
        relation: str,
        *,
        source_file: str | None = None,
        source_location: str | None = None,
        **attrs: Any,
    ) -> str:
        digest = hashlib.sha1(f"{source}|{relation}|{target}".encode("utf-8")).hexdigest()[:16]
        link_id = f"pl__edge__{sanitize(relation)}__{digest}"
        payload = {
            "id": link_id,
            "source": source,
            "target": target,
            "relation": relation,
            "confidence": DERIVED,
            "weight": 1.0,
            "_origin": ORIGIN,
        }
        if source_file:
            payload["source_file"] = norm_path(source_file)
        if source_location:
            payload["source_location"] = source_location
        payload.update({key: value for key, value in attrs.items() if value is not None})
        self.links[link_id] = payload
        return link_id

    def add_source_edge(self, node_id: str, path: str, relation: str = "declared_in") -> None:
        file_id = self.add_file_node(path)
        source_location = self.nodes[node_id].get("source_location")
        self.add_link(
            node_id,
            file_id,
            relation,
            source_file=path,
            source_location=source_location,
        )

    def sorted_nodes(self) -> list[dict[str, Any]]:
        return [self.nodes[key] for key in sorted(self.nodes)]

    def sorted_links(self) -> list[dict[str, Any]]:
        return [self.links[key] for key in sorted(self.links)]


def build_overlay(repo: Path, graphify_path: Path, *, allow_missing_graphify: bool = False) -> dict[str, Any]:
    repo = repo.resolve()
    if graphify_path.exists():
        graphify = load_json(graphify_path)
    elif allow_missing_graphify:
        graphify = {"nodes": [], "links": []}
    else:
        raise FileNotFoundError(f"Graphify graph not found: {graphify_path}")
    if not isinstance(graphify, dict) or "nodes" not in graphify or "links" not in graphify:
        raise ValueError(f"Unsupported Graphify JSON shape: {graphify_path}")

    builder = OverlayBuilder(repo)

    for input_path in CRITICAL_INPUTS:
        builder.add_file_node(input_path)

    declarations = parse_api_declarations(repo / HEADER_PATH)
    header_apis = parse_header_apis(str(repo / HEADER_PATH))
    manifest = load_json(repo / CAPABILITY_PATH)
    matrix = parse_markdown_matrix(str(repo / MATRIX_PATH))
    direct_funcs = parse_c_api_functions_detailed(repo / DIRECT_PATH)
    proxy_funcs = parse_c_api_functions_detailed(repo / PROXY_PATH)
    msgtypes = parse_msgtypes(repo / MSGTYPES_PATH)
    message_structs = parse_message_structs(repo / MESSAGES_PATH)
    dispatcher_cases = parse_dispatcher_cases(repo / DISPATCHER_PATH)
    tests = parse_tests(repo)
    cmake = parse_cmake(repo)
    presets = parse_presets(repo)
    runtime_methods = runtimehost_methods(repo / RUNTIME_HOST_PATH)
    app_calls = parse_app_call_sites(repo, set(runtime_methods))
    runtimehost_allowlist = load_runtimehost_allowlist(repo)
    allowed_bypass_keys = {
        "|".join(
            [
                norm_path(entry.get("source_file", "")),
                entry.get("enclosing_function", ""),
                entry.get("api", ""),
                entry.get("line_text", ""),
                str(entry.get("occurrence_index", 0)),
            ]
        )
        for entry in runtimehost_allowlist.get("allowed_bypasses", [])
        if isinstance(entry, dict)
    }
    allowed_bypass_keys.update(
        str(key)
        for key in runtimehost_allowlist.get("allowed_bypass_keys", [])
        if isinstance(key, str)
    )

    api_nodes: dict[str, str] = {}
    direct_nodes: dict[str, str] = {}
    proxy_nodes: dict[str, str] = {}
    msgtype_nodes: dict[str, str] = {}
    dispatcher_nodes: dict[str, str] = {}
    runtimehost_method_nodes: dict[str, str] = {}
    file_nodes_by_path: dict[str, str] = {}

    for api in header_apis:
        decl = declarations.get(api, {"signature": api, "source_location": "L1"})
        node_id = f"pl__api__{api}"
        api_nodes[api] = builder.add_node(
            node_id,
            api,
            "public_c_api",
            name=api,
            source_file=HEADER_PATH,
            source_location=decl["source_location"],
            signature=decl["signature"],
        )
        builder.add_source_edge(node_id, HEADER_PATH, "declared_in")

        entry = manifest.get(api, {})
        cap_id = f"pl__capability__{api}"
        builder.add_node(
            cap_id,
            api,
            "capability_entry",
            api=api,
            source_file=CAPABILITY_PATH,
            source_location="L1",
            direct_status=entry.get("direct_status"),
            proxy_status=entry.get("proxy_status"),
            notes=entry.get("notes"),
            evidence_files=entry.get("evidence_files", []),
        )
        builder.add_link(node_id, cap_id, "has_capability_entry", source_file=CAPABILITY_PATH)
        for evidence_path in entry.get("evidence_files", []):
            evidence_id = builder.add_file_node(evidence_path)
            file_nodes_by_path[norm_path(evidence_path)] = evidence_id
            builder.add_link(
                cap_id,
                evidence_id,
                "claims_evidence_file",
                source_file=CAPABILITY_PATH,
            )

        row = matrix.get(api, {})
        row_id = f"pl__matrix_row__{api}"
        builder.add_node(
            row_id,
            api,
            "capability_matrix_row",
            api=api,
            source_file=MATRIX_PATH,
            source_location="L1",
            direct_status=row.get("direct_status"),
            proxy_status=row.get("proxy_status"),
        )
        builder.add_link(node_id, row_id, "has_matrix_row", source_file=MATRIX_PATH)

        if api in direct_funcs:
            details = direct_funcs[api]
            direct_id = f"pl__direct_impl__{api}"
            direct_nodes[api] = builder.add_node(
                direct_id,
                api,
                "direct_c_api_impl",
                api=api,
                source_file=DIRECT_PATH,
                source_location=details["source_location"],
                signature=details["signature"],
                body_hash=details["body_hash"],
            )
            builder.add_link(
                node_id,
                direct_id,
                "direct_implemented_by",
                source_file=DIRECT_PATH,
                source_location=details["source_location"],
            )
            builder.add_source_edge(direct_id, DIRECT_PATH, "declared_in")

        if api in proxy_funcs:
            details = proxy_funcs[api]
            aliases = sorted(set(details["aliases"] + ([SPECIAL_API_ALIASES[api]] if api in SPECIAL_API_ALIASES else [])))
            proxy_id = f"pl__proxy_impl__{api}"
            proxy_nodes[api] = builder.add_node(
                proxy_id,
                api,
                "proxy_c_api_impl",
                api=api,
                source_file=PROXY_PATH,
                source_location=details["source_location"],
                signature=details["signature"],
                body_hash=details["body_hash"],
                returns_not_supported=details["returns_not_supported"],
                requests=details["requests"],
                aliases=aliases,
            )
            builder.add_link(
                node_id,
                proxy_id,
                "proxy_implemented_by",
                source_file=PROXY_PATH,
                source_location=details["source_location"],
            )
            builder.add_source_edge(proxy_id, PROXY_PATH, "declared_in")

    for name, details in msgtypes.items():
        msg_id = f"pl__msgtype__{name}"
        msgtype_nodes[name] = builder.add_node(
            msg_id,
            name,
            "ipc_msgtype",
            name=name,
            source_file=MSGTYPES_PATH,
            source_location=details["source_location"],
            numeric_value=details["numeric_value"],
            category=details["category"],
            direction=details["direction"],
        )
        builder.add_source_edge(msg_id, MSGTYPES_PATH, "declared_in")

    for name, details in msgtypes.items():
        if name.endswith("Req"):
            response = name[:-3] + "Resp"
            if response in msgtype_nodes:
                builder.add_link(
                    msgtype_nodes[name],
                    msgtype_nodes[response],
                    "paired_with_response",
                    source_file=MSGTYPES_PATH,
                    source_location=details["source_location"],
                )

    for msgtype, details in message_structs.items():
        struct_id = f"pl__msgstruct__{details['name']}"
        builder.add_node(
            struct_id,
            details["name"],
            "ipc_message_struct",
            name=details["name"],
            msgtype=msgtype,
            source_file=MESSAGES_PATH,
            source_location=details["source_location"],
            serialized_size=details["serialized_size"],
            variable_size=details["variable_size"],
            has_serialize=details["has_serialize"],
            has_deserialize=details["has_deserialize"],
            fields=details["fields"],
        )
        builder.add_source_edge(struct_id, MESSAGES_PATH, "declared_in")
        if msgtype in msgtype_nodes:
            builder.add_link(
                msgtype_nodes[msgtype],
                struct_id,
                "typed_by_struct",
                source_file=MESSAGES_PATH,
                source_location=details["source_location"],
            )

    for api, proxy_id in proxy_nodes.items():
        details = proxy_funcs[api]
        for request in details["requests"]:
            if request in msgtype_nodes:
                builder.add_link(
                    proxy_id,
                    msgtype_nodes[request],
                    "sends_request",
                    source_file=PROXY_PATH,
                    source_location=details["source_location"],
                )
        aliases = sorted(set(details["aliases"] + ([SPECIAL_API_ALIASES[api]] if api in SPECIAL_API_ALIASES else [])))
        for alias in aliases:
            if alias in api_nodes:
                builder.add_link(
                    proxy_id,
                    api_nodes[alias],
                    "aliases_api",
                    source_file=PROXY_PATH,
                    source_location=details["source_location"],
                )

    for msgtype, details in dispatcher_cases.items():
        case_id = f"pl__dispatcher_case__{msgtype}"
        dispatcher_nodes[msgtype] = builder.add_node(
            case_id,
            msgtype,
            "dispatcher_case",
            msgtype=msgtype,
            source_file=DISPATCHER_PATH,
            source_location=details["source_location"],
            called_apis=details["called_apis"],
            response_msgtype=details["response_msgtype"],
            deserialize_calls=details["deserialize_calls"],
        )
        builder.add_source_edge(case_id, DISPATCHER_PATH, "declared_in")
        if msgtype in msgtype_nodes:
            builder.add_link(
                msgtype_nodes[msgtype],
                case_id,
                "handled_by_dispatcher",
                source_file=DISPATCHER_PATH,
                source_location=details["source_location"],
            )
        if details["response_msgtype"] in msgtype_nodes:
            builder.add_link(
                case_id,
                msgtype_nodes[details["response_msgtype"]],
                "dispatcher_returns",
                source_file=DISPATCHER_PATH,
                source_location=details["source_location"],
            )
        for called_api in details["called_apis"]:
            if called_api in api_nodes:
                builder.add_link(
                    case_id,
                    api_nodes[called_api],
                    "dispatch_calls_api",
                    source_file=DISPATCHER_PATH,
                    source_location=details["source_location"],
                )

    runtimehost_id = builder.add_node(
        "pl__runtime_host__RuntimeHost",
        "RuntimeHost",
        "runtime_host_interface",
        name="RuntimeHost",
        source_file=RUNTIME_HOST_PATH,
        source_location="L19",
    )
    builder.add_source_edge(runtimehost_id, RUNTIME_HOST_PATH, "declared_in")

    for method_name, details in sorted(runtime_methods.items()):
        method_id = f"pl__runtime_host_method__{sanitize(method_name)}"
        runtimehost_method_nodes[method_name] = builder.add_node(
            method_id,
            method_name,
            "runtime_host_method",
            name=method_name,
            source_file=RUNTIME_HOST_PATH,
            source_location=details["source_location"],
        )
        builder.add_link(
            runtimehost_id,
            method_id,
            "declares_runtime_method",
            source_file=RUNTIME_HOST_PATH,
            source_location=details["source_location"],
        )

    for call in app_calls:
        digest = hashlib.sha1(call["key"].encode("utf-8")).hexdigest()[:16]
        call_id = (
            f"pl__app_call__{sanitize(call['source_file'])}__"
            f"{sanitize(call['source_location'])}__{sanitize(call['callee'])}__{digest}"
        )
        builder.add_node(
            call_id,
            f"{call['source_file']}:{call['source_location']} {call['callee']}",
            "app_call_site",
            source_file=call["source_file"],
            source_location=call["source_location"],
            enclosing_function=call["enclosing_function"],
            callee=call["callee"],
            call_kind=call["call_kind"],
            line_text=call["line_text"],
            source_area=call["source_area"],
            occurrence_index=call["occurrence_index"],
            allowlist_key=call["key"],
            runtime_host_bypass_allowed=call["key"] in allowed_bypass_keys,
        )
        builder.add_source_edge(call_id, call["source_file"], "declared_in")
        if call["call_kind"] == "public_c_api" and call["callee"] in api_nodes:
            builder.add_link(
                call_id,
                api_nodes[call["callee"]],
                "app_calls_public_api",
                source_file=call["source_file"],
                source_location=call["source_location"],
            )
            if call["source_area"] != "runtime_host_adapter":
                builder.add_link(
                    call_id,
                    api_nodes[call["callee"]],
                    "bypasses_runtime_host",
                    source_file=call["source_file"],
                    source_location=call["source_location"],
                    allowlist_key=call["key"],
                    allowlisted=call["key"] in allowed_bypass_keys,
                )
        elif call["call_kind"] == "runtime_host" and call["callee"] in runtimehost_method_nodes:
            builder.add_link(
                call_id,
                runtimehost_method_nodes[call["callee"]],
                "app_calls_runtime_host",
                source_file=call["source_file"],
                source_location=call["source_location"],
            )

    for test in tests:
        file_id = builder.add_file_node(test["source_file"])
        test_id = f"pl__test_case__{sanitize(test['source_file'])}__{sanitize(test['full_name'])}"
        builder.add_node(
            test_id,
            test["full_name"],
            "test_case",
            suite=test["suite"],
            name=test["name"],
            disabled=test["disabled"],
            source_file=test["source_file"],
            source_location=test["source_location"],
            apis=test["apis"],
            msgtypes=test["msgtypes"],
        )
        builder.add_link(
            file_id,
            test_id,
            "contains_test_case",
            source_file=test["source_file"],
            source_location=test["source_location"],
        )
        for api in test["apis"]:
            if api in api_nodes:
                builder.add_link(
                    test_id,
                    api_nodes[api],
                    "covers_api_call",
                    source_file=test["source_file"],
                    source_location=test["source_location"],
                    disabled=test["disabled"],
                )
        for msgtype in test["msgtypes"]:
            if msgtype in msgtype_nodes:
                builder.add_link(
                    test_id,
                    msgtype_nodes[msgtype],
                    "covers_msgtype",
                    source_file=test["source_file"],
                    source_location=test["source_location"],
                    disabled=test["disabled"],
                )
            if msgtype in dispatcher_nodes:
                builder.add_link(
                    test_id,
                    dispatcher_nodes[msgtype],
                    "exercises_dispatcher_case",
                    source_file=test["source_file"],
                    source_location=test["source_location"],
                    disabled=test["disabled"],
                )

    for preset_name, preset in presets.items():
        builder.add_node(
            f"pl__cmake_preset__{sanitize(preset_name)}",
            preset_name,
            "cmake_preset",
            name=preset_name,
            hidden=preset["hidden"],
            binary_dir=preset["binary_dir"],
            cache_variables=preset["cache_variables"],
            inherits=preset["inherits"],
            source_file=PRESETS_PATH,
            source_location="L1",
        )

    target_nodes: dict[str, str] = {}
    source_nodes: dict[str, str] = dict(file_nodes_by_path)
    for target_name, target in sorted(cmake["targets"].items()):
        target_id = f"pl__cmake_target__{sanitize(target_name)}"
        target_nodes[target_name] = builder.add_node(
            target_id,
            target_name,
            "cmake_target",
            name=target_name,
            target_type=target["target_type"],
            source_file=CMAKE_PATH,
            source_location=target["source_location"],
            sources=target["sources"],
            links=target["links"],
        )
        builder.add_source_edge(target_id, CMAKE_PATH, "declared_in")
        for preset_name in presets:
            preset_id = f"pl__cmake_preset__{sanitize(preset_name)}"
            builder.add_link(target_id, preset_id, "configured_by_preset", source_file=PRESETS_PATH)
        for source in target["sources"]:
            source_id = source_nodes.setdefault(source, builder.add_file_node(source))
            builder.add_link(target_id, source_id, "includes_source", source_file=CMAKE_PATH)
            if source == DIRECT_PATH:
                for impl_id in direct_nodes.values():
                    builder.add_link(target_id, impl_id, "builds_api_impl", source_file=CMAKE_PATH)
            if source == PROXY_PATH:
                for impl_id in proxy_nodes.values():
                    builder.add_link(target_id, impl_id, "builds_proxy_impl", source_file=CMAKE_PATH)
            if source == DISPATCHER_PATH:
                for case_id in dispatcher_nodes.values():
                    builder.add_link(target_id, case_id, "builds_dispatcher", source_file=CMAKE_PATH)
            if source.startswith("tests/"):
                builder.add_link(target_id, source_id, "builds_test_file", source_file=CMAKE_PATH)

    for target_name, target in sorted(cmake["targets"].items()):
        source_id = target_nodes.get(target_name)
        if not source_id:
            continue
        for link_target in target["links"]:
            target_id = target_nodes.get(link_target)
            if target_id:
                builder.add_link(source_id, target_id, "links_target", source_file=CMAKE_PATH)

    source_hashes: dict[str, str] = {}
    tracked_sources = CRITICAL_INPUTS + [test["source_file"] for test in tests] + [
        rel_path(repo, path) for path in iter_app_files(repo)
    ]
    for input_path in sorted(set(tracked_sources)):
        path = repo / input_path
        if path.exists() and path.is_file():
            source_hashes[norm_path(input_path)] = file_hash(path)

    nodes = builder.sorted_nodes()
    links = builder.sorted_links()
    node_counts = Counter(node["kind"] for node in nodes)
    link_counts = Counter(link["relation"] for link in links)
    proxy_status_counts = Counter(
        entry.get("proxy_status", "unknown")
        for entry in manifest.values()
        if isinstance(entry, dict)
    )
    direct_status_counts = Counter(
        entry.get("direct_status", "unknown")
        for entry in manifest.values()
        if isinstance(entry, dict)
    )
    app_call_counts = Counter(call["call_kind"] for call in app_calls)
    app_bypass_count = sum(
        1
        for call in app_calls
        if call["call_kind"] == "public_c_api" and call["source_area"] != "runtime_host_adapter"
    )
    allowlisted_app_bypass_count = sum(
        1
        for call in app_calls
        if call["call_kind"] == "public_c_api"
        and call["source_area"] != "runtime_host_adapter"
        and call["key"] in allowed_bypass_keys
    )

    return {
        "schema_version": SCHEMA_VERSION,
        "generator": "scripts/enrich_graphify_projectlegends.py",
        "generated_at": "deterministic-source-derived",
        "graphify_graph": rel_path(repo, graphify_path),
        "allow_missing_graphify": allow_missing_graphify,
        "source_hashes": source_hashes,
        "nodes": nodes,
        "links": links,
        "summary": {
            "graphify_nodes": len(graphify.get("nodes", [])),
            "graphify_links": len(graphify.get("links", [])),
            "enrichment_nodes": len(nodes),
            "enrichment_links": len(links),
            "node_counts": dict(sorted(node_counts.items())),
            "link_counts": dict(sorted(link_counts.items())),
            "public_api_count": len(header_apis),
            "direct_status_counts": dict(sorted(direct_status_counts.items())),
            "proxy_status_counts": dict(sorted(proxy_status_counts.items())),
            "dispatcher_case_count": len(dispatcher_cases),
            "test_case_count": len(tests),
            "cmake_target_count": len(cmake["targets"]),
            "runtimehost_method_count": len(runtime_methods),
            "app_call_counts": dict(sorted(app_call_counts.items())),
            "runtimehost_bypass_count": app_bypass_count,
            "runtimehost_allowlisted_bypass_count": allowlisted_app_bypass_count,
        },
    }


def merge_graph(graphify_path: Path, overlay: dict[str, Any]) -> dict[str, Any]:
    if graphify_path.exists():
        graph = load_json(graphify_path)
    elif overlay.get("allow_missing_graphify"):
        graph = {"nodes": [], "links": []}
    else:
        raise FileNotFoundError(f"Graphify graph not found: {graphify_path}")
    merged = dict(graph)
    merged["nodes"] = list(graph.get("nodes", [])) + list(overlay["nodes"])
    merged["links"] = list(graph.get("links", [])) + list(overlay["links"])
    merged["projectlegends_enrichment"] = {
        "schema_version": overlay["schema_version"],
        "generator": overlay["generator"],
        "source_hashes": overlay["source_hashes"],
        "summary": overlay["summary"],
    }
    return merged


def write_report(path: Path, overlay: dict[str, Any]) -> None:
    summary = overlay["summary"]
    node_counts = summary["node_counts"]
    link_counts = summary["link_counts"]
    proxy_counts = summary["proxy_status_counts"]
    direct_counts = summary["direct_status_counts"]
    lines = [
        "# Graphify ProjectLegends Enrichment Report",
        "",
        "This report is generated by `scripts/enrich_graphify_projectlegends.py`.",
        "",
        "## Summary",
        "",
        f"* Graphify base nodes: {summary['graphify_nodes']}",
        f"* Graphify base links: {summary['graphify_links']}",
        f"* Enrichment nodes: {summary['enrichment_nodes']}",
        f"* Enrichment links: {summary['enrichment_links']}",
        f"* Public C APIs: {summary['public_api_count']}",
        f"* Dispatcher cases: {summary['dispatcher_case_count']}",
        f"* Test cases scanned: {summary['test_case_count']}",
        f"* CMake targets scanned: {summary['cmake_target_count']}",
        f"* RuntimeHost methods: {summary['runtimehost_method_count']}",
        f"* App direct RuntimeHost bypasses: {summary['runtimehost_bypass_count']}",
        f"* Allowlisted app RuntimeHost bypasses: {summary['runtimehost_allowlisted_bypass_count']}",
        "",
        "## Capability Status Counts",
        "",
        "| Status Type | Status | Count |",
        "|---|---:|---:|",
    ]
    for status, count in direct_counts.items():
        lines.append(f"| direct | `{status}` | {count} |")
    for status, count in proxy_counts.items():
        lines.append(f"| proxy | `{status}` | {count} |")

    lines.extend(["", "## Node Counts", "", "| Kind | Count |", "|---|---:|"])
    for kind, count in sorted(node_counts.items()):
        lines.append(f"| `{kind}` | {count} |")

    lines.extend(["", "## Edge Counts", "", "| Relation | Count |", "|---|---:|"])
    for relation, count in sorted(link_counts.items()):
        lines.append(f"| `{relation}` | {count} |")

    lines.extend(
        [
            "",
            "## Regeneration",
            "",
            "```powershell",
            "python scripts/enrich_graphify_projectlegends.py --repo . --graphify graphify-out/graph.json --out graphify-out/projectlegends-enrichment.json --merged graphify-out/projectlegends-graph-enriched.json --report docs/architecture/graphify-enrichment-report.md",
            "python scripts/check_graphify_enrichment.py --repo . --overlay graphify-out/projectlegends-enrichment.json --strict",
            "```",
            "",
        ]
    )
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Build ProjectLegends Graphify enrichment overlay.")
    parser.add_argument("--repo", default=".", help="Repository root")
    parser.add_argument("--graphify", default="graphify-out/graph.json", help="Graphify graph JSON")
    parser.add_argument("--out", default="graphify-out/projectlegends-enrichment.json", help="Overlay output JSON")
    parser.add_argument("--merged", default="graphify-out/projectlegends-graph-enriched.json", help="Merged graph output JSON")
    parser.add_argument("--report", default="docs/architecture/graphify-enrichment-report.md", help="Markdown report output")
    parser.add_argument(
        "--allow-missing-graphify",
        action="store_true",
        help="Use an empty base graph when graphify-out/graph.json is unavailable, intended for CI source-only validation",
    )
    parser.add_argument("--check", action="store_true", help="Also run the checker after writing outputs")
    args = parser.parse_args()

    repo = Path(args.repo).resolve()
    graphify_path = (repo / args.graphify).resolve()
    overlay_path = (repo / args.out).resolve()
    merged_path = (repo / args.merged).resolve()
    report_path = (repo / args.report).resolve()

    overlay = build_overlay(repo, graphify_path, allow_missing_graphify=args.allow_missing_graphify)
    write_json(overlay_path, overlay)
    write_json(merged_path, merge_graph(graphify_path, overlay))
    write_report(report_path, overlay)

    print(
        "PASS: wrote ProjectLegends Graphify enrichment. "
        f"{overlay['summary']['enrichment_nodes']} nodes; "
        f"{overlay['summary']['enrichment_links']} links."
    )
    print(f"Overlay: {rel_path(repo, overlay_path)}")
    print(f"Merged: {rel_path(repo, merged_path)}")
    print(f"Report: {rel_path(repo, report_path)}")

    if args.check:
        import check_graphify_enrichment

        return check_graphify_enrichment.run_from_builder(repo, overlay_path, strict=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
