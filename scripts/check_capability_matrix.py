#!/usr/bin/env python3
"""
Validate the public C API capability truth matrix.

The gate is intentionally static and dependency-free. It verifies that every
LEGENDS_API export has a manifest entry, that the Markdown table stays in sync
with the JSON source of truth, and that proxy-supported APIs are backed by an
engine-host dispatcher case.
"""

import argparse
import json
import os
import re
import sys


ALLOWED_DIRECT = {"implemented", "partial", "unsupported", "stub-success"}
ALLOWED_PROXY = {"proxy-supported", "proxy-partial", "proxy-missing"}


def read_text(path):
    with open(path, "r", encoding="utf-8") as handle:
        return handle.read()


def parse_header_apis(header_path):
    content = read_text(header_path)
    apis = re.findall(
        r"\bLEGENDS_API\s+legends_error_t\s+(legends_[a-z0-9_]+)\s*\(",
        content,
    )
    if apis:
        return apis

    # Fallback for declarations split across unusual whitespace.
    matches = list(re.finditer(r"\bLEGENDS_API\b", content))
    fallback = []
    for match in matches:
        snippet = content[match.start():match.start() + 300]
        name_match = re.search(r"\b(legends_[a-z0-9_]+)\s*\(", snippet)
        if name_match:
            fallback.append(name_match.group(1))
    return fallback


def find_matching_brace(content, brace_start):
    depth = 1
    pos = brace_start + 1
    while depth > 0 and pos < len(content):
        char = content[pos]
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
        pos += 1
    if depth != 0:
        return None
    return pos


def parse_c_api_functions(source_path):
    content = read_text(source_path)
    functions = {}
    pattern = re.compile(r"\blegends_error_t\s+(legends_[a-z0-9_]+)\s*\(")
    for match in pattern.finditer(content):
        func_name = match.group(1)
        brace_start = content.find("{", match.end())
        if brace_start == -1:
            continue
        body_end = find_matching_brace(content, brace_start)
        if body_end is None:
            continue
        functions[func_name] = content[brace_start:body_end]
    return functions


def parse_dispatcher_cases(dispatcher_path):
    content = read_text(dispatcher_path)
    return set(re.findall(r"\bcase\s+MsgType::([A-Za-z0-9_]+)\s*:", content))


def proxy_request_types(proxy_body):
    direct_requests = set(re.findall(r"\bMsgType::([A-Za-z0-9_]+)\b", proxy_body))
    macro_requests = set(
        re.findall(r"\bPROXY_(?:EMPTY_)?REQUEST\s*\(\s*([A-Za-z0-9_]+)", proxy_body)
    )
    return direct_requests | macro_requests


def parse_markdown_matrix(matrix_path):
    content = read_text(matrix_path)
    rows = {}
    row_re = re.compile(
        r"^\|\s*`(legends_[^`]+)`\s*\|\s*`([^`]+)`\s*\|\s*`([^`]+)`\s*\|",
        re.MULTILINE,
    )
    for match in row_re.finditer(content):
        rows[match.group(1)] = {
            "direct_status": match.group(2),
            "proxy_status": match.group(3),
        }
    return rows


def validate_manifest_entry(api_name, entry, repo_path):
    errors = []
    if not isinstance(entry, dict):
        return [f"API '{api_name}' manifest entry must be an object."]

    required_fields = {"direct_status", "proxy_status", "evidence_files", "notes"}
    missing_fields = sorted(required_fields - set(entry.keys()))
    if missing_fields:
        errors.append(f"API '{api_name}' is missing manifest fields: {missing_fields}")

    direct_status = entry.get("direct_status")
    proxy_status = entry.get("proxy_status")
    evidence_files = entry.get("evidence_files")
    notes = entry.get("notes")

    if direct_status not in ALLOWED_DIRECT:
        errors.append(
            f"API '{api_name}' has invalid direct_status '{direct_status}'. "
            f"Must be one of {sorted(ALLOWED_DIRECT)}."
        )
    if proxy_status not in ALLOWED_PROXY:
        errors.append(
            f"API '{api_name}' has invalid proxy_status '{proxy_status}'. "
            f"Must be one of {sorted(ALLOWED_PROXY)}."
        )
    if not isinstance(evidence_files, list) or not evidence_files:
        errors.append(f"API '{api_name}' must have a non-empty evidence_files list.")
    else:
        for evidence_path in evidence_files:
            if not isinstance(evidence_path, str) or not evidence_path:
                errors.append(f"API '{api_name}' has an invalid evidence path entry.")
                continue
            if not os.path.exists(os.path.join(repo_path, evidence_path)):
                errors.append(
                    f"API '{api_name}' references missing evidence file '{evidence_path}'."
                )
    if not isinstance(notes, str) or not notes.strip():
        errors.append(f"API '{api_name}' must have non-empty notes.")

    return errors


def main():
    parser = argparse.ArgumentParser(description="Validate ProjectLegends capability truth.")
    parser.add_argument("--repo", default=".", help="Repository root path")
    args = parser.parse_args()

    repo_path = os.path.abspath(args.repo)
    header_path = os.path.join(repo_path, "include", "legends", "legends_embed.h")
    direct_path = os.path.join(repo_path, "src", "legends", "legends_embed_api.cpp")
    proxy_path = os.path.join(repo_path, "src", "legends_proxy", "proxy_api.cpp")
    dispatcher_path = os.path.join(repo_path, "src", "engine_host", "engine_dispatcher.cpp")
    manifest_path = os.path.join(repo_path, "docs", "architecture", "capability_truth.json")
    matrix_path = os.path.join(
        repo_path,
        "docs",
        "architecture",
        "2026-06-08-public-capability-truth-matrix.md",
    )

    required_paths = [
        ("header", header_path),
        ("direct implementation", direct_path),
        ("proxy implementation", proxy_path),
        ("engine dispatcher", dispatcher_path),
        ("manifest", manifest_path),
        ("Markdown matrix", matrix_path),
    ]
    for label, path in required_paths:
        if not os.path.exists(path):
            print(f"FAIL: {label} file not found at {path}")
            sys.exit(1)

    header_apis = parse_header_apis(header_path)
    if not header_apis:
        print("FAIL: No C APIs parsed from header file.")
        sys.exit(1)

    seen = set()
    duplicates = []
    for api_name in header_apis:
        if api_name in seen:
            duplicates.append(api_name)
        seen.add(api_name)
    if duplicates:
        print(f"FAIL: Duplicate declarations found in header: {sorted(duplicates)}")
        sys.exit(1)

    try:
        manifest = json.loads(read_text(manifest_path))
    except Exception as exc:
        print(f"FAIL: Error parsing manifest JSON: {exc}")
        sys.exit(1)

    direct_funcs = parse_c_api_functions(direct_path)
    proxy_funcs = parse_c_api_functions(proxy_path)
    dispatcher_cases = parse_dispatcher_cases(dispatcher_path)
    markdown_rows = parse_markdown_matrix(matrix_path)

    errors = []
    header_set = set(header_apis)
    manifest_set = set(manifest.keys())
    markdown_set = set(markdown_rows.keys())

    missing_in_manifest = header_set - manifest_set
    if missing_in_manifest:
        errors.append(
            "APIs present in header but missing in capability_truth.json: "
            f"{sorted(missing_in_manifest)}"
        )

    extra_in_manifest = manifest_set - header_set
    if extra_in_manifest:
        errors.append(
            "APIs present in capability_truth.json but missing in header: "
            f"{sorted(extra_in_manifest)}"
        )

    missing_in_markdown = header_set - markdown_set
    if missing_in_markdown:
        errors.append(
            "APIs present in header but missing in Markdown matrix: "
            f"{sorted(missing_in_markdown)}"
        )

    extra_in_markdown = markdown_set - header_set
    if extra_in_markdown:
        errors.append(
            "APIs present in Markdown matrix but missing in header: "
            f"{sorted(extra_in_markdown)}"
        )

    for api_name in header_apis:
        entry = manifest.get(api_name)
        if entry is None:
            continue

        errors.extend(validate_manifest_entry(api_name, entry, repo_path))

        direct_status = entry.get("direct_status")
        proxy_status = entry.get("proxy_status")

        markdown_entry = markdown_rows.get(api_name)
        if markdown_entry:
            if markdown_entry["direct_status"] != direct_status:
                errors.append(
                    f"API '{api_name}' direct_status mismatch: manifest has "
                    f"'{direct_status}', Markdown has '{markdown_entry['direct_status']}'."
                )
            if markdown_entry["proxy_status"] != proxy_status:
                errors.append(
                    f"API '{api_name}' proxy_status mismatch: manifest has "
                    f"'{proxy_status}', Markdown has '{markdown_entry['proxy_status']}'."
                )

        direct_body = direct_funcs.get(api_name)
        if direct_body is None:
            errors.append(f"API '{api_name}' missing from direct implementation file.")
        elif direct_status == "unsupported" and "return LEGENDS_ERR_NOT_SUPPORTED;" not in direct_body:
            errors.append(
                f"API '{api_name}' is marked unsupported but direct body does not "
                "return LEGENDS_ERR_NOT_SUPPORTED directly."
            )

        proxy_body = proxy_funcs.get(api_name)
        if proxy_body is None:
            errors.append(f"API '{api_name}' missing from proxy implementation file.")
            continue

        returns_unsupported = "return LEGENDS_ERR_NOT_SUPPORTED;" in proxy_body
        requests = proxy_request_types(proxy_body)
        unhandled_requests = sorted(requests - dispatcher_cases)

        if proxy_status == "proxy-supported":
            if returns_unsupported:
                errors.append(
                    f"API '{api_name}' is proxy-supported but proxy body returns "
                    "LEGENDS_ERR_NOT_SUPPORTED directly."
                )
            if not requests:
                errors.append(
                    f"API '{api_name}' is proxy-supported but no IPC request type was found."
                )
            if unhandled_requests:
                errors.append(
                    f"API '{api_name}' is proxy-supported but dispatcher lacks cases for "
                    f"{unhandled_requests}."
                )

        if proxy_status == "proxy-missing":
            if requests and not returns_unsupported and not unhandled_requests:
                errors.append(
                    f"API '{api_name}' is proxy-missing, but proxy requests "
                    f"{sorted(requests)} and all request types have dispatcher cases."
                )

        if proxy_status == "proxy-partial" and not entry.get("notes", "").strip():
            errors.append(f"API '{api_name}' is proxy-partial but has no explanatory notes.")

    if errors:
        print("FAIL: Capability matrix validation failed.")
        for err in errors:
            print(f"  - {err}")
        sys.exit(1)

    print(
        "PASS: Capability matrix validated successfully. "
        f"{len(header_apis)} public C APIs mapped; "
        f"{len(markdown_rows)} Markdown rows synced; "
        "proxy dispatcher constraints checked."
    )
    sys.exit(0)


if __name__ == "__main__":
    main()
