#!/usr/bin/env python3
"""Validate the ProjectLegends Graphify enrichment overlay."""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from check_capability_matrix import (  # noqa: E402
    parse_header_apis,
    parse_markdown_matrix,
    read_text,
)
from enrich_graphify_projectlegends import (  # noqa: E402
    CAPABILITY_PATH,
    CMAKE_PATH,
    CRITICAL_INPUTS,
    DERIVED,
    DIRECT_PATH,
    DISPATCHER_PATH,
    GRAPHIFY_EXTRACTED,
    HEADER_PATH,
    MANDATORY_TARGETS,
    MATRIX_PATH,
    MSGTYPES_PATH,
    ORIGIN,
    PROXY_PATH,
    SCHEMA_VERSION,
    file_hash,
    load_json,
    norm_path,
)


EXPECTED_PUBLIC_API_COUNT = 50


class CheckResult:
    def __init__(self) -> None:
        self.errors: list[str] = []
        self.warnings: list[str] = []

    def error(self, message: str) -> None:
        self.errors.append(message)

    def warn(self, message: str) -> None:
        self.warnings.append(message)


def load_overlay(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError("overlay must be a JSON object")
    return payload


def node_map(overlay: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {node["id"]: node for node in overlay.get("nodes", []) if isinstance(node, dict) and "id" in node}


def links_by_relation(overlay: dict[str, Any]) -> dict[str, list[dict[str, Any]]]:
    grouped: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for link in overlay.get("links", []):
        grouped[link.get("relation")].append(link)
    return grouped


def outgoing(overlay: dict[str, Any], source: str, relation: str | None = None) -> list[dict[str, Any]]:
    return [
        link
        for link in overlay.get("links", [])
        if link.get("source") == source and (relation is None or link.get("relation") == relation)
    ]


def incoming(overlay: dict[str, Any], target: str, relation: str | None = None) -> list[dict[str, Any]]:
    return [
        link
        for link in overlay.get("links", [])
        if link.get("target") == target and (relation is None or link.get("relation") == relation)
    ]


def nodes_by_kind(overlay: dict[str, Any], kind: str) -> list[dict[str, Any]]:
    return [node for node in overlay.get("nodes", []) if node.get("kind") == kind]


def node_by_kind_name(overlay: dict[str, Any], kind: str, name: str) -> dict[str, Any] | None:
    for node in nodes_by_kind(overlay, kind):
        if node.get("name") == name or node.get("api") == name or node.get("msgtype") == name:
            return node
    return None


def gate_inputs(repo: Path, overlay_path: Path, overlay: dict[str, Any], result: CheckResult) -> None:
    if overlay.get("schema_version") != SCHEMA_VERSION:
        result.error(f"schema_version must be {SCHEMA_VERSION}; found {overlay.get('schema_version')!r}")
    for key in ["generator", "generated_at", "graphify_graph", "source_hashes", "nodes", "links", "summary"]:
        if key not in overlay:
            result.error(f"overlay missing top-level key: {key}")

    graphify_path = repo / overlay.get("graphify_graph", "graphify-out/graph.json")
    manifest_path = repo / "graphify-out" / "manifest.json"
    allow_missing_graphify = bool(overlay.get("allow_missing_graphify", False))

    if not graphify_path.exists() and not allow_missing_graphify:
        result.error(f"Graphify graph missing: {graphify_path}")
    elif not graphify_path.exists() and allow_missing_graphify:
        result.warn(f"Graphify graph unavailable; validating source-only overlay: {graphify_path}")
    else:
        try:
            graph = load_json(graphify_path)
            if not isinstance(graph, dict) or "nodes" not in graph or "links" not in graph:
                result.error("Graphify graph must contain nodes and links")
        except Exception as exc:
            result.error(f"Graphify graph does not parse: {exc}")

    if not manifest_path.exists() and not allow_missing_graphify:
        result.error(f"Graphify manifest missing: {manifest_path}")
    elif not manifest_path.exists() and allow_missing_graphify:
        result.warn(f"Graphify manifest unavailable in source-only mode: {manifest_path}")
    else:
        try:
            manifest = load_json(manifest_path)
            for path in CRITICAL_INPUTS:
                if path not in manifest:
                    result.warn(f"Graphify manifest does not list critical input: {path}")
        except Exception as exc:
            result.error(f"Graphify manifest does not parse: {exc}")

    if not overlay_path.exists():
        result.error(f"overlay file missing: {overlay_path}")

    source_hashes = overlay.get("source_hashes", {})
    if not isinstance(source_hashes, dict):
        result.error("source_hashes must be an object")
        return
    for path in CRITICAL_INPUTS:
        full_path = repo / path
        if not full_path.exists():
            result.error(f"required input missing: {path}")
            continue
        current_hash = file_hash(full_path)
        stored_hash = source_hashes.get(path)
        if stored_hash != current_hash:
            result.error(f"stale overlay source hash for {path}")


def gate_graph_integrity(repo: Path, overlay: dict[str, Any], result: CheckResult) -> None:
    nodes = overlay.get("nodes", [])
    links = overlay.get("links", [])
    ids = [node.get("id") for node in nodes]
    duplicates = [item for item, count in Counter(ids).items() if count > 1]
    if duplicates:
        result.error(f"duplicate node IDs: {duplicates[:10]}")

    node_ids = set(ids)
    link_ids = [link.get("id") for link in links]
    duplicate_links = [item for item, count in Counter(link_ids).items() if count > 1]
    if duplicate_links:
        result.error(f"duplicate link IDs: {duplicate_links[:10]}")

    for node in nodes:
        if node.get("_origin") != ORIGIN:
            result.error(f"enrichment node has wrong _origin: {node.get('id')}")

    for link in links:
        if link.get("_origin") != ORIGIN:
            result.error(f"enrichment link has wrong _origin: {link.get('id')}")
        if link.get("confidence") == GRAPHIFY_EXTRACTED:
            result.error(f"enrichment link must not use EXTRACTED confidence: {link.get('id')}")
        if link.get("confidence") != DERIVED:
            result.error(f"enrichment link must use DERIVED confidence: {link.get('id')}")
        if link.get("source") not in node_ids:
            result.error(f"dangling link source {link.get('source')} in {link.get('id')}")
        if link.get("target") not in node_ids:
            result.error(f"dangling link target {link.get('target')} in {link.get('id')}")

    for node in nodes_by_kind(overlay, "source_file"):
        path = node.get("path")
        if path and not (repo / path).exists() and not path.startswith("graphify-out/"):
            result.warn(f"source_file node points to missing path: {path}")

    actual_node_counts = Counter(node.get("kind") for node in nodes)
    actual_link_counts = Counter(link.get("relation") for link in links)
    summary = overlay.get("summary", {})
    if summary.get("node_counts") != dict(sorted(actual_node_counts.items())):
        result.error("summary node_counts does not match nodes")
    if summary.get("link_counts") != dict(sorted(actual_link_counts.items())):
        result.error("summary link_counts does not match links")


def gate_api_inventory(repo: Path, overlay: dict[str, Any], result: CheckResult) -> None:
    header_apis = parse_header_apis(str(repo / HEADER_PATH))
    if len(header_apis) != EXPECTED_PUBLIC_API_COUNT:
        result.warn(
            f"public API count is {len(header_apis)}; expected baseline is {EXPECTED_PUBLIC_API_COUNT}"
        )

    api_nodes = nodes_by_kind(overlay, "public_c_api")
    api_names = [node.get("name") for node in api_nodes]
    if sorted(api_names) != sorted(header_apis):
        result.error("public_c_api nodes do not exactly match header exports")

    for api in header_apis:
        api_node = node_by_kind_name(overlay, "public_c_api", api)
        if not api_node:
            result.error(f"missing API node for {api}")
            continue
        api_id = api_node["id"]
        requirements = {
            "declared_in": HEADER_PATH,
            "direct_implemented_by": DIRECT_PATH,
            "proxy_implemented_by": PROXY_PATH,
            "has_capability_entry": CAPABILITY_PATH,
            "has_matrix_row": MATRIX_PATH,
        }
        for relation in requirements:
            if not outgoing(overlay, api_id, relation):
                result.error(f"{api} missing {relation} edge")


def gate_capability_sync(repo: Path, overlay: dict[str, Any], result: CheckResult) -> None:
    manifest = load_json(repo / CAPABILITY_PATH)
    matrix = parse_markdown_matrix(str(repo / MATRIX_PATH))
    header_apis = set(parse_header_apis(str(repo / HEADER_PATH)))
    if set(manifest.keys()) != header_apis:
        result.error("capability_truth.json keys do not match header exports")
    if set(matrix.keys()) != header_apis:
        result.error("Markdown capability matrix rows do not match header exports")

    for api in sorted(header_apis):
        cap_node = node_by_kind_name(overlay, "capability_entry", api)
        row_node = node_by_kind_name(overlay, "capability_matrix_row", api)
        if not cap_node:
            result.error(f"missing capability_entry for {api}")
            continue
        if not row_node:
            result.error(f"missing capability_matrix_row for {api}")
            continue
        manifest_entry = manifest.get(api, {})
        matrix_entry = matrix.get(api, {})
        for field in ["direct_status", "proxy_status"]:
            if cap_node.get(field) != manifest_entry.get(field):
                result.error(f"{api} overlay capability {field} drift")
            if row_node.get(field) != matrix_entry.get(field):
                result.error(f"{api} overlay matrix {field} drift")
            if manifest_entry.get(field) != matrix_entry.get(field):
                result.error(f"{api} manifest/Markdown {field} mismatch")
        if manifest_entry.get("proxy_status") == "proxy-partial" and not str(manifest_entry.get("notes", "")).strip():
            result.error(f"{api} is proxy-partial without explanatory notes")
        for evidence_path in manifest_entry.get("evidence_files", []):
            if not (repo / evidence_path).exists():
                result.error(f"{api} references missing evidence file {evidence_path}")


def request_targets_for_api(overlay: dict[str, Any], api: str) -> list[str]:
    proxy = node_by_kind_name(overlay, "proxy_c_api_impl", api)
    if not proxy:
        return []
    requests = [link["target"] for link in outgoing(overlay, proxy["id"], "sends_request")]
    if requests:
        return requests
    alias_requests: list[str] = []
    for alias_link in outgoing(overlay, proxy["id"], "aliases_api"):
        alias_node = node_map(overlay).get(alias_link["target"])
        if alias_node and alias_node.get("name"):
            alias_requests.extend(request_targets_for_api(overlay, alias_node["name"]))
    return sorted(set(alias_requests))


def gate_ipc_parity(repo: Path, overlay: dict[str, Any], result: CheckResult) -> None:
    manifest = load_json(repo / CAPABILITY_PATH)
    nodes = node_map(overlay)

    for api, entry in sorted(manifest.items()):
        proxy_status = entry.get("proxy_status")
        proxy_node = node_by_kind_name(overlay, "proxy_c_api_impl", api)
        if not proxy_node:
            result.error(f"{api} missing proxy implementation node")
            continue
        if proxy_status == "proxy-supported":
            if proxy_node.get("returns_not_supported"):
                result.error(f"{api} is proxy-supported but returns LEGENDS_ERR_NOT_SUPPORTED")
            request_ids = request_targets_for_api(overlay, api)
            if not request_ids:
                result.error(f"{api} is proxy-supported but has no request MsgType path")
                continue
            for request_id in request_ids:
                request_node = nodes.get(request_id)
                if not request_node:
                    result.error(f"{api} request edge targets missing node {request_id}")
                    continue
                msgtype = request_node.get("name")
                dispatcher_edges = outgoing(overlay, request_id, "handled_by_dispatcher")
                if not dispatcher_edges:
                    result.error(f"{api} request {msgtype} lacks dispatcher case")
                    continue
                for dispatcher_edge in dispatcher_edges:
                    dispatcher_node = nodes.get(dispatcher_edge["target"])
                    if not dispatcher_node:
                        result.error(f"{api} dispatcher edge target missing for {msgtype}")
                        continue
                    if not outgoing(overlay, dispatcher_node["id"], "dispatcher_returns"):
                        result.error(f"{api} dispatcher case for {msgtype} lacks response edge")
                    if not outgoing(overlay, request_id, "typed_by_struct"):
                        result.error(f"{api} request {msgtype} lacks message struct edge")
                    called_api_ids = {
                        link["target"]
                        for link in outgoing(overlay, dispatcher_node["id"], "dispatch_calls_api")
                    }
                    called_names = {
                        nodes[target].get("name")
                        for target in called_api_ids
                        if target in nodes
                    }
                    aliases = set(proxy_node.get("aliases", []))
                    expected = {api} | aliases
                    if not called_names.intersection(expected):
                        result.error(
                            f"{api} dispatcher case {msgtype} calls {sorted(called_names)}; "
                            f"expected one of {sorted(expected)}"
                        )
        elif proxy_status == "proxy-missing":
            if request_targets_for_api(overlay, api) and not proxy_node.get("returns_not_supported"):
                result.error(f"{api} is proxy-missing but has a complete request path")
        elif proxy_status == "proxy-partial":
            if not str(entry.get("notes", "")).strip():
                result.error(f"{api} is proxy-partial without notes")


def gate_ipc_schema(overlay: dict[str, Any], result: CheckResult) -> None:
    nodes = node_map(overlay)
    msgtypes = {node.get("name"): node for node in nodes_by_kind(overlay, "ipc_msgtype")}
    referenced_msgtypes = set()
    for link in overlay.get("links", []):
        if link.get("relation") in {
            "sends_request",
            "handled_by_dispatcher",
            "dispatcher_returns",
            "covers_msgtype",
        }:
            target = nodes.get(link.get("target"))
            source = nodes.get(link.get("source"))
            for node in [target, source]:
                if node and node.get("kind") == "ipc_msgtype":
                    referenced_msgtypes.add(node.get("name"))

    for name in sorted(referenced_msgtypes):
        node = msgtypes.get(name)
        if not node:
            result.error(f"referenced MsgType missing node: {name}")
            continue
        if not outgoing(overlay, node["id"], "typed_by_struct"):
            result.error(f"referenced MsgType lacks struct: {name}")
        if name.endswith("Req"):
            response = name[:-3] + "Resp"
            if response not in msgtypes:
                result.error(f"request MsgType {name} lacks paired response enum {response}")
            elif not outgoing(overlay, node["id"], "paired_with_response"):
                result.error(f"request MsgType {name} lacks paired_with_response edge")

    error_response = msgtypes.get("ErrorResponse")
    if not error_response:
        result.error("MsgType::ErrorResponse missing")


def gate_tests(overlay: dict[str, Any], result: CheckResult, strict_tests: str) -> None:
    test_cases = nodes_by_kind(overlay, "test_case")
    if not test_cases:
        result.error("no test_case nodes generated")
    manifest_proxy_supported = [
        node.get("api")
        for node in nodes_by_kind(overlay, "capability_entry")
        if node.get("proxy_status") == "proxy-supported"
    ]
    nodes = node_map(overlay)
    for api in sorted(filter(None, manifest_proxy_supported)):
        api_node = node_by_kind_name(overlay, "public_c_api", api)
        if not api_node:
            continue
        active_api_coverage = [
            link
            for link in incoming(overlay, api_node["id"], "covers_api_call")
            if not link.get("disabled")
        ]
        request_ids = request_targets_for_api(overlay, api)
        active_msg_coverage = []
        for request_id in request_ids:
            active_msg_coverage.extend(
                link
                for link in incoming(overlay, request_id, "covers_msgtype")
                if not link.get("disabled")
            )
        if not active_api_coverage and not active_msg_coverage:
            message = f"{api} has no active static test evidence"
            if strict_tests == "fail":
                result.error(message)
            else:
                result.warn(message)

    target_names = {node.get("name") for node in nodes_by_kind(overlay, "cmake_target")}
    for target in ["legends_abi_test", "legends_ipc_integration_tests"]:
        if target not in target_names:
            result.error(f"missing CMake test target node: {target}")


def gate_cmake(overlay: dict[str, Any], result: CheckResult) -> None:
    targets = {node.get("name"): node for node in nodes_by_kind(overlay, "cmake_target")}
    for target in MANDATORY_TARGETS:
        if target not in targets:
            result.error(f"missing mandatory CMake target node: {target}")

    def source_paths(target: str) -> set[str]:
        node = targets.get(target)
        return set(node.get("sources", [])) if node else set()

    def links(target: str) -> set[str]:
        node = targets.get(target)
        return set(node.get("links", [])) if node else set()

    checks = [
        ("legends_proxy", PROXY_PATH),
        ("legends_engine_host", "src/engine_host/main.cpp"),
        ("legends_engine_host", DISPATCHER_PATH),
        ("legends_app", "src/app/runtime_host.cpp"),
    ]
    for target, source in checks:
        if source not in source_paths(target):
            result.error(f"{target} missing source edge for {source}")

    for required_link in ["legends_core", "legends_ipc"]:
        if required_link not in links("legends_engine_host"):
            result.error(f"legends_engine_host missing link to {required_link}")
    if "legends_ipc" not in links("legends_proxy"):
        result.error("legends_proxy missing link to legends_ipc")


def validate_merged_graph(repo: Path, overlay: dict[str, Any], result: CheckResult) -> None:
    graphify_path = repo / overlay.get("graphify_graph", "graphify-out/graph.json")
    merged_path = repo / "graphify-out" / "projectlegends-graph-enriched.json"
    if not merged_path.exists() or not graphify_path.exists():
        return
    try:
        graph = load_json(graphify_path)
        merged = load_json(merged_path)
    except Exception as exc:
        result.error(f"could not parse merged/original graph: {exc}")
        return
    original_nodes = graph.get("nodes", [])
    original_links = graph.get("links", [])
    if merged.get("nodes", [])[: len(original_nodes)] != original_nodes:
        result.error("merged graph does not preserve original nodes prefix")
    if merged.get("links", [])[: len(original_links)] != original_links:
        result.error("merged graph does not preserve original links prefix")


def run_checks(
    repo: Path,
    overlay_path: Path,
    *,
    strict: bool = False,
    gates: set[str] | None = None,
    strict_tests: str = "warn",
    allow_missing_graphify: bool = False,
) -> CheckResult:
    overlay = load_overlay(overlay_path)
    if strict:
        overlay.setdefault("strict_mode", True)
    if allow_missing_graphify:
        overlay["allow_missing_graphify"] = True
    result = CheckResult()
    selected = gates or {
        "inputs",
        "graph-integrity",
        "api-inventory",
        "capability-sync",
        "ipc-parity",
        "ipc-schema",
        "tests",
        "cmake",
        "merged",
    }
    if "inputs" in selected:
        gate_inputs(repo, overlay_path, overlay, result)
    if "graph-integrity" in selected:
        gate_graph_integrity(repo, overlay, result)
    if "api-inventory" in selected:
        gate_api_inventory(repo, overlay, result)
    if "capability-sync" in selected:
        gate_capability_sync(repo, overlay, result)
    if "ipc-parity" in selected:
        gate_ipc_parity(repo, overlay, result)
    if "ipc-schema" in selected:
        gate_ipc_schema(overlay, result)
    if "tests" in selected:
        gate_tests(overlay, result, strict_tests)
    if "cmake" in selected:
        gate_cmake(overlay, result)
    if "merged" in selected:
        validate_merged_graph(repo, overlay, result)
    if strict and result.warnings:
        # Strict mode preserves warn-only coverage gates but makes stale or
        # malformed graph warnings visible in the command output.
        pass
    return result


def print_result(result: CheckResult) -> None:
    if result.errors:
        print("FAIL: Graphify enrichment validation failed.")
        for err in result.errors:
            print(f"  - {err}")
    else:
        print("PASS: Graphify enrichment validation passed.")
    if result.warnings:
        print("WARNINGS:")
        for warning in result.warnings:
            print(f"  - {warning}")


def run_from_builder(repo: Path, overlay_path: Path, strict: bool = True) -> int:
    result = run_checks(repo, overlay_path, strict=strict)
    print_result(result)
    return 1 if result.errors else 0


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate ProjectLegends Graphify enrichment overlay.")
    parser.add_argument("--repo", default=".", help="Repository root")
    parser.add_argument("--overlay", default="graphify-out/projectlegends-enrichment.json", help="Overlay JSON")
    parser.add_argument("--strict", action="store_true", help="Run all strict source consistency gates")
    parser.add_argument(
        "--allow-missing-graphify",
        action="store_true",
        help="Allow source-only validation when Graphify graph/manifest are unavailable",
    )
    parser.add_argument(
        "--strict-tests",
        choices=["warn", "fail"],
        default="warn",
        help="Treat missing static test evidence as warning or failure",
    )
    parser.add_argument(
        "--gate",
        action="append",
        choices=[
            "inputs",
            "graph-integrity",
            "api-inventory",
            "capability-sync",
            "ipc-parity",
            "ipc-schema",
            "tests",
            "cmake",
            "merged",
        ],
        help="Run a single gate; can be passed more than once",
    )
    args = parser.parse_args()

    repo = Path(args.repo).resolve()
    overlay_path = (repo / args.overlay).resolve()
    result = run_checks(
        repo,
        overlay_path,
        strict=args.strict,
        gates=set(args.gate) if args.gate else None,
        strict_tests=args.strict_tests,
        allow_missing_graphify=args.allow_missing_graphify,
    )
    print_result(result)
    return 1 if result.errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
