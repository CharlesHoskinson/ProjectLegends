#!/usr/bin/env python3
"""ProjectLegends Graphify command interface."""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_graphify_enrichment  # noqa: E402
import enrich_graphify_projectlegends  # noqa: E402


DEFAULT_GRAPHIFY_EXE = Path(
    os.environ.get(
        "GRAPHIFY_EXE",
        r"C:\Users\charl\AppData\Roaming\Python\Python314\Scripts\graphify.exe",
    )
)
DEFAULT_GRAPH = Path("graphify-out/graph.json")
DEFAULT_OVERLAY = Path("graphify-out/projectlegends-enrichment.json")
DEFAULT_MERGED = Path("graphify-out/projectlegends-graph-enriched.json")
DEFAULT_REPORT = Path("docs/architecture/graphify-enrichment-report.md")


def repo_root(value: str) -> Path:
    return Path(value).resolve()


def run_command(args: list[str], cwd: Path) -> int:
    print("+ " + " ".join(args))
    completed = subprocess.run(args, cwd=str(cwd), check=False)
    return completed.returncode


def resolve_graphify_exe(path: Path) -> Path | None:
    if path.exists():
        return path
    found = shutil.which("graphify")
    return Path(found) if found else None


def command_update(args: argparse.Namespace) -> int:
    repo = repo_root(args.repo)
    graph_path = repo / args.graph
    overlay_path = repo / args.overlay
    merged_path = repo / args.merged
    report_path = repo / args.report

    source_only = args.source_only
    if not source_only and not args.skip_graphify:
        graphify_exe = resolve_graphify_exe(Path(args.graphify_exe))
        if not graphify_exe:
            print(
                "WARN: Graphify executable not found; falling back to source-only enrichment.",
                file=sys.stderr,
            )
            source_only = True
        else:
            rc = run_command([str(graphify_exe), "update", ".", "--no-cluster"], repo)
            if rc != 0:
                return rc

    overlay = enrich_graphify_projectlegends.build_overlay(
        repo,
        graph_path,
        allow_missing_graphify=source_only or args.allow_missing_graphify,
    )
    enrich_graphify_projectlegends.write_json(overlay_path, overlay)
    enrich_graphify_projectlegends.write_json(
        merged_path,
        enrich_graphify_projectlegends.merge_graph(graph_path, overlay),
    )
    enrich_graphify_projectlegends.write_report(report_path, overlay)

    print(
        "PASS: updated ProjectLegends Graphify interface. "
        f"{overlay['summary']['enrichment_nodes']} enrichment nodes; "
        f"{overlay['summary']['enrichment_links']} enrichment links."
    )
    if not args.no_check:
        result = check_graphify_enrichment.run_checks(
            repo,
            overlay_path,
            strict=True,
            strict_tests=args.strict_tests,
            allow_missing_graphify=source_only or args.allow_missing_graphify,
        )
        check_graphify_enrichment.print_result(result)
        return 1 if result.errors else 0
    return 0


def command_check(args: argparse.Namespace) -> int:
    repo = repo_root(args.repo)
    result = check_graphify_enrichment.run_checks(
        repo,
        repo / args.overlay,
        strict=args.strict,
        strict_tests=args.strict_tests,
        allow_missing_graphify=args.allow_missing_graphify,
    )
    check_graphify_enrichment.print_result(result)
    return 1 if result.errors else 0


def load_overlay(repo: Path, overlay: str) -> dict[str, Any]:
    return json.loads((repo / overlay).read_text(encoding="utf-8"))


def command_summary(args: argparse.Namespace) -> int:
    repo = repo_root(args.repo)
    overlay = load_overlay(repo, args.overlay)
    summary = overlay.get("summary", {})
    print("ProjectLegends Graphify Enrichment")
    print(f"  Public APIs:       {summary.get('public_api_count')}")
    print(f"  Dispatcher cases:  {summary.get('dispatcher_case_count')}")
    print(f"  Test cases:        {summary.get('test_case_count')}")
    print(f"  CMake targets:     {summary.get('cmake_target_count')}")
    print(f"  Enrichment nodes:  {summary.get('enrichment_nodes')}")
    print(f"  Enrichment links:  {summary.get('enrichment_links')}")
    print(f"  Proxy statuses:    {summary.get('proxy_status_counts')}")
    print(f"  Direct statuses:   {summary.get('direct_status_counts')}")
    return 0


def nodes_by_id(overlay: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {node["id"]: node for node in overlay.get("nodes", [])}


def outgoing(overlay: dict[str, Any], source: str, relation: str) -> list[dict[str, Any]]:
    return [
        link
        for link in overlay.get("links", [])
        if link.get("source") == source and link.get("relation") == relation
    ]


def command_explain_api(args: argparse.Namespace) -> int:
    repo = repo_root(args.repo)
    overlay = load_overlay(repo, args.overlay)
    nodes = nodes_by_id(overlay)
    api = args.api
    api_id = f"pl__api__{api}"
    api_node = nodes.get(api_id)
    if not api_node:
        print(f"FAIL: API not found in enrichment overlay: {api}", file=sys.stderr)
        return 1

    print(api)
    print(f"  Declaration: {api_node.get('source_file')}:{api_node.get('source_location')}")
    print(f"  Signature:   {api_node.get('signature')}")

    for relation, label in [
        ("has_capability_entry", "Capability"),
        ("has_matrix_row", "Matrix"),
        ("direct_implemented_by", "Direct"),
        ("proxy_implemented_by", "Proxy"),
    ]:
        for link in outgoing(overlay, api_id, relation):
            target = nodes.get(link["target"], {})
            print(
                f"  {label}: {target.get('source_file')}:{target.get('source_location')} "
                f"{target.get('direct_status', '')} {target.get('proxy_status', '')}".rstrip()
            )

    proxy_links = outgoing(overlay, api_id, "proxy_implemented_by")
    for proxy_link in proxy_links:
        proxy = nodes.get(proxy_link["target"], {})
        requests = outgoing(overlay, proxy["id"], "sends_request")
        aliases = outgoing(overlay, proxy["id"], "aliases_api")
        if proxy.get("returns_not_supported"):
            print("  Proxy behavior: returns LEGENDS_ERR_NOT_SUPPORTED")
        for alias in aliases:
            target = nodes.get(alias["target"], {})
            print(f"  Proxy alias: {target.get('name')}")
        for request in requests:
            request_node = nodes.get(request["target"], {})
            print(f"  Request: {request_node.get('name')}")
            for handled in outgoing(overlay, request_node["id"], "handled_by_dispatcher"):
                dispatcher = nodes.get(handled["target"], {})
                print(
                    f"    Dispatcher: {dispatcher.get('source_file')}:"
                    f"{dispatcher.get('source_location')}"
                )
                for response in outgoing(overlay, dispatcher["id"], "dispatcher_returns"):
                    response_node = nodes.get(response["target"], {})
                    print(f"    Response:   {response_node.get('name')}")

    tests = [
        nodes.get(link["source"], {})
        for link in overlay.get("links", [])
        if link.get("target") == api_id and link.get("relation") == "covers_api_call"
    ]
    active_tests = [test for test in tests if not test.get("disabled")]
    print(f"  Active API test evidence: {len(active_tests)}")
    for test in active_tests[:10]:
        print(f"    {test.get('label')} ({test.get('source_file')}:{test.get('source_location')})")
    if len(active_tests) > 10:
        print(f"    ... {len(active_tests) - 10} more")
    return 0


def command_commands(_: argparse.Namespace) -> int:
    print("Local full refresh:")
    print("  python scripts/graphify_projectlegends.py update --repo .")
    print("")
    print("Source-only CI refresh:")
    print("  python scripts/graphify_projectlegends.py update --repo . --source-only")
    print("")
    print("Strict check:")
    print("  python scripts/graphify_projectlegends.py check --repo . --strict --strict-tests fail")
    print("")
    print("Summary:")
    print("  python scripts/graphify_projectlegends.py summary --repo .")
    print("")
    print("Explain one API:")
    print("  python scripts/graphify_projectlegends.py explain-api legends_mount_drive --repo .")
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="ProjectLegends Graphify interface")
    subparsers = parser.add_subparsers(dest="command", required=True)

    update = subparsers.add_parser("update", help="Refresh Graphify and ProjectLegends enrichment")
    update.add_argument("--repo", default=".")
    update.add_argument("--graph", default=str(DEFAULT_GRAPH))
    update.add_argument("--overlay", default=str(DEFAULT_OVERLAY))
    update.add_argument("--merged", default=str(DEFAULT_MERGED))
    update.add_argument("--report", default=str(DEFAULT_REPORT))
    update.add_argument("--graphify-exe", default=str(DEFAULT_GRAPHIFY_EXE))
    update.add_argument("--skip-graphify", action="store_true")
    update.add_argument("--source-only", action="store_true")
    update.add_argument("--allow-missing-graphify", action="store_true")
    update.add_argument("--no-check", action="store_true")
    update.add_argument("--strict-tests", choices=["warn", "fail"], default="fail")
    update.set_defaults(func=command_update)

    check = subparsers.add_parser("check", help="Validate the enrichment overlay")
    check.add_argument("--repo", default=".")
    check.add_argument("--overlay", default=str(DEFAULT_OVERLAY))
    check.add_argument("--strict", action="store_true")
    check.add_argument("--strict-tests", choices=["warn", "fail"], default="fail")
    check.add_argument("--allow-missing-graphify", action="store_true")
    check.set_defaults(func=command_check)

    summary = subparsers.add_parser("summary", help="Print enrichment summary")
    summary.add_argument("--repo", default=".")
    summary.add_argument("--overlay", default=str(DEFAULT_OVERLAY))
    summary.set_defaults(func=command_summary)

    explain = subparsers.add_parser("explain-api", help="Explain a public legends_* API path")
    explain.add_argument("api")
    explain.add_argument("--repo", default=".")
    explain.add_argument("--overlay", default=str(DEFAULT_OVERLAY))
    explain.set_defaults(func=command_explain_api)

    commands = subparsers.add_parser("commands", help="Print common Graphify commands")
    commands.set_defaults(func=command_commands)
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
