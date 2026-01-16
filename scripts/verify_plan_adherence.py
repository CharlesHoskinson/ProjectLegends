#!/usr/bin/env python3
"""
verify_plan_adherence.py - Logic Gate verification script

Verifies that C++ implementation matches the structured plan schema.
Uses regex-based AST-like parsing (no libclang dependency).

Usage:
    python verify_plan_adherence.py --schema schemas/phase-03-dma.json

Part of the Supervisor-Worker architecture for Project Legends.
"""

import argparse
import json
import re
import sys
from pathlib import Path
from dataclasses import dataclass
from typing import Optional


@dataclass
class CheckResult:
    """Result of a single verification check."""
    name: str
    passed: bool
    message: str
    file: Optional[str] = None
    line: Optional[int] = None


class PlanVerifier:
    """Verifies C++ code against a plan schema."""

    def __init__(self, schema_path: Path, project_root: Path):
        self.schema_path = schema_path
        self.project_root = project_root
        self.schema = self._load_schema()
        self.results: list[CheckResult] = []

    def _load_schema(self) -> dict:
        """Load and parse the JSON schema."""
        with open(self.schema_path, 'r') as f:
            return json.load(f)

    def _read_file(self, relative_path: str) -> Optional[str]:
        """Read a file relative to project root."""
        full_path = self.project_root / relative_path
        if not full_path.exists():
            return None
        with open(full_path, 'r', encoding='utf-8', errors='replace') as f:
            return f.read()

    def _find_struct(self, content: str, name: str) -> Optional[re.Match]:
        """Find a struct or class definition in C++ content."""
        # Match: struct/class Name { ... } or struct/class Name : Base { ... }
        pattern = rf'\b(?:struct|class)\s+{name}\s*(?::\s*[^{{]+)?\{{'
        return re.search(pattern, content)

    def _find_member(self, content: str, struct_name: str, member_name: str) -> Optional[re.Match]:
        """Find a member within a struct."""
        # First find the struct
        struct_match = self._find_struct(content, struct_name)
        if not struct_match:
            return None

        # Find the struct body (simplistic - doesn't handle nested braces perfectly)
        start = struct_match.end()
        brace_count = 1
        end = start
        while end < len(content) and brace_count > 0:
            if content[end] == '{':
                brace_count += 1
            elif content[end] == '}':
                brace_count -= 1
            end += 1

        struct_body = content[start:end]

        # Look for the member (variable or method)
        # Match: type member_name; or type member_name(...) or type member_name[...]
        pattern = rf'\b{member_name}\s*[\[\(;]'
        return re.search(pattern, struct_body)

    def _find_global(self, content: str, pattern: str) -> Optional[re.Match]:
        """Find a global variable matching pattern."""
        return re.search(pattern, content)

    def _check_structures(self) -> None:
        """Verify all required structures exist with their members."""
        structures = self.schema.get('structures', {})

        for struct_name, struct_spec in structures.items():
            file_path = struct_spec.get('file', '')
            content = self._read_file(file_path)

            if content is None:
                self.results.append(CheckResult(
                    name=f"{struct_name} struct",
                    passed=False,
                    message=f"File not found: {file_path}",
                    file=file_path
                ))
                continue

            # Check struct exists
            struct_match = self._find_struct(content, struct_name)
            if struct_match:
                line_num = content[:struct_match.start()].count('\n') + 1
                self.results.append(CheckResult(
                    name=f"{struct_name} struct",
                    passed=True,
                    message=f"Found in {file_path}",
                    file=file_path,
                    line=line_num
                ))
            else:
                self.results.append(CheckResult(
                    name=f"{struct_name} struct",
                    passed=False,
                    message=f"Not found in {file_path}",
                    file=file_path
                ))
                continue

            # Check members
            members = struct_spec.get('members', {})
            for member_name, member_spec in members.items():
                member_match = self._find_member(content, struct_name, member_name)
                if member_match:
                    self.results.append(CheckResult(
                        name=f"{struct_name}.{member_name}",
                        passed=True,
                        message=f"Member found",
                        file=file_path
                    ))
                else:
                    self.results.append(CheckResult(
                        name=f"{struct_name}.{member_name}",
                        passed=False,
                        message=f"Member not found in {struct_name}",
                        file=file_path
                    ))

    def _check_context_additions(self) -> None:
        """Verify context has required new members."""
        additions = self.schema.get('context_additions', {})

        for context_name, context_spec in additions.items():
            file_path = context_spec.get('file', '')
            content = self._read_file(file_path)

            if content is None:
                continue

            new_members = context_spec.get('new_members', {})
            for member_name, member_spec in new_members.items():
                member_match = self._find_member(content, context_name, member_name)
                if member_match:
                    self.results.append(CheckResult(
                        name=f"{context_name}.{member_name}",
                        passed=True,
                        message="Context member found",
                        file=file_path
                    ))
                else:
                    self.results.append(CheckResult(
                        name=f"{context_name}.{member_name}",
                        passed=False,
                        message=f"Context member not found",
                        file=file_path
                    ))

    def _check_globals_removed(self) -> None:
        """Verify global variables have been removed."""
        globals_to_remove = self.schema.get('globals_to_remove', [])

        for global_spec in globals_to_remove:
            file_path = global_spec.get('file', '')
            pattern = global_spec.get('line_pattern', '')
            name = global_spec.get('name', 'unnamed')

            content = self._read_file(file_path)
            if content is None:
                self.results.append(CheckResult(
                    name=f"Global {name} removed",
                    passed=False,
                    message=f"File not found: {file_path}",
                    file=file_path
                ))
                continue

            # Check if global still exists
            global_match = self._find_global(content, pattern)
            if global_match:
                line_num = content[:global_match.start()].count('\n') + 1
                self.results.append(CheckResult(
                    name=f"Global {name} removed",
                    passed=False,
                    message=f"Global still exists at line {line_num}",
                    file=file_path,
                    line=line_num
                ))
            else:
                self.results.append(CheckResult(
                    name=f"Global {name} removed",
                    passed=True,
                    message="Global successfully removed",
                    file=file_path
                ))

    def _check_compat_shims(self) -> None:
        """Verify compatibility shim file exists with required functions."""
        compat = self.schema.get('compat_shims', {})
        file_path = compat.get('file', '')

        if not file_path:
            return

        content = self._read_file(file_path)
        if content is None:
            self.results.append(CheckResult(
                name="Compat shim file",
                passed=False,
                message=f"File not found: {file_path}",
                file=file_path
            ))
            return

        self.results.append(CheckResult(
            name="Compat shim file",
            passed=True,
            message=f"File exists: {file_path}",
            file=file_path
        ))

        functions = compat.get('functions', [])
        for func in functions:
            if isinstance(func, dict):
                func_name = func.get('name', '')
            else:
                func_name = func

            if re.search(rf'\b{func_name}\s*\(', content):
                self.results.append(CheckResult(
                    name=f"Compat shim: {func_name}",
                    passed=True,
                    message="Function found",
                    file=file_path
                ))
            else:
                self.results.append(CheckResult(
                    name=f"Compat shim: {func_name}",
                    passed=False,
                    message="Function not found",
                    file=file_path
                ))

    def _check_state_hash(self) -> None:
        """Verify state hash includes required call."""
        hash_spec = self.schema.get('state_hash_additions', {})
        file_path = hash_spec.get('file', '')
        required_call = hash_spec.get('required_call', '')

        if not file_path or not required_call:
            return

        content = self._read_file(file_path)
        if content is None:
            self.results.append(CheckResult(
                name="State hash integration",
                passed=False,
                message=f"File not found: {file_path}",
                file=file_path
            ))
            return

        # Escape special regex characters but allow some flexibility
        pattern = required_call.replace('.', r'\.').replace('->', r'->')
        pattern = pattern.replace('(', r'\(').replace(')', r'\)')

        if re.search(pattern, content):
            self.results.append(CheckResult(
                name="State hash integration",
                passed=True,
                message=f"Found: {required_call}",
                file=file_path
            ))
        else:
            self.results.append(CheckResult(
                name="State hash integration",
                passed=False,
                message=f"Not found: {required_call}",
                file=file_path
            ))

    def verify(self) -> bool:
        """Run all verification checks. Returns True if all pass."""
        print(f"\n{'='*60}")
        print(f"Logic Gate Verification: {self.schema.get('phase_name', 'Unknown')}")
        print(f"Schema: {self.schema_path.name}")
        print(f"{'='*60}\n")

        self._check_structures()
        self._check_context_additions()
        self._check_globals_removed()
        self._check_compat_shims()
        self._check_state_hash()

        # Print results
        passed = 0
        failed = 0

        for result in self.results:
            # Use ASCII-safe characters for Windows compatibility
            status = "[PASS]" if result.passed else "[FAIL]"
            color = "\033[92m" if result.passed else "\033[91m"
            reset = "\033[0m"

            location = ""
            if result.file:
                location = f" [{result.file}"
                if result.line:
                    location += f":{result.line}"
                location += "]"

            print(f"{color}{status}{reset} {result.name}: {result.message}{location}")

            if result.passed:
                passed += 1
            else:
                failed += 1

        print(f"\n{'-'*60}")
        print(f"Logic Gate: {'PASS' if failed == 0 else 'FAIL'} ({passed}/{passed+failed} checks)")
        print(f"{'-'*60}\n")

        return failed == 0


def main():
    parser = argparse.ArgumentParser(
        description="Verify C++ implementation against plan schema (Logic Gate)"
    )
    parser.add_argument(
        '--schema', '-s',
        type=Path,
        required=True,
        help="Path to JSON schema file"
    )
    parser.add_argument(
        '--project-root', '-p',
        type=Path,
        default=Path(__file__).parent.parent,
        help="Project root directory (default: parent of scripts/)"
    )

    args = parser.parse_args()

    if not args.schema.exists():
        print(f"Error: Schema file not found: {args.schema}", file=sys.stderr)
        sys.exit(1)

    verifier = PlanVerifier(args.schema, args.project_root)
    success = verifier.verify()

    sys.exit(0 if success else 1)


if __name__ == '__main__':
    main()
