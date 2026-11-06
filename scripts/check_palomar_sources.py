#!/usr/bin/env python3
"""Check the source-format requirements of a prepared Palomar publication tree."""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

from check import code_only

EXCLUDED_DIRECTORIES = {".git", ".lake"}
MAX_SOURCE_LINES = 10_000
MAX_CHALLENGE_LINES = 1_000
MAX_CHALLENGE_BYTES = 100 * 1024
MAX_REPOSITORY_BYTES = 500 * 1024 * 1024


def physical_lines(raw: bytes) -> int:
    return raw.count(b"\n") + int(bool(raw) and not raw.endswith(b"\n"))


def inspect_tree(root: Path) -> dict:
    root = root.resolve()
    files = [path for path in root.rglob("*")
             if (path.is_file() or path.is_symlink())
             and not EXCLUDED_DIRECTORIES.intersection(path.relative_to(root).parts)]
    issues = []
    sources = []
    for path in files:
        if path.suffix != ".lean":
            continue
        relative = str(path.relative_to(root))
        if path.is_symlink():
            issues.append(f"Lean source is a symbolic link: {relative}")
            continue
        raw = path.read_bytes()
        try:
            text = raw.decode("utf-8")
        except UnicodeDecodeError:
            issues.append(f"Source is not UTF-8: {relative}")
            continue
        lines = physical_lines(raw)
        sources.append({"file": relative, "physical_lines": lines, "bytes": len(raw)})
        if lines > MAX_SOURCE_LINES:
            issues.append(f"Source exceeds {MAX_SOURCE_LINES} physical lines: {relative}")
        if path.name != "lakefile.lean":
            try:
                masked = code_only(text)
            except ValueError as error:
                issues.append(f"Malformed source {relative}: {error}")
                continue
            if re.match(r"\s*module\b", masked) is None:
                issues.append(f"Source needs a module header: {relative}")
    config_path = root / "Palomar/comparator.json"
    if config_path.is_file():
        try:
            config = json.loads(config_path.read_text())
            modules = [config[key] for key in ("challenge_module", "solution_module")]
            module_pattern = r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
            if any(not isinstance(name, str) or re.fullmatch(module_pattern, name) is None
                   for name in modules):
                raise ValueError("Comparator module names must be safe dotted Lean names")
            challenge, solution = [root.joinpath(*name.split(".")).with_suffix(".lean")
                                   for name in modules]
            raw = challenge.read_bytes()
            if len(raw) > MAX_CHALLENGE_BYTES or physical_lines(raw) > MAX_CHALLENGE_LINES:
                issues.append("Challenge exceeds its size limit")
            forbidden = re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b|debug\.skipKernelTC",
                                  code_only(solution.read_text()))
            if forbidden:
                issues.append(f"Prohibited Solution token: {forbidden.group()}")
        except (ValueError, KeyError, OSError) as error:
            issues.append(f"Invalid Comparator sources: {error}")
    else:
        issues.append("Missing Palomar/comparator.json")
    total_bytes = sum(path.lstat().st_size for path in files)
    if total_bytes > MAX_REPOSITORY_BYTES:
        issues.append("Repository exceeds the 500 MiB source limit")
    return {"source_files": len(sources), "repository_bytes": total_bytes,
            "largest_sources": sorted(sources, key=lambda row: row["physical_lines"], reverse=True)[:10],
            "issues": issues}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path, help="Prepared publication directory")
    args = parser.parse_args()
    report = inspect_tree(args.root)
    print(json.dumps(report, indent=2))
    return bool(report["issues"])


if __name__ == "__main__":
    raise SystemExit(main())
