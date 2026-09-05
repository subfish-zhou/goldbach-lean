#!/usr/bin/env python3
"""Check the release source surface and the public theorem axiom reports."""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE_DIRS = ("Goldbach", "MathlibNt", "AnalyticNumberTheory", "PrimeNumberTheoremAnd")
EXPECTED = {
    "Goldbach.chen_theorem",
    "Goldbach.representation_lower_bound",
    "MathlibNt.ChensTheorem.chens_theorem_unconditional",
    "MathlibNt.ChensTheorem.chen_good_representations_lower_bound_unconditional",
}
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def code_only(text: str) -> str:
    """Mask nested comments and strings, preserving offsets and line breaks.

    This is a lexical check, not a Lean parser or a kernel verifier.
    """
    out = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                out[i:i + 2] = "  "
                depth += 1
                i += 2
                continue
            if text.startswith("-/", i):
                out[i:i + 2] = "  "
                depth -= 1
                i += 2
                continue
        elif string:
            if text[i] == "\\":
                out[i] = " "
                i += 1
                if i < len(text):
                    out[i] = " "
                    i += 1
                continue
            if text[i] == '"':
                string = False
        elif text.startswith("/-", i):
            out[i:i + 2] = "  "
            depth = 1
            i += 2
            continue
        elif text.startswith("--", i):
            j = text.find("\n", i)
            j = len(text) if j < 0 else j
            out[i:j] = " " * (j - i)
            i = j
            continue
        elif text[i] == '"':
            string = True
        else:
            i += 1
            continue
        if text[i] != "\n":
            out[i] = " "
        i += 1
    if depth or string:
        raise ValueError("unterminated comment or string")
    return "".join(out)


def source_files() -> list[Path]:
    files = list(ROOT.glob("*.lean"))
    for name in SOURCE_DIRS:
        files.extend((ROOT / name).rglob("*.lean"))
    return sorted(files)


def release_files() -> list[Path]:
    files = [p for p in ROOT.iterdir() if p.is_file()]
    for name in (*SOURCE_DIRS, "docs", "scripts", ".github"):
        directory = ROOT / name
        if directory.exists():
            files.extend(p for p in directory.rglob("*")
                         if p.is_file() and "__pycache__" not in p.parts)
    return sorted(files)


def static_checks() -> dict:
    issues = []
    files = source_files()
    graph = {}
    words = re.compile(r"\b(sorry|admit|axiom|native_decide|unsafe)\b|debug\.skipKernelTC")
    for path in files:
        text = path.read_text(encoding="utf-8")
        if text.startswith("/-\n!"):
            issues.append(f"malformed module header: {path.relative_to(ROOT)}")
        masked = code_only(text)
        module = str(path.relative_to(ROOT).with_suffix("")).replace("/", ".")
        imports = []
        for line in masked.splitlines():
            match = re.match(r"\s*(?:(?:public|meta)\s+)*import\s+(.+)", line)
            if match:
                imports.extend(match.group(1).split())
        graph[module] = imports
        for match in words.finditer(masked):
            line = masked.count("\n", 0, match.start()) + 1
            issues.append(f"{path.relative_to(ROOT)}:{line}: prohibited token {match.group()}")
    for path in release_files():
        relative = str(path.relative_to(ROOT))
        if path.is_symlink():
            issues.append(f"symlink in release surface: {relative}")
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            issues.append(f"unexpected binary release file: {relative}")
            continue
        if re.search(r"[\u3400-\u9fff\uf900-\ufaff\U00020000-\U0003134f]", text + relative):
            issues.append(f"untranslated CJK text: {relative}")
        if re.search(r"/(?:home|mnt|Users)/|comms/(?:inbox|outbox)/", text):
            issues.append(f"private machine path: {relative}")
    own = set(SOURCE_DIRS)
    for module, imports in graph.items():
        for imported in imports:
            if imported.split(".")[0] in own and imported not in graph:
                issues.append(f"missing local module: {module} -> {imported}")
    roots = {"Goldbach", "Goldbach.Checks", "MathlibNt", "AnalyticNumberTheory"} & graph.keys()
    seen, active = set(), set()

    def visit(module):
        if module in active:
            issues.append(f"import cycle at {module}")
            return
        if module in seen or module not in graph:
            return
        active.add(module)
        for dep in graph[module]:
            visit(dep)
        active.remove(module)
        seen.add(module)

    for module in roots:
        visit(module)
    unreachable = sorted(set(graph) - seen)
    if unreachable:
        issues.append(f"source modules outside all public/check roots: {unreachable}")
    result = {"source_modules": len(files), "reachable_modules": len(seen), "issues": issues}
    print(json.dumps(result, indent=2))
    if issues:
        raise RuntimeError("release source checks failed")
    return result


def check_axiom_output(text: str) -> None:
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.S)
    found = {}
    for name, axioms in reports:
        if name not in EXPECTED:
            continue
        if name in found:
            raise RuntimeError(f"duplicate axiom report for {name}")
        found[name] = {x.strip() for x in axioms.split(",") if x.strip()}
        extra = found[name] - STANDARD_AXIOMS
        if extra:
            raise RuntimeError(f"nonstandard axioms for {name}: {sorted(extra)}")
    absent = EXPECTED - found.keys()
    if absent:
        raise RuntimeError(f"missing axiom reports: {sorted(absent)}")
    print("All public theorem axiom reports use only the standard classical axioms.")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--static-only", action="store_true")
    args = parser.parse_args()
    static_checks()
    if not args.static_only:
        result = subprocess.run(["lake", "env", "lean", "Goldbach/Checks.lean"],
                                cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        print(result.stdout, end="")
        if result.returncode:
            return result.returncode
        check_axiom_output(result.stdout)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, RuntimeError) as error:
        print(f"CHECK FAILED: {error}", file=sys.stderr)
        sys.exit(1)
