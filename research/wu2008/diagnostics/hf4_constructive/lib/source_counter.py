#!/usr/bin/env python3
"""Check the release source surface and the public theorem axiom reports."""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE_DIRS = ("Goldbach", "MathlibNt", "AnalyticNumberTheory", "PrimeNumberTheoremAnd")
ONE_TWO_EXPECTED = {
    "Goldbach.chen_theorem",
    "Goldbach.representation_lower_bound",
    "MathlibNt.ChensTheorem.chens_theorem_unconditional",
    "MathlibNt.ChensTheorem.chen_good_representations_lower_bound_unconditional",
}
ONE_NINE_EXPECTED = {
    "Goldbach.one_plus_one_nine",
    "Goldbach.one_plus_one_nine_real",
    "Goldbach.one_plus_one_nine_count",
    "Goldbach.one_plus_one_nine_lower_bound",
}
EXPECTED = ONE_TWO_EXPECTED | ONE_NINE_EXPECTED
PUBLIC_ROOTS = (
    "Goldbach", "Goldbach.Checks", "Goldbach.Blueprint", "MathlibNt", "AnalyticNumberTheory",
    "Goldbach.OnePlusOneNine", "Goldbach.OnePlusOneNineChecks", "Goldbach.All",
)
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def code_only(text: str, *, keep_strings: bool = False) -> str:
    """Mask nested comments and, by default, strings; preserve text offsets.

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
                if not keep_strings:
                    out[i] = " "
                i += 1
                if i < len(text):
                    if not keep_strings:
                        out[i] = " "
                    i += 1
                continue
            if text[i] == '"':
                string = False
            if not keep_strings and text[i] != "\n":
                out[i] = " "
            i += 1
            continue
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
            if keep_strings:
                i += 1
                continue
        else:
            i += 1
            continue
        if text[i] != "\n":
            out[i] = " "
        i += 1
    if depth or string:
        raise ValueError("unterminated comment or string")
    return "".join(out)


def count_code_lines(text: str) -> int:
    return sum(bool(line.strip()) for line in code_only(text, keep_strings=True).splitlines())


def source_files() -> list[Path]:
    files = list(ROOT.glob("*.lean"))
    for name in SOURCE_DIRS:
        files.extend((ROOT / name).rglob("*.lean"))
    return sorted(files)


def release_files() -> list[Path]:
    # A linked worktree's .git file is Git metadata, not a publication artifact.
    files = [p for p in ROOT.iterdir() if p.is_file() and p.name != ".git"]
    for name in (*SOURCE_DIRS, "docs", "scripts", ".github"):
        directory = ROOT / name
        if directory.exists():
            files.extend(p for p in directory.rglob("*")
                         if p.is_file() and "__pycache__" not in p.parts)
    files.extend(p for p in (ROOT / "docbuild").glob("*") if p.is_file())
    files.extend(p for p in (ROOT / "blueprint/src").glob("*")
                 if p.is_file() and p.suffix in {".tex", ".cfg", ".py"})
    requirements = ROOT / "blueprint/requirements.txt"
    if requirements.exists():
        files.append(requirements)
    return sorted(files)


def module_glob_matches(module: str, glob: str) -> bool:
    """Match Lake's exact, submodules (.+), and inclusive (.*) name globs."""
    if glob.endswith((".+", ".*")):
        prefix = glob[:-2]
        return module.startswith(prefix + ".") or (glob.endswith(".*") and module == prefix)
    if "*" in glob or "+" in glob:
        raise ValueError(f"unsupported library glob: {glob}")
    return module == glob


def default_library_modules(modules: set[str]) -> tuple[dict, set[str]]:
    """Read explicit default library globs; do not infer coverage from headlines."""
    config = tomllib.loads((ROOT / "lakefile.toml").read_text(encoding="utf-8"))
    libraries = {library["name"]: library for library in config["lean_lib"]}
    selected, covered = {}, set()
    for name in config["defaultTargets"]:
        if name not in libraries:
            raise ValueError(f"default target is not a configured Lean library: {name}")
        library = libraries[name]
        if library.get("srcDir", ".") != "." or config.get("srcDir", ".") != ".":
            raise ValueError("source coverage requires repository-root library source directories")
        globs = library.get("globs")
        if not isinstance(globs, list) or not globs or not all(isinstance(g, str) for g in globs):
            raise ValueError(f"explicit nonempty library globs required: {name}")
        selected[name] = globs
        for glob in globs:
            # Exact and inclusive globs require the named root module to exist.
            required = glob[:-2] if glob.endswith(".*") else glob
            if not glob.endswith(".+") and required not in modules:
                raise ValueError(f"missing library glob module: {required}")
            covered.update(module for module in modules if module_glob_matches(module, glob))
    return selected, covered


def import_closure(graph: dict[str, list[str]], roots) -> set[str]:
    seen, pending = set(), list(roots)
    while pending:
        module = pending.pop()
        if module in seen or module not in graph:
            continue
        seen.add(module)
        pending.extend(graph[module])
    return seen


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
        if re.search(r"\b_private\.", text):
            issues.append(f"compiler-internal declaration name: {relative}")
    own = set(SOURCE_DIRS)
    for module, imports in graph.items():
        for imported in imports:
            if imported.split(".")[0] in own and imported not in graph:
                issues.append(f"missing local module: {module} -> {imported}")
    roots = set(PUBLIC_ROOTS) & graph.keys()
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

    # Check every source component, including library-only audits and helpers.
    for module in graph:
        visit(module)
    closures = {root: import_closure(graph, [root]) for root in sorted(roots)}
    entrypoint_modules = import_closure(graph, roots)
    libraries, glob_modules = default_library_modules(set(graph))
    build_modules = import_closure(graph, glob_modules)
    uncovered = sorted(set(graph) - build_modules)
    if uncovered:
        issues.append(f"source modules outside default library build coverage: {uncovered}")
    result = {
        "source_modules": len(files),
        "reachable_modules": len(entrypoint_modules),
        "entrypoint_closures": {root: len(modules) for root, modules in closures.items()},
        "default_libraries": libraries,
        "default_library_glob_modules": len(glob_modules),
        "default_build_modules": len(build_modules),
        "library_only_modules": len(build_modules - entrypoint_modules),
        "issues": issues,
    }
    print(json.dumps(result, indent=2))
    if issues:
        raise RuntimeError("release source checks failed")
    return result


def check_axiom_output(text: str, expected: set[str] | None = None) -> None:
    expected = EXPECTED if expected is None else expected
    reports = re.findall(
        r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
        text, re.S)
    found = {}
    for name, axioms in reports:
        if name not in expected:
            continue
        if name in found:
            raise RuntimeError(f"duplicate axiom report for {name}")
        found[name] = {x.strip() for x in axioms.split(",") if x.strip()}
        extra = found[name] - STANDARD_AXIOMS
        if extra:
            raise RuntimeError(f"nonstandard axioms for {name}: {sorted(extra)}")
    absent = expected - found.keys()
    if absent:
        raise RuntimeError(f"missing axiom reports: {sorted(absent)}")
    print("All public theorem axiom reports use only the standard classical axioms.")


def lean_environment():
    env = os.environ.copy()
    for name in ("LEAN_PATH", "LEAN_SRC_PATH"):
        env.pop(name, None)
    return env


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--static-only", action="store_true")
    parser.add_argument("--one-two-only", action="store_true",
                        help="check only the independent 1+2 probe; still scan all release sources")
    parser.add_argument("--count-lines", action="store_true",
                        help="report nonblank Lean lines excluding comments, retaining strings")
    args = parser.parse_args()
    static_checks()
    if args.count_lines:
        counts = {name: 0 for name in (*SOURCE_DIRS, "root")}
        for path in source_files():
            relative = path.relative_to(ROOT)
            area = relative.parts[0] if len(relative.parts) > 1 else "root"
            counts[area] += count_code_lines(path.read_text(encoding="utf-8"))
        print(json.dumps({"lean_code_lines": counts, "total": sum(counts.values())}, indent=2))
    if not args.static_only:
        probes = [("Goldbach/Checks.lean", ONE_TWO_EXPECTED)]
        if not args.one_two_only:
            probes.append(("Goldbach/OnePlusOneNineChecks.lean", ONE_NINE_EXPECTED))
        outputs = []
        for path, expected in probes:
            result = subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", path],
                                    cwd=ROOT, env=lean_environment(), text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT)
            print(result.stdout, end="")
            if result.returncode:
                return result.returncode
            check_axiom_output(result.stdout, expected)
            outputs.append(result.stdout)
        if not args.one_two_only:
            # Also reject duplicate or nonstandard reports across probe boundaries.
            check_axiom_output("\n".join(outputs))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, RuntimeError) as error:
        print(f"CHECK FAILED: {error}", file=sys.stderr)
        sys.exit(1)
