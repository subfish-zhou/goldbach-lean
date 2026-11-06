#!/usr/bin/env python3
"""Prepare a complete Chen/Li-Liu publication from the upgraded main libraries."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import tempfile
from pathlib import Path

from check import ROOT, source_files
from check_palomar_sources import inspect_tree

CONFIGURATION = ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "LICENSE")
VERIFICATION_SCRIPTS = ("check.py", "test_check.py", "check_palomar_sources.py",
                        "test_check_palomar_sources.py")


def prepare_publication(output: Path, authors: list[str]) -> dict:
    output = output.resolve()
    if output.exists():
        raise FileExistsError(f"Choose a new output directory: {output}")
    if not authors or any(not author.strip() for author in authors):
        raise ValueError("Provide a public author name or identifier")
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=".palomar-", dir=output.parent) as temporary:
        stage = Path(temporary) / "publication"
        stage.mkdir()
        inputs = source_files() + [ROOT / name for name in CONFIGURATION]
        inputs += [ROOT / "scripts" / name for name in VERIFICATION_SCRIPTS]
        inputs += [ROOT / "Palomar" / name for name in
                   ("Challenge.lean", "Solution.lean", "comparator.json")]
        manifest = {}
        for source in inputs:
            relative = source.relative_to(ROOT)
            target = stage / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)
            digest = hashlib.sha256(source.read_bytes()).hexdigest()
            assert hashlib.sha256(target.read_bytes()).hexdigest() == digest
            manifest[str(relative)] = digest
        shutil.copyfile(ROOT / "Palomar/README.md", stage / "README.md")
        metadata = (ROOT / "Palomar/formalization.yaml").read_text()
        identities = json.dumps(authors, ensure_ascii=False)
        metadata, count = re.subn(r"^  authors: .*$", lambda _: "  authors: " + identities,
                                  metadata, count=1, flags=re.M)
        assert count == 1
        metadata, count = re.subn(r"^  responsible_maintainers: .*$",
                                  lambda _: "  responsible_maintainers: " + identities,
                                  metadata, count=1, flags=re.M)
        assert count == 1
        (stage / "formalization.yaml").write_text(metadata)
        for relative in ("README.md", "formalization.yaml"):
            manifest[relative] = hashlib.sha256((stage / relative).read_bytes()).hexdigest()
        (stage / ".gitignore").write_text(".lake/\n.build/\n__pycache__/\n*.pyc\n")
        (stage / "Palomar/source-manifest.json").write_text(
            json.dumps({"files": manifest, "scope": "Complete upgraded main proof development"},
                       indent=2) + "\n")
        report = inspect_tree(stage)
        if report["issues"]:
            raise ValueError("Publication source checks failed: " + "; ".join(report["issues"]))
        os.replace(stage, output)
    return {"output": str(output), "main_modules": len(source_files()),
            "copied_input_files": len(manifest), "source_check": report,
            "metadata_review": "Maintainer review required before registration"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--author", required=True, action="append",
                        help="Public human author name or identifier; repeat for coauthors")
    args = parser.parse_args()
    try:
        report = prepare_publication(args.output, args.author)
    except (FileExistsError, ValueError) as error:
        parser.error(str(error))
    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
