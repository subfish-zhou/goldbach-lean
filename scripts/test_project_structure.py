#!/usr/bin/env python3
"""Unit and full-export acceptance tests for the project structure explorer."""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch
import sys
sys.dont_write_bytecode = True

EXPORT = None
TEST_ROOT = None

SPEC = importlib.util.spec_from_file_location("structure_builder", Path(__file__).with_name("build_project_structure.py"))
assert SPEC is not None and SPEC.loader is not None
builder = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(builder)


class StructureTests(unittest.TestCase):
    def test_scc_preserves_cycles_and_self_edges(self):
        graph = {"a": {"b"}, "b": {"a", "c"}, "c": set(), "d": {"d"}}
        self.assertEqual({frozenset(c) for c in builder.cyclic_components(graph)},
                         {frozenset(["a", "b"]), frozenset(["d"])})

    def test_owner_is_census_not_namespace(self):
        owners = {"OtherNamespace.fact": [7, 9]}
        extras = {"Generated.helper": [8]}
        self.assertEqual(builder.classify("OtherNamespace.fact", owners, extras),
                         {"scope": "local", "modules": [7, 9]})
        self.assertEqual(builder.classify("Goldbach.unknown", owners, extras),
                         {"scope": "outside-local-census", "modules": []})
        self.assertEqual(builder.classify("Generated.helper", owners, extras),
                         {"scope": "local-extra", "modules": [8]})

    def test_census_mismatch_and_conflicting_parts_fail(self):
        row = {"name": "a", "kind": "axiom", "hasValue": False,
               "type": [], "value": [], "recursorRHS": []}
        with self.assertRaises(ValueError):
            builder.normalize_declarations({"constNames": ["b"], "declarations": [row]})
        bad = dict(row, kind="theorem")
        with self.assertRaises(ValueError):
            builder.normalize_declarations({"constNames": ["a", "a"], "declarations": [row, bad]})
        self.assertEqual(builder.normalize_declarations(
            {"constNames": ["a", "a"], "declarations": [row, row]}), [row])

    def test_private_body_replaces_exported_axiom_shell(self):
        shell = {"name": "a", "kind": "axiom", "hasValue": False,
                 "type": ["Nat"], "value": [], "recursorRHS": []}
        body = dict(shell, kind="theorem", hasValue=True, value=["Nat.zero"])
        for rows in ([shell, body], [body, shell]):
            self.assertEqual(builder.normalize_declarations(
                {"constNames": ["a", "a"], "declarations": rows}), [body])
        with self.assertRaises(ValueError):
            builder.normalize_declarations({"constNames": ["a", "a"],
                "declarations": [shell, dict(body, type=["Int"])]})

    def test_missing_object_fails_before_output(self):
        with tempfile.TemporaryDirectory(dir=TEST_ROOT) as tmp:
            output = Path(tmp) / "new"
            with patch.object(builder, "modules_in", return_value=["Goldbach.MissingObject"]), \
                 patch.object(builder, "revision_checked", return_value="0" * 40):
                with self.assertRaisesRegex(ValueError, "Missing compiled modules"):
                    builder.build_structure(output)
            self.assertFalse(output.exists())

    def test_corrupt_export_is_rejected(self):
        if EXPORT is None:
            self.skipTest("Pass --structure for full-data corruption tests")
        mutations = [
            ("modules.json", lambda j: j["modules"][0]["imports"].append(999999)),
            ("build-info.json", lambda j: j.update(declaration_count=j["declaration_count"] + 1)),
            ("search/0.json", lambda j: j["declarations"].pop()),
            ("modules/49.json", lambda j: j["targets"][next(iter(j["targets"]))].update(modules=[-1])),
        ]
        for relative, mutate in mutations:
            with self.subTest(file=relative), tempfile.TemporaryDirectory(dir=TEST_ROOT) as tmp:
                target = Path(tmp)
                # Symlink untouched files, copy only the intentionally corrupted
                # JSON. Never write through an alias to the verified export.
                for source in EXPORT.iterdir():
                    destination = target / source.name
                    if source.name == relative.split("/")[0] and source.is_dir():
                        destination.mkdir()
                        for child in source.iterdir():
                            if child.name != Path(relative).name:
                                (destination / child.name).symlink_to(child)
                    elif source.name != relative:
                        destination.symlink_to(source, target_is_directory=source.is_dir())
                data = builder.read_json(EXPORT / relative)
                mutate(data)
                builder.write_json(target / relative, data)
                with self.assertRaises((ValueError, KeyError)):
                    builder.verify_export(target)

    def test_real_inventory(self):
        modules = builder.modules_in(builder.ROOT)
        from build_docs import modules_in as api_modules_in
        self.assertEqual(modules, api_modules_in(builder.ROOT))
        self.assertEqual(set(m.split(".")[0] for m in modules), set(builder.LIBRARIES))
        self.assertIn("Goldbach.OnePlusOneNine", modules)

    def test_errors_do_not_create_output(self):
        with tempfile.TemporaryDirectory(dir=TEST_ROOT) as tmp:
            output = Path(tmp) / "new"
            with self.assertRaises(ValueError):
                builder.build_structure(output, source_revision="HEAD")
            self.assertFalse(output.exists())
            output.mkdir()
            sentinel = output / "keep"
            sentinel.write_text("untouched")
            with self.assertRaises(ValueError):
                builder.build_structure(output)
            self.assertEqual(sentinel.read_text(), "untouched")

    def test_anchor_parser_preserves_quotes_and_decodes_entities(self):
        parser = builder.AnchorParser()
        parser.feed("<div id=\"Example.fact'\"></div><span id='Example.x&#39;'></span>")
        self.assertEqual(parser.ids, {"Example.fact'", "Example.x'"})

    def test_api_links_require_real_anchor(self):
        with tempfile.TemporaryDirectory(dir=TEST_ROOT) as tmp:
            api = Path(tmp)
            (api / "declarations").mkdir()
            (api / "M.html").write_text('<div id="Real.fact"></div>')
            (api / "declarations/declaration-data.bmp").write_text(json.dumps(
                {"declarations": {"Real.fact": {"docLink": "./M.html#Real.fact"}}}))
            links, pages = builder.api_links(api)
            self.assertEqual(links["Real.fact"], "../docs/M.html#Real.fact")
            self.assertNotIn("Real.fact._proof_1", links)
            self.assertIn("M", pages)
            (api / "M.html").write_text("no anchor")
            with self.assertRaises(ValueError):
                builder.api_links(api)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--structure", type=Path, help="Validate a real output/structure directory")
    parser.add_argument("--api", type=Path, help="Check every exported API link against these real pages")
    parser.add_argument("--evidence-dir", type=Path, help="Private root for transient test fixtures")
    args = parser.parse_args()
    global EXPORT, TEST_ROOT
    EXPORT = args.structure.resolve() if args.structure else None
    TEST_ROOT = args.evidence_dir
    if TEST_ROOT:
        TEST_ROOT.mkdir(parents=True, exist_ok=True)
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(StructureTests))
    if not result.wasSuccessful():
        raise SystemExit(1)
    if args.structure:
        report = builder.verify_export(args.structure, expected_modules=builder.modules_in(builder.ROOT), api=args.api)
        if report["module_count"] != 2514:
            raise AssertionError("Expected all 2514 source modules")
        print(json.dumps(report, indent=2))
    subprocess.run(["node", "--check", str(builder.ROOT / "website/structure/explorer.js")], check=True)


if __name__ == "__main__":
    main()
