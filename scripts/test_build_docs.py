#!/usr/bin/env python3
"""Regression tests for project-only documentation routing and validation."""
import json
from pathlib import Path
import tempfile
import unittest

from build_docs import MATHLIB_DOCS, decorate_homepage, modules_in, rewrite_site, ROOT, verify_site


class DocumentationTests(unittest.TestCase):
    def test_all_four_libraries_are_enumerated(self):
        modules = modules_in(ROOT)
        self.assertEqual({m.split(".")[0] for m in modules},
                         {"Goldbach", "MathlibNt", "AnalyticNumberTheory", "PrimeNumberTheoremAnd"})
        self.assertIn("Goldbach.Statement", modules)
        self.assertIn("PrimeNumberTheoremAnd.Defs", modules)

    def test_dependency_urls_and_embedded_headers_are_rewritten(self):
        with tempfile.TemporaryDirectory() as directory:
            site = Path(directory)
            (site / "Goldbach").mkdir()
            (site / "declarations").mkdir()
            page = site / "Goldbach/Statement.html"
            page.write_text('<a href="../Mathlib/Data/Nat/Prime/Defs.html#Nat.Prime">prime</a>'
                            '<a href="Statement.html#Goldbach.ChenTheorem">local</a>'
                            '<a href="https://example.org/?a=1&amp;b=2">unchanged</a>')
            index = site / "declarations/declaration-data.bmp"
            index.write_text(json.dumps({"modules": {"Mathlib.Data.Nat.Prime.Defs": {
                "url": "./Mathlib/Data/Nat/Prime/Defs.html"}},
                "header": '<a href="./Mathlib/Data/Nat/Prime/Defs.html#Nat.Prime">prime</a>'}))
            args = (site, ["Goldbach.Statement"], {"packages": []}, "https://example.org/blob/sha", MATHLIB_DOCS)
            rewrite_site(*args)
            self.assertIn(MATHLIB_DOCS + "Mathlib/Data/Nat/Prime/Defs.html#Nat.Prime", page.read_text())
            self.assertIn('href="Statement.html#Goldbach.ChenTheorem"', page.read_text())
            self.assertIn("a=1&amp;b=2", page.read_text())
            self.assertNotIn("amp;amp", page.read_text())
            data = json.loads(index.read_text())
            self.assertTrue(data["modules"]["Mathlib.Data.Nat.Prime.Defs"]["url"].startswith(MATHLIB_DOCS))
            self.assertIn(MATHLIB_DOCS, data["header"])
            before = (page.read_bytes(), index.read_bytes())
            rewrite_site(*args)
            self.assertEqual(before, (page.read_bytes(), index.read_bytes()))
            self.assertFalse((site / "Mathlib").exists())

    def test_migrated_module_links_resolve_to_exact_local_pages(self):
        with tempfile.TemporaryDirectory() as directory:
            site = Path(directory)
            parent = site / "AnalyticNumberTheory/LargeSieve"
            parent.mkdir(parents=True)
            page = parent / "Multiplicative.html"
            page.write_text('<a href="../.././LargeSieve/WellSpaced.html#known">legacy</a>'
                            '<a href="https://example.org/?a=1&amp;b=2">external</a>')
            (parent / "WellSpaced.html").write_text('<div id="known"></div>')
            args = (site, ["AnalyticNumberTheory.LargeSieve.WellSpaced"],
                    {"packages": []}, "https://example.org/blob/sha", MATHLIB_DOCS)
            urls = rewrite_site(*args)
            self.assertIn('href="WellSpaced.html#known"', page.read_text())
            before = page.read_bytes()
            self.assertEqual(rewrite_site(*args), urls)
            self.assertEqual(page.read_bytes(), before)
            self.assertEqual(urls, ['https://example.org/?a=1&b=2'])

    def test_legacy_mapping_requires_a_real_project_module(self):
        with tempfile.TemporaryDirectory() as directory:
            site = Path(directory)
            (site / "index.html").write_text('<a href="LargeSieve/PanTypeIAssembly.html">legacy</a>')
            with self.assertRaisesRegex(ValueError, "Missing canonical module"):
                rewrite_site(site, [], {"packages": []}, "https://example.org", MATHLIB_DOCS)

    def test_omitted_auxiliaries_link_only_to_existing_owners(self):
        with tempfile.TemporaryDirectory() as directory:
            site = Path(directory)
            page = site / "Module.html"
            page.write_text('<div id="definition"></div><div id="Side"></div>'
                            '<div id="real._proof_1"></div>'
                            '<a href="Module.html#definition._proof_1">proof</a>'
                            '<a href="Module.html#definition._aux_2">auxiliary</a>'
                            '<a href="Module.html#Side.ctorIdx">constructor index</a>'
                            '<a href="Module.html#real._proof_1">documented auxiliary</a>'
                            '<a href="Module.html#missing._proof_1">missing owner</a>'
                            '<a href="Module.html#unrelated">unrelated</a>')
            args = (site, ["Module"], {"packages": []}, "https://example.org", MATHLIB_DOCS)
            rewrite_site(*args)
            content = page.read_text()
            self.assertIn('href="Module.html#definition">proof', content)
            self.assertIn('href="Module.html#definition">auxiliary', content)
            self.assertIn('href="Module.html#Side">constructor index', content)
            self.assertIn('href="Module.html#real._proof_1"', content)
            self.assertIn('href="Module.html#missing._proof_1"', content)
            self.assertIn('href="Module.html#unrelated"', content)
            rewrite_site(*args)
            self.assertEqual(page.read_text(), content)

    def test_unknown_dependencies_fail_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            site = Path(directory)
            (site / "index.html").write_text('<a href="Unknown/Module.html">unknown</a>')
            with self.assertRaisesRegex(ValueError, "No external documentation mapping"):
                rewrite_site(site, [], {"packages": []}, "https://example.org", MATHLIB_DOCS)

    def test_apostrophe_declaration_anchor_is_valid(self):
        with tempfile.TemporaryDirectory() as directory:
            site = Path(directory)
            for name in ("index.html", "search.html", "search.js", "find/index.html",
                         "declarations/header-data.bmp", "navbar.html", "style.css"):
                file = site / name
                file.parent.mkdir(parents=True, exist_ok=True)
                file.touch()
            (site / "Support.html").write_text('<div id="Function.support_id\'"></div>')
            data = {"declarations": {"Function.support_id'": {
                "docLink": "./Support.html#Function.support_id%27"}},
                "modules": {"Support": {"url": "./Support.html"}}}
            (site / "declarations/declaration-data.bmp").write_text(json.dumps(data))
            self.assertEqual(verify_site(site, ["Support"]), 1)
            page = site / "Support.html"
            page.write_text(page.read_text() + '<a href="#top">top</a>'
                            '<a href="Support.html#Function.support_id%27">declaration</a>'
                            '<a href="find/?pattern=Function.support_id%27#doc">find</a>')
            self.assertEqual(verify_site(site, ["Support"]), 1)
            page.write_text(page.read_text() + '<a href="Support.html#missing">broken</a>')
            with self.assertRaisesRegex(ValueError, "Broken local anchor"):
                verify_site(site, ["Support"])

    def test_homepage_links_are_inside_main_and_idempotent(self):
        with tempfile.TemporaryDirectory() as directory:
            site = Path(directory)
            page = site / "index.html"
            page.write_text('<html><head><title>Index</title></head><body><main>'
                            '<h1>Welcome to the documentation page </h1></main></body></html>')
            (site / "Goldbach").mkdir()
            (site / "Goldbach/Statement.html").touch()
            decorate_homepage(site, True)
            first = page.read_bytes()
            content = page.read_text()
            self.assertIn('<title>Goldbach Lean — API documentation</title>', content)
            self.assertLess(content.index('<main>'), content.index('href="blueprint/index.html"'))
            self.assertLess(content.index('href="blueprint/index.html"'), content.index('</main>'))
            self.assertIn('Goldbach/Statement.html#Goldbach.ChenTheorem', content)
            self.assertNotIn('Goldbach/Theorem.html', content)
            decorate_homepage(site, True)
            self.assertEqual(first, page.read_bytes())

    def test_missing_assets_fail_validation(self):
        with tempfile.TemporaryDirectory() as directory:
            site = Path(directory)
            (site / "declarations").mkdir()
            (site / "declarations/declaration-data.bmp").write_text('{"declarations":{},"modules":{}}')
            with self.assertRaisesRegex(ValueError, "Missing documentation asset"):
                verify_site(site, [])


if __name__ == "__main__":
    unittest.main()
