"""Project-home layout, input preservation and deployment-boundary regressions."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from build_docs import verify_local_links, verify_site
from build_site import add_project_navigation, assemble


class ProjectSiteTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.api = self.root / "api"
        self.blueprint = self.root / "blueprint"
        self.output = self.root / "published"
        self.modules = ["Goldbach.Statement", "Goldbach.Theorem"]
        declarations = {"Goldbach.ChenTheorem": "Statement",
                        "Goldbach.chen_theorem": "Theorem",
                        "Goldbach.representation_lower_bound": "Theorem"}
        for name in ("search.html", "search.js", "find/index.html", "style.css",
                     "declarations/header-data.bmp"):
            file = self.api / name
            file.parent.mkdir(parents=True, exist_ok=True)
            file.touch()
        (self.api / "index.html").write_text('<html><head></head><body><main>'
                                              '<a href="blueprint/index.html">Proof Blueprint</a>'
                                              '</main></body></html>')
        (self.api / "navbar.html").write_text('<html><head></head><body>'
                                               '<h3>General documentation</h3></body></html>')
        (self.api / "Goldbach").mkdir()
        for module in ("Statement", "Theorem"):
            ids = ''.join(f'<div id="{name}"></div>' for name, mod in declarations.items() if mod == module)
            (self.api / f"Goldbach/{module}.html").write_text(f'<html><head></head><body>{ids}</body></html>')
        index = {"modules": {m: {"url": m.replace('.', '/') + '.html'} for m in self.modules},
                 "declarations": {name: {"docLink": f"./Goldbach/{mod}.html#{name}"}
                                  for name, mod in declarations.items()}}
        (self.api / "declarations/declaration-data.bmp").write_text(json.dumps(index))
        self.report = {"scope": "full", "modules": self.modules, "module_count": 2,
                       "declaration_count": 3, "source_revision": "a" * 40, "blueprint_included": True}
        (self.api / "build-info.json").write_text(json.dumps(self.report))
        (self.api / "blueprint").mkdir()
        (self.api / "blueprint/index.html").write_text("Old nested copy")
        self.blueprint.mkdir()
        for name in ("index.html", "dep_graph_document.html"):
            (self.blueprint / name).write_text('<html><head></head><body><header>Blueprint</header></body></html>')

    def snapshot(self, directory):
        return {str(p.relative_to(directory)): p.read_bytes() for p in directory.rglob('*') if p.is_file()}

    def test_complete_layout_preserves_inputs_and_navigation_is_idempotent(self):
        before = self.snapshot(self.api), self.snapshot(self.blueprint)
        report = assemble(self.api, self.blueprint, self.output)
        self.assertEqual(before, (self.snapshot(self.api), self.snapshot(self.blueprint)))
        self.assertTrue((self.output / "docs/search.js").is_file())
        self.assertFalse((self.output / "docs/blueprint").exists())
        self.assertIn('href="../index.html"', (self.output / "docs/navbar.html").read_text())
        self.assertIn('href="../blueprint/index.html"', (self.output / "docs/index.html").read_text())
        self.assertIn('href="../docs/index.html"', (self.output / "blueprint/index.html").read_text())
        self.assertEqual(verify_site(self.output / "docs", self.modules, site_root=self.output), 3)
        original = self.snapshot(self.output)
        add_project_navigation(self.output)
        self.assertEqual(original, self.snapshot(self.output))
        self.assertEqual(report['homepage_sha256'], hashlib.sha256((self.output / 'index.html').read_bytes()).hexdigest())
        self.assertFalse(json.loads((self.output / 'docs/build-info.json').read_text())['blueprint_included'])
        self.assertTrue(report['blueprint_included'])
        self.assertNotIn('@@', (self.output / 'index.html').read_text())
        with self.assertRaisesRegex(ValueError, 'Output already exists'):
            assemble(self.api, self.blueprint, self.output)

    def test_api_only_input_matches_ci_layout(self):
        # Remove only the disposable legacy-bundle fixture.
        (self.api / 'blueprint/index.html').unlink()
        (self.api / 'blueprint').rmdir()
        (self.api / 'index.html').write_text('<html><head></head><body><main>Lean Doc</main></body></html>')
        self.report['blueprint_included'] = False
        (self.api / 'build-info.json').write_text(json.dumps(self.report))
        result = assemble(self.api, self.blueprint, self.output)
        self.assertTrue(result['blueprint_included'])
        self.assertIn('href="../blueprint/index.html"', (self.output / 'docs/navbar.html').read_text())
        self.assertEqual(verify_site(self.output / 'docs', self.modules, site_root=self.output), 3)

    def test_blueprint_theorem_headers_are_not_page_headers(self):
        page = self.blueprint / 'index.html'
        page.write_text('<html><head></head><body><header>Page</header>'
                        '<article><header>Theorem</header></article></body></html>')
        assemble(self.api, self.blueprint, self.output)
        text = (self.output / 'blueprint/index.html').read_text()
        self.assertEqual(text.count('id="goldbach-project-links"'), 1)
        self.assertIn('<article><header>Theorem</header></article>', text)

    def test_partial_api_cannot_back_the_complete_homepage(self):
        self.report['scope'] = 'partial'
        (self.api / 'build-info.json').write_text(json.dumps(self.report))
        with self.assertRaisesRegex(ValueError, 'requires a full API'):
            assemble(self.api, self.blueprint, self.output)
        self.assertFalse(self.output.exists())

    def test_invalid_revision_fails_before_template_expansion(self):
        self.report['source_revision'] = '<script>bad</script>'
        (self.api / 'build-info.json').write_text(json.dumps(self.report))
        with self.assertRaisesRegex(ValueError, 'full source revision'):
            assemble(self.api, self.blueprint, self.output)

    def test_missing_homepage_target_fails_before_publication(self):
        # This is an explicitly disposable test fixture, not a project artifact.
        (self.blueprint / 'dep_graph_document.html').unlink()
        with self.assertRaisesRegex(ValueError, 'Broken local link'):
            assemble(self.api, self.blueprint, self.output)
        self.assertFalse(self.output.exists())

    def test_stale_declaration_count_fails(self):
        self.report['declaration_count'] = 4
        (self.api / 'build-info.json').write_text(json.dumps(self.report))
        with self.assertRaisesRegex(ValueError, 'census changed'):
            assemble(self.api, self.blueprint, self.output)

    def test_empty_directory_is_not_a_valid_web_route(self):
        site = self.root / 'empty-route'
        (site / 'missing-index').mkdir(parents=True)
        (site / 'index.html').write_text('<a href="missing-index/">broken</a>')
        with self.assertRaisesRegex(ValueError, 'Broken local link'):
            verify_local_links(site)

    def test_parent_boundary_does_not_allow_escape_from_project(self):
        site = self.root / 'boundary'
        (site / 'docs').mkdir(parents=True)
        (self.root / 'outside.html').write_text('outside')
        (site / 'docs/index.html').write_text('<a href="../../outside.html">escape</a>')
        with self.assertRaisesRegex(ValueError, 'Broken local link'):
            verify_local_links(site / 'docs', boundary=site)


if __name__ == '__main__':
    unittest.main()
