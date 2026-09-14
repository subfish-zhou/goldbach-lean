"""Synthetic publication-gate fixtures and real local Git transport tests."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from publish_site import publish_tree, validate_payload


class PayloadTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.rev = '1' * 40
        for name in ('index.html', 'docs/index.html', 'blueprint/index.html',
                     'assets/dependencies/panel.html', 'report/index.html', '.nojekyll'):
            p = self.root / name
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text('Synthetic fixture, not release evidence.')
        self.api = {'scope': 'full', 'source_revision': self.rev,
                    'modules': ['Example'], 'module_count': 1, 'declaration_count': 1}
        self.info = {'scope': 'full', 'website_source_revision': self.rev,
                     'api_source_revision': self.rev, 'blueprint_source_revision': self.rev,
                     'structure_source_revision': self.rev}
        self.write_info()
        for part in ('blueprint', 'assets/dependencies'):
            (self.root / part / 'build-info.json').write_text(json.dumps({'source_revision': self.rev}))
        self.structure_check = patch('publish_site.verify_export')
        self.structure_check.start()
        self.addCleanup(self.structure_check.stop)
        self.site_check = patch('publish_site.verify_site', return_value=1)
        self.link_check = patch('publish_site.verify_local_links')
        self.site_check.start()
        self.link_check.start()
        self.addCleanup(self.site_check.stop)
        self.addCleanup(self.link_check.stop)

    def write_info(self):
        (self.root / 'build-info.json').write_text(json.dumps(self.info))
        (self.root / 'docs/build-info.json').write_text(json.dumps(self.api))

    def test_retired_route_is_rejected(self):
        (self.root / 'structure').mkdir()
        (self.root / 'structure/index.html').write_text('retired redirect fixture')
        with self.assertRaisesRegex(ValueError, 'Retired standalone'):
            validate_payload(self.root)

    def test_complete_inventory(self):
        r = validate_payload(self.root, expected_modules=['Example'])
        self.assertEqual(r['module_count'], 1)
        self.assertIn('assets/dependencies/panel.html', r['files'])
        with self.assertRaisesRegex(ValueError, 'inventory differs'):
            validate_payload(self.root, expected_modules=['Example', 'Missing'])

    def test_partial_and_relabelled_api_rejected(self):
        self.api['scope'] = 'partial'
        self.write_info()
        with self.assertRaisesRegex(ValueError, 'full API'):
            validate_payload(self.root)
        self.api['scope'] = 'full'
        self.info['api_source_revision'] = '2' * 40
        self.write_info()
        with self.assertRaisesRegex(ValueError, 'relabelled'):
            validate_payload(self.root)

    def test_missing_route_and_symlink_rejected(self):
        (self.root / 'report/index.html').unlink()
        with self.assertRaisesRegex(ValueError, 'Missing publication route'):
            validate_payload(self.root)
        (self.root / 'report/index.html').write_text('fixture')
        (self.root / 'bad.json').symlink_to(self.root / 'build-info.json')
        with self.assertRaisesRegex(ValueError, 'Symlink'):
            validate_payload(self.root)

    def test_graph_webassembly_assets_have_a_real_header(self):
        asset = self.root / 'blueprint/graphviz.wasm'
        asset.write_bytes(b'\x00asm\x01\x00\x00\x00')
        self.assertIn('blueprint/graphviz.wasm', validate_payload(self.root)['files'])
        asset.write_bytes(b'not a WebAssembly module')
        with self.assertRaisesRegex(ValueError, 'Invalid WebAssembly'):
            validate_payload(self.root)

    def test_nonstatic_and_private_content_rejected(self):
        bad = self.root / 'proof.olean'
        bad.write_bytes(b'fixture')
        with self.assertRaisesRegex(ValueError, 'Non-static'):
            validate_payload(self.root)
        bad.unlink()
        synthetic_path = str(Path('/', 'home', 'synthetic-user', 'hidden', 'file'))
        (self.root / 'leak.json').write_text(json.dumps({'path': synthetic_path}))
        with self.assertRaisesRegex(ValueError, 'Private provenance'):
            validate_payload(self.root)


class GitPublicationTests(unittest.TestCase):
    def test_generated_branch_is_fast_forwarded_and_history_preserved(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp)
            remote = p / 'remote.git'
            subprocess.run(['git', 'init', '--bare', '-q', remote], check=True)
            site = p / 'site'
            site.mkdir()
            (site / 'old.html').write_text('first synthetic fixture')

            def record():
                return {'website_source_revision': '1' * 40,
                        'files': {str(f.relative_to(site)): hashlib.sha256(f.read_bytes()).hexdigest()
                                  for f in site.rglob('*') if f.is_file()}}

            first = publish_tree(site, p / 'stage-1', str(remote),
                                 ('Fixture Publisher', 'fixture@localhost'), record())
            (site / 'old.html').unlink()
            (site / 'index.html').write_text('second synthetic fixture')
            second = publish_tree(site, p / 'stage-2', str(remote),
                                  ('Fixture Publisher', 'fixture@localhost'), record())
            self.assertNotEqual(first, second)
            names = subprocess.check_output(['git', '--git-dir', remote, 'ls-tree', '-r', '--name-only', 'gh-pages'], text=True)
            self.assertEqual(names.strip(), 'index.html')
            old = subprocess.check_output(['git', '--git-dir', remote, 'show', first + ':old.html'], text=True)
            self.assertEqual(old, 'first synthetic fixture')
            parent = subprocess.check_output(['git', '--git-dir', remote, 'rev-parse', second + '^'], text=True).strip()
            self.assertEqual(parent, first)

    def test_changed_payload_is_not_pushed(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp)
            remote = p / 'remote.git'
            subprocess.run(['git', 'init', '--bare', '-q', remote], check=True)
            site = p / 'site'
            site.mkdir()
            (site / 'index.html').write_text('actual fixture')
            bad = {'website_source_revision': '1' * 40, 'files': {'index.html': '0' * 64}}
            with self.assertRaisesRegex(ValueError, 'Payload changed'):
                publish_tree(site, p / 'stage', str(remote), ('Fixture', 'fixture@localhost'), bad)
            refs = subprocess.check_output(['git', '--git-dir', remote, 'show-ref'], text=True) if subprocess.run(
                ['git', '--git-dir', remote, 'show-ref', '--quiet']).returncode == 0 else ''
            self.assertEqual(refs, '')


if __name__ == '__main__':
    unittest.main()
