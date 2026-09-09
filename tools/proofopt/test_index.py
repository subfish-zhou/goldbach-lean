import importlib.util
import json
from pathlib import Path
import sqlite3
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('proof_index', Path(__file__).with_name('index.py'))
assert spec is not None and spec.loader is not None
idx = importlib.util.module_from_spec(spec)
spec.loader.exec_module(idx)


class IndexTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.text = 'theorem A : True := by\n  trivial\ntheorem B : True := by\n  trivial\n'
        (self.root / 'M.lean').write_text(self.text)
        obj = self.root / 'M.olean'; obj.write_bytes(b'fixture-not-real-olean')
        ilean = self.root / 'M.ilean'; ilean.write_text('{}')
        self.manifest = {'schema': 1, 'revision': 'fixture', 'source_root': str(self.root), 'modules': [
            {'module': 'M', 'source': 'M.lean', 'source_sha256': idx.digest(self.text.encode()),
             'object': str(obj), 'object_parts_sha256': idx.object_parts(obj), 'object_size': obj.stat().st_size, 'object_mtime_ns': obj.stat().st_mtime_ns,
             'ilean': str(ilean), 'ilean_sha256': idx.digest(ilean.read_bytes()),
             'direct_imports': [], 'decls': {'A': [0,0,1,9,0,8,0,9], 'B': [2,0,3,9,2,8,2,9]}}]}

    def row(self, name, **kw):
        d = dict(module='M', name=name, kind='theorem', type_hash='1', type_shape_hash='2',
                 conclusion_head='True', level_params=[], proof_hash=None, proof_nodes=2,
                 direct_deps=[], type_deps=['True'])
        d.update(kw)
        return d

    def build(self, rows):
        stream = self.root / 'input.jsonl'
        raw = ''.join(json.dumps(x)+'\n' for x in rows).encode()
        requested = sorted(set(x['module'] for x in rows))
        stream.write_bytes(idx.seal_records(self.manifest, raw, requested, 'fixture-extractor'))
        out = self.root / 'index.sqlite'
        idx.build_index(self.manifest, [stream], out)
        return out

    def test_unicode_utf16(self):
        self.assertEqual(idx.utf16_prefix('a😀b', 3), 'a😀')
        with self.assertRaises(UnicodeDecodeError): idx.utf16_prefix('a😀b', 2)
        self.assertEqual(idx.source_slice('a😀b\n', [0,1,0,3,0,1,0,3]), '😀')

    def test_bad_range(self):
        for span in ([1,0,0,1,0,0,0,0], [0,0,4,1,0,0,0,0], [0,0]):
            with self.assertRaises(ValueError): idx.source_slice('abc\n', list(span))

    def test_cycles_terminate(self):
        g = {'a': {'b'}, 'b': {'a'}}
        self.assertTrue(idx.reachable(g, 'a', 'b'))
        self.assertFalse(idx.reachable(g, 'a', 'c'))

    def test_candidate_not_verification_and_no_self(self):
        db = self.build([self.row('A'), self.row('B')])
        result = idx.candidates(db, min_lines=1)
        self.assertEqual(result['candidate_count'], 2)
        self.assertTrue(all(x['target'] != x['provider'] and x['status'].startswith('unverified') for x in result['candidates']))
        with sqlite3.connect(db) as c:
            self.assertEqual(c.execute('SELECT proof_hash FROM declarations WHERE name=\'A\'').fetchone(), (None,))

    def test_generated_names_not_candidates(self):
        db = self.build([self.row('A'), self.row('A.generated'), self.row('B', kind='definition')])
        self.assertEqual(idx.candidates(db, min_lines=1)['candidate_count'], 0)

    def test_reverse_dependency_rejected(self):
        db = self.build([self.row('A'), self.row('B', direct_deps=['A'])])
        pairs = {(x['target'],x['provider']) for x in idx.candidates(db, min_lines=1)['candidates']}
        self.assertNotIn(('A','B'), pairs)
        self.assertIn(('B','A'), pairs)

    def test_conflicting_duplicate_rejected(self):
        with self.assertRaisesRegex(ValueError, 'conflicting'):
            self.build([self.row('A'),self.row('A', type_hash='changed')])

    def test_identical_duplicate_deduplicated(self):
        db = self.build([self.row('A'),self.row('A')])
        with sqlite3.connect(db) as c:
            self.assertEqual(c.execute('SELECT count(*) FROM declarations').fetchone()[0], 1)

    def test_unknown_module_rejected(self):
        with self.assertRaisesRegex(ValueError, 'unknown module'):
            self.build([self.row('A', module='Other')])

    def test_stale_source_rejected(self):
        db = self.build([self.row('A')])
        (self.root / 'M.lean').write_text('changed')
        with self.assertRaisesRegex(ValueError, 'stale source'): idx.candidates(db)

    def test_changed_object_rejected(self):
        (self.root / 'M.olean').write_bytes(b'changed')
        with self.assertRaisesRegex(ValueError, 'object changed'): idx.validate_manifest(self.manifest)

    def test_changed_ilean_rejected(self):
        (self.root / 'M.ilean').write_text('{"changed":true}')
        with self.assertRaisesRegex(ValueError, 'stale ilean'): idx.validate_manifest(self.manifest)

    def test_incomplete_index_rejected(self):
        with self.assertRaises(ValueError):
            self.build([self.row('A', module='Other')])
        with self.assertRaisesRegex(ValueError, 'incomplete index'):
            idx.candidates(self.root / 'index.sqlite')

    def test_empty_index_rejected(self):
        with self.assertRaisesRegex(ValueError, 'empty extraction'):
            self.build([])

    def test_actual_import_schema(self):
        self.manifest['modules'][0]['direct_imports'] = [['Mathlib', False, False, False]]
        db = self.build([self.row('A'), self.row('B')])
        self.assertEqual(idx.candidates(db, min_lines=1)['candidate_count'], 2)

    def test_no_overwrite(self):
        self.build([self.row('A')])
        with self.assertRaises(FileExistsError): self.build([self.row('A')])


if __name__ == '__main__':
    unittest.main()
