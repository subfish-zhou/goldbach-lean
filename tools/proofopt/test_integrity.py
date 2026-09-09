"""Regression tests from independent review; initially RED on v1."""
from pathlib import Path
import json
import os
from unittest import mock, TestCase
import test_index as base
idx = base.idx


class IntegrityTests(TestCase):
    setUp = base.IndexTests.setUp
    row = base.IndexTests.row
    build = base.IndexTests.build
    def test_uri_reserved_characters(self):
        db = self.build([self.row('A'),self.row('B')])
        strange = self.root / 'index?audit#one.sqlite'
        db.rename(strange)
        before = set(self.root.iterdir())
        self.assertEqual(idx.candidates(strange, min_lines=1)['candidate_count'], 2)
        self.assertEqual(set(self.root.iterdir()), before)

    def test_lsp_edge_cases(self):
        with self.assertRaises(ValueError):
            idx.source_slice('abc\n', [0,0,0,4,0,99,0,100])
        text = '-- a\u2028b\ntheorem A : True := by trivial\n'
        self.assertEqual(idx.source_slice(text, [1,0,1,28,1,8,1,9]), 'theorem A : True := by trivi')
        self.assertEqual(idx.source_slice('abc\n', [0,0,1,0,0,0,0,3]), 'abc\n')

    def test_restored_stat_not_same_object(self):
        obj = self.root / 'M.olean'
        before = obj.stat()
        obj.write_bytes(b'X' * before.st_size)
        os.utime(obj, ns=(before.st_atime_ns,before.st_mtime_ns))
        with self.assertRaisesRegex(ValueError,'object'):
            idx.validate_manifest(self.manifest)

    def test_unsealed_jsonl_rejected(self):
        stream = self.root / 'raw.jsonl'
        stream.write_text(json.dumps(self.row('A'))+'\n')
        with self.assertRaisesRegex(ValueError, 'sealed|footer|complete|receipt'):
            idx.build_index(self.manifest, [stream], self.root/'bad.sqlite')

    def test_cross_module_occurrences_are_not_equated(self):
        other = dict(self.manifest['modules'][0], module='N', decls={})
        self.manifest['modules'].append(other)
        rows=[self.row('A',direct_deps=['first']),
              self.row('A',module='N',proof_hash='different',direct_deps=['second']),self.row('B')]
        raw=b''.join((json.dumps(r)+'\n').encode() for r in rows)
        stream=self.root/'in.jsonl';stream.write_bytes(idx.seal_records(self.manifest,raw,['M','N'],'fixture'))
        db=self.root/'index.db';summary=idx.build_index(self.manifest,[stream],db)
        self.assertEqual(summary['ambiguous_names_excluded'],1)
        self.assertEqual(idx.candidates(db,min_lines=1)['candidate_count'],0)
        from propose import propose
        result=self.root/'result.json'
        result.write_text(json.dumps([{'target':'A','provider':'B','status':'success','kernel_checked':True,'has_mvar':False,'has_sorry':False,'remaining':[]}]))
        with self.assertRaisesRegex(ValueError,'ambiguous'):
            propose(db,result,'A',self.root,self.root/'proposal',Path('/not-executed'),'')
        with idx.sqlite3.connect(db) as conn:
            self.assertEqual(conn.execute('SELECT count(*) FROM occurrences WHERE name=?',('A',)).fetchone()[0],2)
            self.assertEqual({r[0] for r in conn.execute('SELECT provider FROM dependencies WHERE consumer=? AND role=\'proof\'',('A',))},{'first','second'})

    def test_oversized_proof_node_metric(self):
        db=self.build([self.row('A',proof_nodes=2**100),self.row('B')])
        with idx.sqlite3.connect(db) as conn:
            self.assertEqual(conn.execute('SELECT proof_nodes FROM declarations WHERE name=?',('A',)).fetchone()[0],str(2**100))

    def test_connection_closed_on_stale(self):
        import sqlite3
        db = self.build([self.row('A')])
        (self.root/'M.lean').write_text('changed')
        closed = []
        class Conn(sqlite3.Connection):
            def close(self):
                closed.append(True)
                super().close()
        real_connect = sqlite3.connect
        def connect(*a, **kw):
            return real_connect(*a, **kw, factory=Conn)
        with mock.patch.object(idx.sqlite3, 'connect', connect):
            with self.assertRaises(ValueError): idx.candidates(db)
        self.assertTrue(closed)
