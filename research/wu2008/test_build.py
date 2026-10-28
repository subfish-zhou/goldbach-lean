#!/usr/bin/env python3
"""Regression tests for receipt binding, using a fake Lake and compiler."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


class BuildReceiptsTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        shutil.copyfile(Path(__file__).with_name('build.py'), self.root / 'build.py')
        (self.root / 'src').mkdir()
        (self.root / 'lean-toolchain').write_text('test-toolchain\n')
        rows = []
        for name, imports in [('A', []), ('B', ['A'])]:
            source = self.root / 'src' / (name + '.lean')
            source.write_text('-- test source ' + name + '\n')
            rows.append({'module': name, 'imports': imports,
                         'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest()})
        (self.root / 'source-manifest.json').write_text(json.dumps(rows))
        self.rows = rows
        self.bin = self.root / 'bin'
        self.bin.mkdir()
        lake = self.bin / 'lake'
        lake.write_text('''#!/usr/bin/env python3
from pathlib import Path
import sys
root = Path(__file__).resolve().parent.parent
print(root / 'packages/fake' if sys.argv[-1] == 'LEAN_PATH' else root / 'toolchain')
''')
        lake.chmod(0o755)
        compiler = self.root / 'toolchain/bin/lean'
        compiler.parent.mkdir(parents=True)
        compiler.write_text('''#!/usr/bin/env python3
from pathlib import Path
import sys
root = Path(__file__).resolve().parents[2]
source = Path(sys.argv[-1])
obj = Path(sys.argv[sys.argv.index('-o') + 1])
obj.write_bytes(source.read_bytes())
with (root / 'calls').open('a') as f:
    f.write(source.stem + '\\n')
mode = (root / 'mode').read_text() if (root / 'mode').exists() else ''
if mode in ('parallel', 'parallel_failure'):
    import time
    started = root / ('started-' + source.stem)
    started.touch()
    if source.stem in ('A', 'C'):
        other = root / ('started-C' if source.stem == 'A' else 'started-A')
        deadline = time.monotonic() + 5
        while not other.exists():
            if time.monotonic() > deadline:
                raise SystemExit(8)
            time.sleep(0.01)
    if source.stem == 'B' and not (root / 'finished-A').exists():
        raise SystemExit(9)
    if mode == 'parallel_failure' and source.stem == 'A':
        raise SystemExit(7)
    if mode == 'parallel_failure' and source.stem == 'C':
        time.sleep(0.1)
    (root / ('finished-' + source.stem)).touch()
if mode == 'source' and source.stem == 'A':
    source.write_text('-- changed during compilation\\n')
if mode == 'manifest' and source.stem == 'A':
    with (root / 'source-manifest.json').open('a') as f:
        f.write('\\n')
if mode == 'dependency' and source.stem == 'B':
    (obj.parent / 'A.olean').write_bytes(b'changed dependency')
if mode == 'earlier_source' and source.stem == 'B':
    (source.parent / 'A.lean').write_text('-- earlier source changed\\n')
''')
        compiler.chmod(0o755)

    def build(self, mode='', all_modules=False, first=(), jobs=1, limit=None):
        (self.root / 'mode').write_text(mode)
        env = os.environ.copy()
        env['PATH'] = str(self.bin) + os.pathsep + env['PATH']
        return subprocess.run([sys.executable, str(self.root / 'build.py'), '--root', 'B'] +
                              (['--all'] if all_modules else []) +
                              [arg for name in first for arg in ('--first', name)] +
                              ['--jobs', str(jobs)] +
                              (['--limit', str(limit)] if limit is not None else []),
                              env=env, text=True, capture_output=True, timeout=20)

    def status(self):
        return json.loads((self.root / 'build/STATUS.json').read_text())

    def test_success_and_unchanged_cache(self):
        for _ in range(2):
            result = self.build()
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(self.status()['status'], 'passed')
        self.assertEqual((self.root / 'calls').read_text().splitlines(), ['A', 'B'])

    def test_transitive_import_removal_rebuilds_identical_object_consumers(self):
        # D -> A -> B -> C: removing A's import changes B's context but its
        # serialized object remains identical. C must nevertheless recompile.
        for name, imports in [('D', []), ('C', ['B'])]:
            source = self.root / 'src' / (name + '.lean')
            source.write_text('-- test source ' + name + '\n')
            self.rows.append({'module': name, 'imports': imports,
                              'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest()})
        self.rows[0]['imports'] = ['D']
        (self.root / 'source-manifest.json').write_text(json.dumps(self.rows))
        result = self.build(all_modules=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        before = {n: json.loads((self.root / 'build/receipts' / (n + '.json')).read_text())
                  for n in ['B', 'C']}
        self.rows[0]['imports'] = []
        source = self.root / 'src/A.lean'
        source.write_text('-- A no longer imports D\n')
        self.rows[0]['source_sha256'] = hashlib.sha256(source.read_bytes()).hexdigest()
        (self.root / 'source-manifest.json').write_text(json.dumps(self.rows))
        result = self.build(all_modules=True, jobs=2)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual((self.root / 'calls').read_text().splitlines(),
                         ['D', 'A', 'B', 'C', 'A', 'B', 'C'])
        after = {n: json.loads((self.root / 'build/receipts' / (n + '.json')).read_text())
                 for n in ['B', 'C']}
        self.assertEqual(before['B']['object_sha256'], after['B']['object_sha256'])
        self.assertEqual(before['C']['dependencies'], after['C']['dependencies'])
        self.assertNotEqual(before['C']['dependency_contexts'], after['C']['dependency_contexts'])
        for n in after:
            self.assertNotEqual(before[n]['context_sha256'], after[n]['context_sha256'])
        result = self.build(all_modules=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(len((self.root / 'calls').read_text().splitlines()), 7)

    def test_legacy_receipt_without_context_forces_recompile(self):
        result = self.build()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        path = self.root / 'build/receipts/B.json'
        receipt = json.loads(path.read_text())
        del receipt['dependency_contexts']
        del receipt['context_sha256']
        path.write_text(json.dumps(receipt))
        result = self.build()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual((self.root / 'calls').read_text().splitlines(), ['A', 'B', 'B'])

    def test_corrupt_own_context_forces_recompile(self):
        result = self.build()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        path = self.root / 'build/receipts/B.json'
        receipt = json.loads(path.read_text())
        receipt['context_sha256'] = '0' * 64
        path.write_text(json.dumps(receipt))
        result = self.build()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual((self.root / 'calls').read_text().splitlines(), ['A', 'B', 'B'])

    def test_priority_preserves_dependencies_and_full_scope(self):
        source = self.root / 'src/C.lean'
        source.write_text('-- independent C\n')
        self.rows.insert(0, {'module': 'C', 'imports': [],
                            'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest()})
        (self.root / 'source-manifest.json').write_text(json.dumps(self.rows))
        result = self.build(all_modules=True, first=('B', 'B'))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual((self.root / 'calls').read_text().splitlines(), ['A', 'B', 'C'])
        plan = json.loads((self.root / 'build/PLAN.json').read_text())
        self.assertEqual(plan['modules'], ['A', 'B', 'C'])
        self.assertEqual(self.status()['verified'], 3)

    def test_priority_reordering_reuses_cache(self):
        self.rows[1]['imports'] = []
        (self.root / 'source-manifest.json').write_text(json.dumps(self.rows))
        for first in [('B',), ('A',)]:
            result = self.build(all_modules=True, first=first)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual((self.root / 'calls').read_text().splitlines(), ['B', 'A'])

    def test_priority_cannot_extend_selected_scope(self):
        self.rows[1]['imports'] = []
        (self.root / 'source-manifest.json').write_text(json.dumps(self.rows))
        result = self.build(first=('A',))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('outside selected closure', result.stderr)
        self.assertFalse((self.root / 'build').exists())
        self.assertFalse((self.root / 'calls').exists())

    def test_unknown_priority_fails_before_build(self):
        result = self.build(first=('Missing',))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('outside selected closure', result.stderr)
        self.assertFalse((self.root / 'build').exists())

    def check_changed(self, mode, module):
        result = self.build(mode)
        self.assertEqual(result.returncode, 125, result.stdout + result.stderr)
        self.assertEqual(self.status()['status'], 'inputs_changed')
        receipt = json.loads((self.root / 'build/receipts' / (module + '.json')).read_text())
        self.assertEqual(receipt['exit_code'], 125)
        self.assertEqual(receipt['source_sha256'], self.rows[0 if module == 'A' else 1]['source_sha256'])

    def test_source_changed_while_compiling(self):
        self.check_changed('source', 'A')

    def test_manifest_changed_while_compiling(self):
        self.check_changed('manifest', 'A')

    def test_dependency_object_changed_while_compiling(self):
        self.check_changed('dependency', 'B')

    def test_final_audit_rejects_changed_earlier_source(self):
        result = self.build('earlier_source')
        self.assertEqual(result.returncode, 125, result.stdout + result.stderr)
        self.assertEqual(self.status()['status'], 'inputs_changed')

    def test_final_audit_rejects_changed_unrelated_output(self):
        self.rows[1]['imports'] = []
        (self.root / 'source-manifest.json').write_text(json.dumps(self.rows))
        result = self.build('dependency', all_modules=True)
        self.assertEqual(result.returncode, 125, result.stdout + result.stderr)
        self.assertEqual(self.status()['status'], 'inputs_changed')
        self.assertIn('output object changed', self.status()['reason'])

    def add_independent_module(self):
        source = self.root / 'src/C.lean'
        source.write_text('-- independent C\n')
        self.rows.append({'module': 'C', 'imports': [],
                          'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest()})
        (self.root / 'source-manifest.json').write_text(json.dumps(self.rows))

    def test_parallel_independent_modules_and_dependency_barrier(self):
        self.add_independent_module()
        result = self.build('parallel', all_modules=True, jobs=2)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.status()['verified'], 3)
        calls = (self.root / 'calls').read_text().splitlines()
        self.assertLess(calls.index('A'), calls.index('B'))
        self.assertLess(calls.index('C'), calls.index('B'))
        receipt = json.loads((self.root / 'build/receipts/B.json').read_text())
        self.assertEqual(receipt['dependencies']['A'],
                         hashlib.sha256((self.root / 'build/lib/A.olean').read_bytes()).hexdigest())
        result = self.build(all_modules=True, jobs=3)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual((self.root / 'calls').read_text().splitlines(), calls)

    def test_parallel_failure_drains_jobs_without_releasing_dependents(self):
        self.add_independent_module()
        result = self.build('parallel_failure', all_modules=True, jobs=2)
        self.assertEqual(result.returncode, 7, result.stdout + result.stderr)
        self.assertEqual(self.status()['status'], 'failed')
        self.assertEqual(set((self.root / 'calls').read_text().splitlines()), {'A', 'C'})
        self.assertTrue((self.root / 'finished-C').exists())
        receipt = json.loads((self.root / 'build/receipts/C.json').read_text())
        self.assertEqual(receipt['exit_code'], 0)
        self.assertFalse((self.root / 'build/receipts/B.json').exists())

    def test_parallel_batch_limit_counts_started_compilations(self):
        self.add_independent_module()
        result = self.build(all_modules=True, jobs=2, limit=1)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.status()['status'], 'batch_limit')
        self.assertEqual((self.root / 'calls').read_text().splitlines(), ['A'])
        result = self.build(all_modules=True, jobs=2, limit=2)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.status()['status'], 'passed')
        self.assertEqual(sorted((self.root / 'calls').read_text().splitlines()), ['A', 'B', 'C'])
        result = self.build(all_modules=True, jobs=2, limit=0)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.status()['status'], 'passed')

    def test_parallel_rejects_changed_input(self):
        self.add_independent_module()
        result = self.build('source', all_modules=True, jobs=2)
        self.assertEqual(result.returncode, 125, result.stdout + result.stderr)
        self.assertEqual(self.status()['status'], 'inputs_changed')
        self.assertNotIn('B', (self.root / 'calls').read_text().splitlines())

    def test_zero_jobs_fails_before_build(self):
        result = self.build(jobs=0)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('must be positive', result.stderr)
        self.assertFalse((self.root / 'build').exists())


if __name__ == '__main__':
    unittest.main()
