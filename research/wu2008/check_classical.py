#!/usr/bin/env python3
"""Check the integrated Wu theorem's literal statement and standard axioms.

Run after build.py --all. Only this research tree and pinned package objects
are used; staged or direct-check caches are never imported.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import os
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
BUILD = ROOT / 'build'
THEOREM = 'WuPaper.ClassicalSlots.one8938'
PROBE = '''import WR2ClassicalCertificate

theorem WuLiteralAcceptance :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∃ p r q : ℕ, Nat.Prime p ∧ (r = 1 ∨ Nat.Prime r) ∧ Nat.Prime q ∧
        N = p + r * q ∧ r ^ 5000 ≤ q ^ 4469 :=
  WuPaper.ClassicalSlots.one8938

theorem WuLegacyLiteralAcceptance :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∃ p r q : ℕ, Nat.Prime p ∧ (r = 1 ∨ Nat.Prime r) ∧ Nat.Prime q ∧
        N = p + r * q ∧ r ^ 500 ≤ q ^ 447 :=
  WuPaper.ClassicalSlots.one894

#print axioms WuLegacyLiteralAcceptance
#print axioms WuPaper.ClassicalSlots.one8938
#print axioms WuLiteralAcceptance
#print axioms WuPaper.ClassicalSlots.one894
#print axioms WuPaper.ClassicalSlots.classical_lower
'''


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_build():
    manifest = json.loads((ROOT / 'source-manifest.json').read_text())
    names = {row['module'] for row in manifest}
    assert len(names) == len(manifest), 'Duplicate manifest module'
    assert 'WR2ClassicalCertificate' in names, 'Classical certificate not integrated'
    status = json.loads((BUILD / 'STATUS.json').read_text())
    assert status['status'] == 'passed', status
    assert status['verified'] == status['planned'] == len(names), status
    hashes = {}
    receipts = {}
    sources = set()
    for row in manifest:
        name = row['module']
        relative = Path(*name.split('.'))
        source = (ROOT / 'src' / relative).with_suffix('.lean')
        obj = (BUILD / 'lib' / relative).with_suffix('.olean')
        receipt = json.loads((BUILD / 'receipts' / relative).with_suffix('.json').read_text())
        assert not source.is_symlink() and not obj.is_symlink(), name
        assert receipt['exit_code'] == 0 and not receipt.get('direct_check_only'), name
        assert sha(source) == row['source_sha256'] == receipt['source_sha256'], name
        hashes[name] = sha(obj)
        assert hashes[name] == receipt['object_sha256'], name
        receipts[name] = receipt
        sources.add(source)
    assert sources == set((ROOT / 'src').rglob('*.lean')), 'Source inventory mismatch'
    for row in manifest:
        expected = {n: hashes[n] for n in row['imports'] if n in names}
        receipt = receipts[row['module']]
        assert receipt['dependencies'] == expected, row['module']
        contexts = {n: receipts[n]['context_sha256'] for n in expected}
        assert receipt.get('dependency_contexts') == contexts, row['module']
        payload = {'source_sha256': receipt['source_sha256'],
                   'object_sha256': receipt['object_sha256'],
                   'dependency_contexts': contexts}
        digest = hashlib.sha256(json.dumps(
            payload, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
        assert receipt.get('context_sha256') == digest, row['module']
    return hashes


def main():
    before = verify_build()
    manifest_hash = sha(ROOT / 'source-manifest.json')
    env = os.environ.copy()
    env.pop('LEAN_PATH', None)
    env.pop('LEAN_SRC_PATH', None)
    packages = subprocess.check_output(
        ['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT, env=env, text=True)
    package_paths = []
    for entry in packages.strip().split(':'):
        path = Path(entry)
        path = (ROOT / path).resolve() if not path.is_absolute() else path.resolve()
        if '/packages/' in str(path):
            package_paths.append(str(path))
    assert package_paths, 'No pinned package library paths'
    prefix = subprocess.check_output(
        ['lake', 'env', 'lean', '--print-prefix'], cwd=ROOT, env=env, text=True).strip()
    env['LEAN_PATH'] = ':'.join([str(BUILD / 'lib'), *package_paths])
    spec = importlib.util.spec_from_file_location('release_checks', ROOT.parents[1] / 'scripts/check.py')
    checks = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checks)
    with tempfile.TemporaryDirectory(prefix='wu-literal-') as directory:
        probe = Path(directory) / 'WuLiteralAcceptance.lean'
        probe.write_text(PROBE)
        result = subprocess.run(
            [str(Path(prefix) / 'bin/lean'), '-j2', '-DwarningAsError=true',
             '-DautoImplicit=false', str(probe)],
            cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (BUILD / 'classical-literal-axioms.log').write_text(result.stdout)
    assert result.returncode == 0, result.stdout
    checks.check_axiom_output(result.stdout, {
        THEOREM, 'WuPaper.ClassicalSlots.one894', 'WuPaper.ClassicalSlots.classical_lower',
        'WuLiteralAcceptance', 'WuLegacyLiteralAcceptance'})
    assert sha(ROOT / 'source-manifest.json') == manifest_hash, 'Manifest changed'
    assert verify_build() == before, 'Build objects changed during acceptance'
    report = {'status': 'pass', 'theorem': THEOREM, 'legacy_theorem': 'WuPaper.ClassicalSlots.one894', 'modules': len(before),
              'manifest_sha256': manifest_hash, 'literal_probe_sha256':
              hashlib.sha256(PROBE.encode()).hexdigest(),
              'log': 'build/classical-literal-axioms.log'}
    (BUILD / 'classical-acceptance.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
