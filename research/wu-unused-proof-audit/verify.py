#!/usr/bin/env python3
"""Check archived evidence integrity and current sources; does not execute Lean."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import tarfile


def main():
    here = Path(__file__).resolve().parent
    repo = here.parents[1]
    sha = lambda data: hashlib.sha256(data).hexdigest()
    report = json.loads((here / 'validation.json').read_text())
    assert report['status'] == 'ACCEPTED_INSTALLED_UNUSED_PROOF_PRUNING'
    for name, expected in report['bindings'].items():
        assert sha((here / name).read_bytes()) == expected, name
    index = json.loads((here / 'historical-evidence-index.json').read_text())
    seen = set()
    with tarfile.open(here / 'historical-evidence.tar.gz', 'r:gz') as archive:
        for item in archive:
            assert item.isfile() and item.name in index and item.name not in seen
            seen.add(item.name)
            data = archive.extractfile(item).read()
            assert len(data) == index[item.name]['bytes']
            assert sha(data) == index[item.name]['sha256'], item.name
    assert seen == set(index)
    gates = json.loads((here / 'isolated/report.json').read_text())
    assert len(gates['steps']) == 30 and gates['kernels'] == 21
    assert gates['retired_absent'] == 2119
    for step in gates['steps']:
        expected = 1 if step['label'] == 'retirement-before-negative' else 0
        assert type(step['exit_code']) is int and step['exit_code'] == expected
        for suffix, key in [('.log', 'log_sha256'),
                            ('.resources', 'resources_sha256'),
                            ('.invocation.json', 'invocation_sha256')]:
            assert sha((here / 'isolated' / (step['label'] + suffix)).read_bytes()) == step[key]
    before = (here / 'isolated/context-before.json').read_bytes()
    assert before == (here / 'isolated/context-after.json').read_bytes()
    current = json.loads(subprocess.check_output(
        [sys.executable, str(here / 'measure.py'), '--repo', str(repo)], text=True))
    assert current == json.loads((here / 'measurement.json').read_text())
    assert current['manifest_sha256'] == report['manifest_sha256']
    production = json.loads((here / 'production-verification.json').read_text())
    assert len(production['steps']) == 5
    for step in production['steps']:
        assert type(step['exit_code']) is int and step['exit_code'] == 0
        assert sha((here / (step['label'] + '.log')).read_bytes()) == step['log_sha256']
    assert (here / 'production-build.log').read_text().strip() == 'BUILD_PASS 4151'
    print('ARCHIVED_EVIDENCE_AND_CURRENT_SOURCES_PASS; Lean is not rerun')


if __name__ == '__main__':
    main()
