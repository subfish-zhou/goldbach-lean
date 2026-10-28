#!/usr/bin/env python3
"""Compile isolated Li-Liu audit experiments without editing production sources."""
from pathlib import Path
import argparse
import concurrent.futures
import hashlib
import json
import os
import subprocess

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    inputs = json.loads((HERE / 'source-inputs.json').read_text())
    for relative, expected in inputs.items():
        assert digest(ROOT / relative) == expected, relative
    jobs = {}
    for name in ['CountToExistence', 'StrongToWeak']:
        source = HERE / 'experiments' / (name + '.lean')
        target = output / source.name
        target.write_bytes(source.read_bytes())
        jobs[name] = target
    reductions = json.loads((HERE / 'experiments/import-reductions.json').read_text())
    for name, spec in reductions.items():
        source = ROOT / spec['source']
        assert digest(source) == spec['source_sha256'], spec['source']
        text = source.read_text()
        assert text.count(spec['before']) == 1, spec['source']
        target = output / (name + '.lean')
        target.write_text(text.replace(spec['before'], spec['after']))
        jobs[name] = target
    env = os.environ.copy()
    env.pop('LEAN_PATH', None)
    env.pop('LEAN_SRC_PATH', None)
    env['LEAN_NUM_THREADS'] = '2'

    def run(item):
        name, source = item
        cmd = ['lake', 'env', 'lean', '-DwarningAsError=true', str(source)]
        log = output / (name + '.log')
        with log.open('w') as handle:
            code = subprocess.run(cmd, cwd=ROOT, env=env, stdout=handle,
                                  stderr=subprocess.STDOUT).returncode
        return name, {'exit_code': code, 'command': cmd,
                      'source_sha256': digest(source), 'log_sha256': digest(log)}

    with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
        results = dict(pool.map(run, jobs.items()))
    for relative, expected in inputs.items():
        assert digest(ROOT / relative) == expected, relative
    report = {'status': 'pass' if all(r['exit_code'] == 0 for r in results.values()) else 'fail',
              'scope': 'Five isolated compilations; production proof sources and their import graph are unchanged. This is not a post-cleanup whole-project acceptance.',
              'checks': results,
              'input_manifest_sha256': digest(HERE / 'source-inputs.json')}
    (output / 'validation.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
    assert report['status'] == 'pass', results


if __name__ == '__main__':
    main()
