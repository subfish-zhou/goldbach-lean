#!/usr/bin/env python3
"""Count manifest-bound candidate sources without claiming proof acceptance."""

import argparse
import importlib.util
import json
from pathlib import Path

from audit_completed_batch import sha


def measure(root, counter):
    rows = json.loads((root / 'source-manifest.json').read_text())
    manifest = {r['module']: r for r in rows}
    assert len(manifest) == len(rows)
    counts = {}
    for name, row in manifest.items():
        source = root / 'src' / Path(*name.split('.')).with_suffix('.lean')
        assert sha(source) == row['source_sha256'], name
        raw = source.read_bytes()
        text = raw.decode()
        counts[name] = dict(code_lines=counter.count_code_lines(text), physical_lines=len(text.splitlines()), utf8_bytes=len(raw))
    actual = {str(p.relative_to(root / 'src').with_suffix('')).replace('/', '.') for p in (root / 'src').rglob('*.lean')}
    assert actual == set(manifest)
    closure, todo = set(), ['WR2ClassicalCertificate']
    while todo:
        name = todo.pop()
        if name in manifest and name not in closure:
            closure.add(name)
            todo.extend(manifest[name]['imports'])

    def total(names):
        return dict(modules=len(names), **{k: sum(counts[n][k] for n in names) for k in ['code_lines', 'physical_lines', 'utf8_bytes']})

    return dict(manifest_sha256=sha(root / 'source-manifest.json'), whole_tree=total(set(manifest)), theorem_closure=total(closure))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--baseline', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    counter_path = Path(__file__).resolve().parents[2] / 'scripts/check.py'
    spec = importlib.util.spec_from_file_location('published_source_counter', counter_path)
    counter = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(counter)
    baseline, candidate = args.baseline.resolve(), args.run.resolve()
    before, after = measure(baseline, counter), measure(candidate, counter)
    delta = {scope: {k: before[scope][k] - after[scope][k] for k in ['code_lines', 'physical_lines', 'utf8_bytes']} for scope in ['whole_tree', 'theorem_closure']}
    result = dict(status='ACTUAL_FROZEN_CANDIDATE_SOURCE_MEASUREMENT_NOT_BUILD_OR_INSTALLATION_ACCEPTANCE', baseline=str(baseline), candidate=str(candidate), before=before, after=after, candidate_source_savings=delta, counter_sha256=sha(counter_path), measurement_tool_sha256=sha(Path(__file__)), metric='Whole local imported modules; published count_code_lines; strings retained; external packages excluded')
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
