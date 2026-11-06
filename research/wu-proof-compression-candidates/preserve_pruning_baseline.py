#!/usr/bin/env python3
"""Preserve the accepted baseline before a future atomic source adoption.

Sources/receipts/logs are copied; compiled artifacts use verified hard links.
This does not change the accepted tree or install the candidate.
"""

import argparse
import json
import os
import shutil
from pathlib import Path

from audit_completed_batch import EXTENSIONS, audit, digest, sha


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--candidate-run', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    run, output = args.candidate_run.resolve(), args.output_dir.resolve()
    assert not output.exists()
    here = Path(__file__).resolve().parent
    canonical = here.parent / 'wu2008'
    pre = json.loads((run / 'preflight.json').read_text())
    shared_run = Path(pre['baseline'])
    shared_pre = json.loads((shared_run / 'preflight.json').read_text())
    assert sha(canonical / 'source-manifest.json') == shared_pre['baseline_manifest_sha256']
    before = audit(shared_run, canonical)
    assert before['context_digest'] == pre['baseline_context_digest']
    rows = json.loads((canonical / 'source-manifest.json').read_text())
    manifest = {r['module']: r for r in rows}
    receipts, objects = {}, {}
    for name, row in manifest.items():
        relative = Path(*name.split('.'))
        source = (canonical / 'src' / relative).with_suffix('.lean')
        obj = (canonical / 'build/lib' / relative).with_suffix('.olean')
        receipt = (canonical / 'build/receipts' / relative).with_suffix('.json')
        r = json.loads(receipt.read_text())
        assert r['exit_code'] == 0 and type(r['exit_code']) is int
        assert sha(source) == row['source_sha256'] == r['source_sha256'], name
        objects[name] = sha(obj)
        assert objects[name] == r['object_sha256'], name
        assert sha(canonical / r['log']) == r['log_sha256'], name
        receipts[name] = r
    for name, row in manifest.items():
        r = receipts[name]
        dependencies = {d: objects[d] for d in row['imports'] if d in manifest}
        contexts = {d: receipts[d]['context_sha256'] for d in dependencies}
        assert r['dependencies'] == dependencies and r['dependency_contexts'] == contexts, name
        assert r['context_sha256'] == digest(dict(source_sha256=r['source_sha256'], object_sha256=r['object_sha256'], dependency_contexts=contexts)), name
    output.mkdir(parents=True)
    inventory = {}

    def copy(source, relative, link=False):
        destination = output / relative
        if destination.exists():
            assert sha(destination) == sha(source)
            return
        destination.parent.mkdir(parents=True, exist_ok=True)
        if link:
            os.link(source, destination)
        else:
            shutil.copyfile(source, destination)
        assert sha(source) == sha(destination)
        inventory[str(relative)] = dict(sha256=sha(destination), hard_linked=link)

    for name, row in manifest.items():
        relative = Path(*name.split('.'))
        copy((canonical / 'src' / relative).with_suffix('.lean'), (Path('src') / relative).with_suffix('.lean'))
        copy((canonical / 'build/receipts' / relative).with_suffix('.json'), (Path('build/receipts') / relative).with_suffix('.json'))
        copy(canonical / receipts[name]['log'], Path(receipts[name]['log']))
        for extension in EXTENSIONS:
            source = (canonical / 'build/lib' / relative).with_suffix(extension)
            if source.exists():
                copy(source, (Path('build/lib') / relative).with_suffix(extension), link=True)
    for name in ['source-manifest.json', 'build.py', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'roots.json', 'mathematical-status.json']:
        copy(canonical / name, Path(name))
    after = audit(shared_run, output)
    assert after == before
    assert sha(canonical / 'source-manifest.json') == sha(output / 'source-manifest.json')
    result = dict(status='ACCEPTED_BASELINE_PRESERVED_CANDIDATE_NOT_INSTALLED', baseline=str(canonical), snapshot=str(output), manifest_sha256=sha(output / 'source-manifest.json'), verified_modules=len(manifest), shared_candidate_context_digest=before['context_digest'], source_receipts_logs_are_independent_copies=True, artifact_links_require_atomic_replacement_on_future_installation=True, canonical_unchanged=True, inventory=inventory, preparer_sha256=sha(Path(__file__)))
    (output / 'snapshot-review.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'inventory'}))


if __name__ == '__main__':
    main()
