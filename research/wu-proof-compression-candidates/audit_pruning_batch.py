#!/usr/bin/env python3
"""Check a terminal mixed-pruning build, including recursive cache provenance.

No compilation, interface/kernel validation, or installation is performed here.
"""

import argparse
import json
from pathlib import Path

from audit_completed_batch import EXTENSIONS, audit, digest, sha


def audit_pruning(run):
    state = json.loads((run / 'process.json').read_text())
    status = json.loads((run / 'build/STATUS.json').read_text())
    if state.get('exit_code') != 0 or status.get('status') != 'passed':
        raise ValueError('Pruning build is not terminal and fully passed; no context acceptance')
    preflight = json.loads((run / 'preflight.json').read_text())
    assert sha(run / 'preflight.json') == state['preflight_sha256']
    baseline = Path(preflight['baseline'])
    canonical = Path(__file__).resolve().parent.parent / 'wu2008'
    prior = audit(baseline, canonical)
    assert prior['context_digest'] == preflight['baseline_context_digest']
    assert sha(baseline / 'source-manifest.json') == preflight['baseline_manifest_sha256']
    assert sha(run / 'source-manifest.json') == preflight['candidate_manifest_sha256']
    assert sha(Path(preflight['deletions_manifest'])) == preflight['deletions_manifest_sha256']
    manifest = {r['module']: r for r in json.loads((run / 'source-manifest.json').read_text())}
    original = {r['module']: r for r in json.loads((baseline / 'source-manifest.json').read_text())}
    plan = json.loads((run / 'build/PLAN.json').read_text())
    order = plan['modules']
    assert len(order) == len(set(order)) == len(manifest) == status['verified'] == status['planned'] == 4151
    assert set(order) == set(manifest) == set(original)
    assert plan['lean_threads'] == 1
    assert sha(run / 'build.py') == sha(baseline / 'build.py') == preflight['builder_sha256']
    for name in ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain']:
        assert sha(run / name) == sha(baseline / name)
    for directory, suffix in [('src', '.lean'), ('build/lib', '.olean')]:
        actual = {str(p.relative_to(run / directory).with_suffix('')).replace('/', '.') for p in (run / directory).rglob('*' + suffix)}
        assert actual == set(manifest), directory
    changes = set(preflight['changed_modules'])
    assert changes == set(preflight['candidate_records'])
    import_changes = preflight.get('import_changes', {})
    assert set(import_changes) <= changes
    affected = set(changes)
    while True:
        expanded = affected | {n for n, r in manifest.items() if affected.intersection(r['imports'])}
        if expanded == affected:
            break
        affected = expanded
    assert affected == set(preflight['affected_names']) and len(affected) == preflight['affected_modules']
    assert set(preflight['unaffected_object_hashes']) == set(manifest) - affected
    facts = {}
    for name in order:
        row = manifest[name]
        if name in import_changes:
            assert original[name]['imports'] == import_changes[name]['before'], name
            assert row['imports'] == import_changes[name]['after'], name
        else:
            assert row['imports'] == original[name]['imports'], name
        relative = Path(*name.split('.'))
        source = (run / 'src' / relative).with_suffix('.lean')
        if name in import_changes:
            import re
            actual = re.findall(r'^import ([A-Za-z_][\w.]*)\s*$', source.read_text(), re.M)
            assert actual == [n for n in row['imports'] if n != 'Init'], name
        obj = (run / 'build/lib' / relative).with_suffix('.olean')
        receipt = (run / 'build/receipts' / relative).with_suffix('.json')
        r = json.loads(receipt.read_text())
        assert r['module'] == name and type(r['exit_code']) is int and r['exit_code'] == 0, name
        source_hash, object_hash = sha(source), sha(obj)
        assert source_hash == row['source_sha256'] == r['source_sha256'], name
        assert object_hash == r['object_sha256'], name
        if name in changes:
            candidate = preflight['candidate_records'][name]
            assert original[name]['source_sha256'] == candidate['before_sha256']
            assert source_hash == candidate['after_sha256']
        else:
            assert source_hash == original[name]['source_sha256'], name
        dependencies = {d: facts[d]['object'] for d in row['imports'] if d in manifest}
        contexts = {d: facts[d]['context'] for d in dependencies}
        assert r['dependencies'] == dependencies and r['dependency_contexts'] == contexts, name
        context = digest(dict(source_sha256=source_hash, object_sha256=object_hash, dependency_contexts=contexts))
        assert context == r['context_sha256'], name
        bundle = {ext: sha((run / 'build/lib' / relative).with_suffix(ext)) for ext in EXTENSIONS if (run / 'build/lib' / relative).with_suffix(ext).exists()}
        if name in affected:
            command = [prior['lean'], '-j1', '-DwarningAsError=true', '-R', str(run / 'src'), '-o', str(obj)]
            if name.startswith(('W', 'R2')):
                command.append('-DautoImplicit=false')
            command.append(str(source))
            assert r['command'] == command, name
            log = run / r['log']
            assert sha(log) == r['log_sha256'], name
            assert json.loads(log.with_suffix('.json').read_text()) == r, name
        else:
            previous = prior['facts'][name]
            assert sha(receipt) == previous['receipt'], name
            assert object_hash == previous['object'] == preflight['unaffected_object_hashes'][name], name
            assert bundle == previous['bundle'] == preflight['cached_artifact_bundles'][name], name
            assert r['log_sha256'] == previous['log'], name
        facts[name] = dict(source=source_hash, object=object_hash, context=context, bundle=bundle, receipt=sha(receipt), log=r['log_sha256'])
    assert Path(state['log']).read_text().splitlines()[-1] == 'BUILD_PASS 4151'
    assert sha(run / 'source-manifest.json') == preflight['candidate_manifest_sha256']
    return dict(status='COMPLETE_PRUNING_SOURCE_OBJECT_LOG_RECURSIVE_CONTEXT_AUDIT_NOT_ACCEPTANCE', modules=len(facts), fresh_source_compilations=len(affected), verified_unchanged=len(manifest) - len(affected), manifest_sha256=preflight['candidate_manifest_sha256'], context_digest=digest(facts), lean=prior['lean'], package_paths=plan['package_paths'], baseline_context_digest=prior['context_digest'], facts=facts)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = audit_pruning(args.run.resolve())
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'facts'}))


if __name__ == '__main__':
    main()
