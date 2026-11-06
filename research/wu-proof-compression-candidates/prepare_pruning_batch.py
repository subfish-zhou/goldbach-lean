#!/usr/bin/env python3
"""Freeze the exact mixed-declaration overlay and reuse unaffected artifacts."""

import argparse
import difflib
import json
import os
import shutil
from pathlib import Path

from audit_completed_batch import audit, sha


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--deletions', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--selberg-probe', type=Path)
    args = parser.parse_args()
    deletion_dir, output = args.deletions.resolve(), args.output_dir.resolve()
    assert not output.exists()
    deletion = json.loads((deletion_dir / 'manifest.json').read_text())
    assert deletion['status'] == 'SOURCE_AND_COMPILED_REFERENCE_CLOSED_EXACT_OVERLAY_UNCOMPILED_NOT_ADOPTED'
    for p, h in deletion['bindings'].items():
        assert sha(Path(p)) == h, p
    baseline = Path(deletion['baseline_run'])
    original = Path(__file__).resolve().parent.parent / 'wu2008'
    context = audit(baseline, original)
    assert context['context_digest'] == deletion['context_digest']
    rows = json.loads((baseline / 'source-manifest.json').read_text())
    manifest = {r['module']: r for r in rows}
    changes, records = {}, {}
    for row in deletion['files']:
        name = row['module']
        path = deletion_dir / 'overlay' / row['file']
        assert sha(path) == row['after_sha256'] and manifest[name]['source_sha256'] == row['before_sha256']
        changes[name] = path.read_text()
        records[name] = dict(before_sha256=row['before_sha256'], after_sha256=row['after_sha256'], deletion_count=len(row['deletions']))
    extra = None
    if args.selberg_probe:
        probe = args.selberg_probe.resolve()
        result = json.loads((probe / 'probe-resume-result.json').read_text())
        assert result['status'] == 'SINGLE_CHANGED_MODULE_COMPILE_AND_EXACT_TYPE_AXIOMS_PASS_NO_DOWNSTREAM_ACCEPTANCE'
        assert result['context_digest'] == context['context_digest']
        plan = json.loads((probe / 'probe-plan.json').read_text())
        for p, h in plan['bindings'].items():
            assert sha(Path(p)) == h, p
        spec = json.loads(Path(plan['candidate']).read_text())
        name = spec['module']
        relative = Path(*name.split('.')).with_suffix('.lean')
        source = (baseline / 'src' / relative).read_text()
        candidate = (probe / 'src' / relative).read_text()
        assert sha(baseline / 'src' / relative) == spec['before_sha256']
        assert sha(probe / 'src' / relative) == spec['after_sha256']
        # Apply only the shared-proof hunk, after the independent deletions.
        a, b = source.splitlines(keepends=True), candidate.splitlines(keepends=True)
        text = changes.get(name, source)
        hunks = []
        for tag, i, j, k, l in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
            if tag == 'equal':
                continue
            before, after = ''.join(a[i:j]), ''.join(b[k:l])
            assert before and text.count(before) == 1
            text = text.replace(before, after, 1)
            hunks.append(dict(before=before, after=after))
        assert len(hunks) == 1
        changes[name] = text
        extra = dict(module=name, probe_result=str(probe / 'probe-resume-result.json'), probe_result_sha256=sha(probe / 'probe-resume-result.json'), hunks=hunks)
        records.setdefault(name, dict(before_sha256=spec['before_sha256'], deletion_count=0))['shared_proof_hunk'] = True
    affected = set(changes)
    while True:
        expanded = affected | {n for n, r in manifest.items() if affected.intersection(r['imports'])}
        if expanded == affected:
            break
        affected = expanded
    needed = sum((baseline / 'build/lib' / Path(*n.split('.'))).with_suffix('.olean').stat().st_size for n in affected)
    assert shutil.disk_usage(output.parent).free > needed + 700_000_000
    output.mkdir(parents=True)
    cached, bundles = {}, {}
    for name, row in manifest.items():
        relative = Path(*name.split('.'))
        source = (baseline / 'src' / relative).with_suffix('.lean')
        dest = (output / 'src' / relative).with_suffix('.lean')
        dest.parent.mkdir(parents=True, exist_ok=True)
        if name in changes:
            dest.write_text(changes[name])
            row['source_sha256'] = sha(dest)
            row['source_binding'] = 'isolated_mixed_pruning_and_shared_proof_not_accepted'
            records[name]['after_sha256'] = sha(dest)
        else:
            shutil.copyfile(source, dest)
        dest.chmod(0o444)
        if name in affected:
            continue
        bundle = {}
        for extension in ['.olean', '.olean.server', '.olean.private', '.ir', '.ir.sig']:
            src = (baseline / 'build/lib' / relative).with_suffix(extension)
            if src.exists():
                target = (output / 'build/lib' / relative).with_suffix(extension)
                target.parent.mkdir(parents=True, exist_ok=True)
                os.link(src, target)
                bundle[extension] = sha(src)
        cached[name], bundles[name] = bundle['.olean'], bundle
        src = (baseline / 'build/receipts' / relative).with_suffix('.json')
        target = (output / 'build/receipts' / relative).with_suffix('.json')
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(src, target)
    save(output / 'source-manifest.json', rows)
    for name in ['build.py', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'roots.json']:
        shutil.copyfile(baseline / name, output / name)
    (output / '.lake').mkdir()
    (output / '.lake/packages').symlink_to((baseline / '.lake/packages').resolve())
    preflight = dict(status='FROZEN_INCREMENTAL_MIXED_PRUNING_NOT_BUILT_OR_INSTALLED', baseline=str(baseline), baseline_manifest_sha256=sha(baseline / 'source-manifest.json'), baseline_context_digest=context['context_digest'], candidate_manifest_sha256=sha(output / 'source-manifest.json'), modules=len(rows), changed_modules=sorted(changes), affected_names=sorted(affected), affected_modules=len(affected), cached_modules=len(cached), unaffected_object_hashes=cached, cached_artifact_bundles=bundles, candidate_records=records, builder_sha256=sha(output / 'build.py'), deletions_manifest=str(deletion_dir / 'manifest.json'), deletions_manifest_sha256=sha(deletion_dir / 'manifest.json'), extra_shared_proof=extra, required_estimated_object_bytes=needed, preparer_sha256=sha(Path(__file__)))
    save(output / 'preflight.json', preflight)
    print(json.dumps({k: preflight[k] for k in ['status', 'modules', 'affected_modules', 'cached_modules', 'candidate_manifest_sha256']}))


if __name__ == '__main__':
    main()
