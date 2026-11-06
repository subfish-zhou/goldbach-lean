#!/usr/bin/env python3
"""Adopt only a fully validated candidate; default is a read-only preflight.

The accepted atomic transaction engine is reused with artifact-link rollback.
No fresh source compilation or repeated full kernel replay occurs on adoption.
"""

import argparse
import fcntl
import importlib.util
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import time
from pathlib import Path

from audit_completed_batch import EXTENSIONS, digest, sha
from audit_pruning_batch import audit_pruning
from pruning_transaction import load_engine
from validate_completed_batch import review_pins


SUCCESS = 'PRUNING_FULL_CONTEXT_TYPES_VALUES_LITERALS_RETIREMENTS_FRESH_UNION_PRODUCERS_PASS_NOT_INSTALLED'


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def collect(run, validation, snapshot):
    state = json.loads((run / 'process.json').read_text())
    status = json.loads((run / 'build/STATUS.json').read_text())
    if state.get('exit_code') != 0 or status.get('status') != 'passed':
        raise ValueError('Pruning build is not terminal and fully passed; adoption not prepared')
    plan = json.loads((validation / 'validation-plan.json').read_text())
    report = json.loads((validation / 'report.json').read_text())
    assert Path(plan['run']) == run and report['status'] == SUCCESS
    assert sha(validation / 'validation-plan.json') == report['plan_sha256']
    assert [r['label'] for r in report['steps']] == [r['label'] for r in plan['steps']]
    assert len(report['steps']) == 10
    for p, h in report['bindings'].items():
        assert sha(Path(p)) == h, p
    for row, step in zip(report['steps'], plan['steps']):
        assert type(row['exit_code']) is int and row['exit_code'] == step['expected_exit_code'] == 0
        for suffix, key in [('.log', 'log_sha256'), ('.resources', 'resources_sha256'), ('.invocation.json', 'invocation_sha256')]:
            assert sha(validation / (row['label'] + suffix)) == row[key]
        invocation = json.loads((validation / (row['label'] + '.invocation.json')).read_text())
        assert invocation['command'] == step['command']
        assert invocation['environment']['LEAN_PATH'] == ':'.join([step['library'], *plan['package_paths']])
    for pair in plan['comparisons']:
        reference = json.loads(Path(pair['reference']).read_text())
        actual = json.loads((validation / (pair['label'] + '.json')).read_text())
        assert actual == reference
    facts = audit_pruning(run)
    assert facts['context_digest'] == report['context_digest']
    assert facts == json.loads((validation / 'context-before.json').read_text()) == json.loads((validation / 'context-after.json').read_text())
    pins = review_pins(plan)
    canonical = Path(plan['baseline'])
    pre = json.loads((run / 'preflight.json').read_text())
    baseline_review = json.loads((snapshot / 'snapshot-review.json').read_text())
    assert baseline_review['status'] == 'ACCEPTED_BASELINE_PRESERVED_CANDIDATE_NOT_INSTALLED'
    assert baseline_review['shared_candidate_context_digest'] == pre['baseline_context_digest']
    assert sha(canonical / 'source-manifest.json') == sha(snapshot / 'source-manifest.json') == baseline_review['manifest_sha256']
    for relative, row in baseline_review['inventory'].items():
        assert sha(snapshot / relative) == row['sha256'] == sha(canonical / relative), relative
    deletion = json.loads(Path(pre['deletions_manifest']).read_text())
    selected = {d['basename'] for f in deletion['files'] for d in f['deletions']}
    repo = canonical.parents[1]
    archival = [repo / 'research/wu2008/history', repo / 'research/wu-hf4-constructive-wip', repo / 'research/wu-hf4-constructive-audit/isolated']
    for name in subprocess.check_output(['rg', '--files', '-g', '*.md', '-g', '*.py', '-g', '*.lean'], cwd=repo, text=True).splitlines():
        path = repo / name
        if path.is_relative_to(canonical / 'src') or any(path.is_relative_to(p) for p in archival):
            continue
        assert not selected.intersection(re.findall(r"[A-Za-z_][\w']*", path.read_text())), name
    rows = json.loads((run / 'source-manifest.json').read_text())
    originals = {r['module']: r for r in json.loads((snapshot / 'source-manifest.json').read_text())}
    for row in rows:
        name = row['module']
        row['object_sha256'] = facts['facts'][name]['object']
        if row['source_sha256'] != originals[name]['source_sha256']:
            row['source_binding'] = 'installed_pruning_source_snapshot'
    needed = 0
    for name, f in facts['facts'].items():
        relative = Path(*name.split('.'))
        for ext, expected in f['bundle'].items():
            old = baseline_review['inventory'].get(str((Path('build/lib') / relative).with_suffix(ext)), {})
            if old.get('sha256') != expected:
                needed += (run / 'build/lib' / relative).with_suffix(ext).stat().st_size
    assert shutil.disk_usage(canonical).free > needed + 100_000_000, 'Insufficient space for independent changed artifacts'
    return dict(plan=plan, report=report, facts=facts, pins=pins, canonical=canonical, manifest=rows, changed_artifact_bytes=needed)


def check_installed(root, value):
    expected = value['facts']['facts']
    rows = json.loads((root / 'source-manifest.json').read_text())
    assert rows == value['manifest']
    for area, suffix in [('src', '.lean'), ('build/lib', '.olean'), ('build/receipts', '.json')]:
        actual = {str(p.relative_to(root / area).with_suffix('')).replace('/', '.') for p in (root / area).rglob('*' + suffix)}
        assert actual == set(expected), area
    for row in rows:
        name = row['module']
        relative = Path(*name.split('.'))
        f = expected[name]
        receipt = (root / 'build/receipts' / relative).with_suffix('.json')
        r = json.loads(receipt.read_text())
        assert sha((root / 'src' / relative).with_suffix('.lean')) == row['source_sha256'] == r['source_sha256'] == f['source']
        assert sha((root / 'build/lib' / relative).with_suffix('.olean')) == row['object_sha256'] == r['object_sha256'] == f['object']
        assert sha(receipt) == f['receipt'] and sha(root / r['log']) == f['log']
        assert r['dependencies'] == {d: expected[d]['object'] for d in row['imports'] if d in expected}
        assert r['dependency_contexts'] == {d: expected[d]['context'] for d in row['imports'] if d in expected}
        assert r['context_sha256'] == f['context'] == digest(dict(source_sha256=f['source'], object_sha256=f['object'], dependency_contexts=r['dependency_contexts']))
        bundle = {ext: sha((root / 'build/lib' / relative).with_suffix(ext)) for ext in EXTENSIONS if (root / 'build/lib' / relative).with_suffix(ext).exists()}
        assert bundle == f['bundle']


def install(run, validation, snapshot, value):
    root, facts = value['canonical'], value['facts']['facts']
    tx = root / 'build/adoptions' / ('mixed-pruning-' + str(time.time_ns()))
    tx.mkdir(parents=True)
    items, names = [], set()

    def stage(relative, origin=None, data=None, artifact=False, track_unchanged=False):
        name = str(relative)
        assert name not in names
        names.add(name)
        target = root / relative
        assert not target.is_symlink() and not target.is_dir()
        old = sha(target) if target.exists() else None
        new = sha(origin) if origin else (__import__('hashlib').sha256(data).hexdigest() if data is not None else None)
        if old == new and not track_unchanged:
            return
        path = tx / 'stage' / relative
        if new is not None:
            path.parent.mkdir(parents=True, exist_ok=True)
            if origin:
                shutil.copyfile(origin, path)
            else:
                path.write_bytes(data)
            assert sha(path) == new
        if old is not None:
            backup = tx / 'backup' / relative
            backup.parent.mkdir(parents=True, exist_ok=True)
            os.link(target, backup)
        items.append(dict(target=name, old_sha256=old, new_sha256=new))

    for name in facts:
        relative = Path(*name.split('.'))
        stage((Path('src') / relative).with_suffix('.lean'), origin=(run / 'src' / relative).with_suffix('.lean'))
        stage((Path('build/receipts') / relative).with_suffix('.json'), origin=(run / 'build/receipts' / relative).with_suffix('.json'))
        for ext in EXTENSIONS:
            source = (run / 'build/lib' / relative).with_suffix(ext)
            stage((Path('build/lib') / relative).with_suffix(ext), origin=source if source.exists() else None, artifact=source.exists())
        receipt = json.loads((run / 'build/receipts' / relative).with_suffix('.json').read_text())
        log_relative = Path(receipt['log'])
        if str(log_relative) not in names:
            origins = [run / log_relative, Path(value['plan']['baseline_run']) / log_relative, root / log_relative]
            source = next(p for p in origins if p.exists() and sha(p) == receipt['log_sha256'])
            stage(log_relative, origin=source)
    stage(Path('source-manifest.json'), data=(json.dumps(value['manifest'], indent=2) + '\n').encode())
    stage(Path('build/PLAN.json'), origin=run / 'build/PLAN.json', track_unchanged=True)
    stage(Path('build/STATUS.json'), origin=run / 'build/STATUS.json', track_unchanged=True)
    for relative in ['build/classical-acceptance.json', 'build/classical-literal-axioms.log']:
        target = root / relative
        if target.exists():
            stage(Path(relative), origin=target, track_unchanged=True)
    core, engine = load_engine(root, [i['target'] for i in items])
    evidence = dict(validation_report=str(validation / 'report.json'), validation_report_sha256=sha(validation / 'report.json'), validated_context_digest=value['facts']['context_digest'], baseline_snapshot=str(snapshot), baseline_snapshot_review_sha256=sha(snapshot / 'snapshot-review.json'), candidate_source_manifest_sha256=sha(run / 'source-manifest.json'), engine=engine, adopter_sha256=sha(Path(__file__)))
    core.save(tx / 'evidence.json', evidence)
    journal = dict(phase='prepared', items=items, evidence_sha256=sha(tx / 'evidence.json'))
    core.save(tx / 'journal.json', journal)
    for item in items:
        target = core.valid_target(item['target'])
        assert (sha(target) if target.exists() else None) == item['old_sha256']
    assert audit_pruning(run) == value['facts']
    core.commit_items(tx, journal, lambda: check_installed(root, value))
    env = os.environ.copy()
    for key in ['LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT']:
        env.pop(key, None)
    steps = []
    commands = [
        ('production-cache-check', [sys.executable, str(root / 'build.py'), '--all', '--jobs', '1', '--lean-threads', '1', '--limit', '0']),
        ('production-literal-axioms', [sys.executable, str(root / 'check_classical.py')]),
        ('production-hf4-producer', [sys.executable, str(root / 'diagnostics/hf4_constructive/produce.py'), '--route', 'constructive', '--output-dir', str(root / 'src'), '--check']),
        ('production-c-eighth-producer', [sys.executable, str(root / 'diagnostics/classical_c_eighth_certificates.py'), '--check', str(root / 'src')]),
    ]
    child = None
    try:
        for label, command in commands:
            log = tx / (label + '.log')
            with log.open('x') as handle:
                child = subprocess.Popen(command, cwd=root, env=env, stdout=handle, stderr=subprocess.STDOUT, start_new_session=True)
                rc = child.wait(timeout=1800)
            steps.append(dict(label=label, command=command, exit_code=rc, log_sha256=sha(log)))
            core.save(tx / 'production-verification.json', dict(status='PRODUCTION_CHECKS_RUNNING', steps=steps))
            assert type(rc) is int and rc == 0, label
            if label == 'production-cache-check':
                assert log.read_text().strip() == 'BUILD_PASS 4151', 'Unexpected source compilation or incomplete cache check'
            check_installed(root, value)
        assert review_pins(value['plan']) == value['pins']
    except BaseException as error:
        if child is not None and child.poll() is None:
            os.killpg(child.pid, signal.SIGKILL)
            child.wait()
        journal.update(phase='rollback_needed', error_type=type(error).__name__, error=str(error))
        core.save(tx / 'journal.json', journal)
        core.restore(tx)
        raise
    result = dict(status='INSTALLED_CONTEXT_AND_FOUR_PRODUCTION_CHECKS_PASS_ACCEPTANCE_DOCUMENTATION_PENDING', steps=steps, source_compilations_during_installation=0, installed_manifest_sha256=sha(root / 'source-manifest.json'), context_digest=value['facts']['context_digest'], transaction=str(tx))
    core.save(tx / 'production-verification.json', result)
    journal.update(phase='production_verified', production_verification_sha256=sha(tx / 'production-verification.json'))
    core.save(tx / 'journal.json', journal)
    print(json.dumps(result))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--validation', type=Path, required=True)
    parser.add_argument('--snapshot', type=Path, required=True)
    parser.add_argument('--execute', action='store_true')
    args = parser.parse_args()
    run, validation, snapshot = args.run.resolve(), args.validation.resolve(), args.snapshot.resolve()
    # Reject incomplete builds before taking the existing builder's lock.
    state = json.loads((run / 'process.json').read_text())
    if state.get('exit_code') != 0:
        raise ValueError('Pruning build is not terminal and fully passed; adoption not prepared')
    with Path('/tmp/wu-lean-exclusive.lock').open('a') as lease:
        fcntl.flock(lease, fcntl.LOCK_EX | fcntl.LOCK_NB)
        value = collect(run, validation, snapshot)
        if args.execute:
            def interrupted(signum, frame):
                raise InterruptedError(f'Pruning adoption interrupted by signal {signum}')
            handlers = {s: signal.getsignal(s) for s in [signal.SIGINT, signal.SIGTERM]}
            for signum in handlers:
                signal.signal(signum, interrupted)
            try:
                install(run, validation, snapshot, value)
            finally:
                for signum, handler in handlers.items():
                    signal.signal(signum, handler)
        else:
            print(json.dumps(dict(status='FULL_ADOPTION_PREFLIGHT_PASS_NOT_INSTALLED', validated_modules=len(value['facts']['facts']), changed_artifact_bytes=value['changed_artifact_bytes'], candidate_manifest_sha256=sha(run / 'source-manifest.json'))))


if __name__ == '__main__':
    main()
