#!/usr/bin/env python3
"""Verify a published acceptance archive and installed sources; do not run Lean.

Compiled local artifacts can additionally be compared with the recorded context.
This verifier never promotes an incomplete or merely local compile to acceptance.
"""

import argparse
import hashlib
import importlib.util
import json
import re
import tarfile
from pathlib import Path


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def verify(directory, repo, local_artifacts=False):
    report = json.loads((directory / 'validation.json').read_text())
    assert report['status'] == 'ACCEPTED_INSTALLED_PRUNING_AND_MAX_ENVELOPE_COMPRESSION'
    for relative, expected in report['bindings'].items():
        path = directory / relative
        assert not Path(relative).is_absolute() and '..' not in Path(relative).parts
        assert sha(path) == expected, relative
    index = json.loads((directory / 'historical-evidence-index.json').read_text())
    seen = set()
    with tarfile.open(directory / 'historical-evidence.tar.gz', 'r:gz') as archive:
        for member in archive:
            assert member.isfile() and member.name in index and member.name not in seen
            seen.add(member.name)
            data = archive.extractfile(member).read()
            assert len(data) == index[member.name]['bytes']
            assert hashlib.sha256(data).hexdigest() == index[member.name]['sha256']
    assert seen == set(index)
    isolated = directory / 'isolated'
    gates = json.loads((isolated / 'report.json').read_text())
    assert gates['status'] == 'PRUNING_FULL_CONTEXT_TYPES_VALUES_LITERALS_RETIREMENTS_FRESH_UNION_PRODUCERS_PASS_NOT_INSTALLED'
    plan = json.loads((isolated / 'validation-plan.json').read_text())
    assert sha(isolated / 'validation-plan.json') == gates['plan_sha256']
    assert len(gates['steps']) == len(plan['steps']) == 10
    assert [r['label'] for r in gates['steps']] == [r['label'] for r in plan['steps']]
    for step, planned in zip(gates['steps'], plan['steps']):
        assert type(step['exit_code']) is int and step['exit_code'] == planned['expected_exit_code'] == 0
        label = step['label']
        for suffix, key in [('.log', 'log_sha256'), ('.resources', 'resources_sha256'), ('.invocation.json', 'invocation_sha256')]:
            assert sha(isolated / (label + suffix)) == step[key]
        invocation = json.loads((isolated / (label + '.invocation.json')).read_text())
        assert invocation['command'] == planned['command']
        if step.get('payload_sha256'):
            assert sha(isolated / (label + '.json')) == step['payload_sha256']
    fresh = next(s for s in plan['steps'] if s['label'] == 'fresh-kernel-union')
    assert fresh['command'] == [str(Path(plan['lean']).with_name('leanchecker')), '--verbose', '--fresh', plan['fresh_kernel_module']]
    assert (isolated / 'fresh-kernel-union.log').read_text().strip() == 'replaying ' + plan['fresh_kernel_module'] + ' with --fresh'
    before = json.loads((isolated / 'context-before.json').read_text())
    after = json.loads((isolated / 'context-after.json').read_text())
    assert before == after and before['context_digest'] == gates['context_digest']
    assert digest(before['facts']) == before['context_digest']
    assert before['modules'] == len(before['facts']) == 4151
    assert before['fresh_source_compilations'] == gates['fresh_source_compilations'] == 3911
    assert before['verified_unchanged'] == gates['verified_unchanged'] == 240
    absence = json.loads((isolated / 'retirement-after-absent.json').read_text())
    assert absence['schema'] == 'wu-retired-declaration-absence-v1'
    assert absence['status'] == 'RAW_PRIVATE_INCLUSIVE_RETIREMENT_ABSENCE_NOT_PROOF_ACCEPTANCE'
    assert absence['requestedCount'] == absence['absentCount'] == gates['retired_names_absent'] == plan['retirement_targets'] == 6386
    assert absence['expectedResearchModules'] == 4151
    assert len(plan['comparisons']) == 4
    assert sorted(pair['count'] for pair in plan['comparisons']) == [1, 33, 183, 696]
    for pair in plan['comparisons']:
        reference = directory / 'references' / (pair['label'] + '.json')
        actual = isolated / (pair['label'] + '.json')
        a, b = json.loads(reference.read_text()), json.loads(actual.read_text())
        assert a == b
        step = next(s for s in gates['steps'] if s['label'] == pair['label'])
        assert sha(reference) == step['reference_sha256']
        assert len(a['declarations'] if pair['format'] == 'declarations' else a) == pair['count']
    production = json.loads((directory / 'production-verification.json').read_text())
    assert production['status'] == 'INSTALLED_CONTEXT_AND_FOUR_PRODUCTION_CHECKS_PASS_ACCEPTANCE_DOCUMENTATION_PENDING'
    assert production['source_compilations_during_installation'] == 0
    assert production['context_digest'] == before['context_digest']
    assert len(production['steps']) == 4
    for step in production['steps']:
        assert type(step['exit_code']) is int and step['exit_code'] == 0
        assert sha(directory / (step['label'] + '.log')) == step['log_sha256']
    assert (directory / 'production-cache-check.log').read_text().strip() == 'BUILD_PASS 4151'
    root = repo / 'research/wu2008'
    assert sha(root / 'source-manifest.json') == report['manifest_sha256'] == production['installed_manifest_sha256']
    counter_path = repo / 'scripts/check.py'
    spec = importlib.util.spec_from_file_location('accepted_source_counter', counter_path)
    counter = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(counter)
    counter.check_axiom_output((isolated / 'literal-axioms.log').read_text(), {'WuPaper.ClassicalSlots.one8938', 'WuPaper.ClassicalSlots.one894', 'WuPaper.ClassicalSlots.classical_lower', 'WuLiteralAcceptance', 'WuLegacyLiteralAcceptance'})
    counter.check_axiom_output((isolated / 'after-selberg-type.log').read_text(), {'MathlibNt.SieveTheory.SelbergUpperBound.mainSum_cauchy_schwarz_lower_bound'})
    rows = json.loads((root / 'source-manifest.json').read_text())
    names = {r['module'] for r in rows}
    assert len(names) == len(rows) == 4151 and names == set(before['facts'])
    counts, graph = {}, {}
    facts = before['facts']
    for row in rows:
        name = row['module']
        relative = Path(*name.split('.'))
        source = (root / 'src' / relative).with_suffix('.lean')
        assert sha(source) == row['source_sha256'] == facts[name]['source'], name
        raw = source.read_bytes()
        text = raw.decode()
        counts[name] = dict(code_lines=counter.count_code_lines(text), physical_lines=len(text.splitlines()), utf8_bytes=len(raw))
        actual = [word for m in re.finditer(r'^\s*(?:(?:public|meta)\s+)*import\s+(.+)', counter.code_only(text), re.M) for word in m[1].split() if word in names]
        graph[name] = [n for n in row['imports'] if n in names]
        assert actual == graph[name], name
        if local_artifacts:
            obj = (root / 'build/lib' / relative).with_suffix('.olean')
            receipt = (root / 'build/receipts' / relative).with_suffix('.json')
            assert sha(obj) == row['object_sha256'] == facts[name]['object'], name
            assert sha(receipt) == facts[name]['receipt'], name
            saved = json.loads(receipt.read_text())
            assert saved['module'] == name and type(saved['exit_code']) is int and saved['exit_code'] == 0
            assert saved['source_sha256'] == facts[name]['source']
            assert saved['object_sha256'] == facts[name]['object']
            assert sha(root / saved['log']) == saved['log_sha256'] == facts[name]['log']
            assert saved['context_sha256'] == facts[name]['context']
            assert saved['dependencies'] == {d: facts[d]['object'] for d in graph[name]}
            assert saved['dependency_contexts'] == {d: facts[d]['context'] for d in graph[name]}
            assert saved['context_sha256'] == digest(dict(source_sha256=saved['source_sha256'], object_sha256=saved['object_sha256'], dependency_contexts=saved['dependency_contexts']))
            for suffix, expected in facts[name]['bundle'].items():
                assert sha((root / 'build/lib' / relative).with_suffix(suffix)) == expected
    actual_sources = {str(p.relative_to(root / 'src').with_suffix('')).replace('/', '.') for p in (root / 'src').rglob('*.lean')}
    assert actual_sources == names
    closure, todo = set(), ['WR2ClassicalCertificate']
    while todo:
        name = todo.pop()
        if name not in closure:
            closure.add(name)
            todo.extend(graph[name])

    def total(selected):
        return dict(modules=len(selected), **{k: sum(counts[n][k] for n in selected) for k in ['code_lines', 'physical_lines', 'utf8_bytes']})

    sizes = dict(whole_tree=total(names), theorem_closure=total(closure))
    assert sizes == report['source_size']
    print('ARCHIVED_FULL_VALIDATION_AND_CURRENT_SOURCES_PASS; Lean is not rerun' + ('; local compiled artifacts match' if local_artifacts else ''))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit-dir', type=Path, required=True)
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--local-artifacts', action='store_true')
    args = parser.parse_args()
    verify(args.audit_dir.resolve(), args.repo.resolve(), args.local_artifacts)


if __name__ == '__main__':
    main()
