#!/usr/bin/env python3
"""Stage final pruning checks, reusing successful baseline exports as evidence.

The full imported environment is replayed once with leanchecker --fresh.
This preparer executes no Lean command and does not adopt source changes.
"""

import argparse
import json
import re
from pathlib import Path

from audit_completed_batch import sha


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    run, output = args.run.resolve(), args.output_dir.resolve()
    assert not output.exists() and run not in output.parents
    here = Path(__file__).resolve().parent
    canonical = here.parent / 'wu2008'
    preflight_path = run / 'preflight.json'
    preflight = json.loads(preflight_path.read_text())
    prior_dir = Path(preflight['baseline']).parent / 'validation-inputs-02'
    prior_plan = json.loads((prior_dir / 'validation-plan.json').read_text())
    prior_report = json.loads((prior_dir / 'report.json').read_text())
    assert prior_report['status'] == 'FULL_CONTEXT_EXPORTS_LITERALS_RETIREMENT_21_KERNELS_FRESH_UNION_PRODUCERS_PASS_NOT_INSTALLED'
    assert len(prior_report['steps']) == 34
    assert prior_report['context_digest'] == preflight['baseline_context_digest']
    assert sha(run / 'source-manifest.json') == preflight['candidate_manifest_sha256']
    rows = json.loads((run / 'source-manifest.json').read_text())
    manifest = {r['module']: r for r in rows}
    bindings = {}

    def bind(path):
        bindings[str(path)] = sha(path)

    for path in [Path(__file__).resolve(), here / 'validate_pruning_batch.py', here / 'audit_pruning_batch.py', preflight_path, run / 'source-manifest.json', prior_dir / 'validation-plan.json', prior_dir / 'report.json', Path(preflight['deletions_manifest'])]:
        bind(path)
    for name, expected in prior_report['bindings'].items():
        assert sha(Path(name)) == expected, name
    output.mkdir(parents=True)
    lean = prior_plan['lean']
    steps, comparisons = [], []

    def query(label, source, payload=None):
        path = output / (label + '.lean')
        path.write_text(source)
        bind(path)
        steps.append(dict(label=label, command=[lean, '-j1', '-DwarningAsError=true', '-DautoImplicit=false', '-DmaxRecDepth=16384', '-R', str(output), '-o', str(output / (label + '.olean')), str(path)], library=str(run / 'build/lib'), expected_exit_code=0, payload=str(payload) if payload else None))

    def retarget(source, path):
        matches = re.findall(r'IO\.FS\.writeFile ("(?:\\.|[^"\\])*")', source)
        assert len(matches) == 1
        return source.replace(matches[0], json.dumps(str(path)))

    for label, count in [('after-types', 696), ('after-values', 183), ('after-changed-types', 33)]:
        template, reference = prior_dir / (label + '.lean'), prior_dir / (label + '.json')
        assert len(json.loads(reference.read_text())['declarations']) == count
        bind(template)
        bind(reference)
        destination = output / (label + '.json')
        query(label, retarget(template.read_text(), destination), destination)
        comparisons.append(dict(label=label, reference=str(reference), count=count, format='declarations'))
    extra = preflight['extra_shared_proof']
    probe_result = Path(extra['probe_result'])
    assert sha(probe_result) == extra['probe_result_sha256']
    probe = json.loads(probe_result.read_text())
    assert probe['status'] == 'SINGLE_CHANGED_MODULE_COMPILE_AND_EXACT_TYPE_AXIOMS_PASS_NO_DOWNSTREAM_ACCEPTANCE'
    assert probe['context_digest'] == preflight['baseline_context_digest']
    bind(probe_result)
    reference, template = probe_result.parent / 'after-types.json', probe_result.parent / 'after-types.lean'
    assert sha(reference) == probe['after_type_sha256'] and len(json.loads(reference.read_text())) == 1
    bind(template)
    bind(reference)
    label, destination = 'after-selberg-type', output / 'after-selberg-type.json'
    query(label, retarget(template.read_text(), destination), destination)
    comparisons.append(dict(label=label, reference=str(reference), count=1, format='array'))
    literal = prior_dir / 'literal-axioms.lean'
    bind(literal)
    query('literal-axioms', literal.read_text())

    deletion = json.loads(Path(preflight['deletions_manifest']).read_text())
    chosen = {d['runtime_name'] for f in deletion['files'] for d in f['deletions']}
    census_path = Path('/tmp/wu-next-mixed-family-census-v1/census.json')
    census_result = json.loads(census_path.with_name('execution-result.json').read_text())
    assert sha(census_path) == census_result['payload_sha256']
    assert census_result['context_digest'] == preflight['baseline_context_digest']
    census = json.loads(census_path.read_text())
    targets = {(r['name'], r['module']) for r in census['members'] if r['family'] in chosen}
    targets.update(tuple(pair) for pair in prior_plan['retirement_targets'])
    if preflight.get('extra_retirement_census'):
        extra_census = Path(preflight['extra_retirement_census'])
        extra_result = Path(preflight['extra_retirement_result'])
        result = json.loads(extra_result.read_text())
        assert result['status'] == 'ACTUAL_EXTRA_W08_RETIREMENT_FAMILIES_PASS_NOT_SOURCE_ACCEPTANCE' and result['exit_code'] == 0
        assert sha(extra_census) == result['payload_sha256']
        assert result['context_digest'] == preflight['baseline_context_digest']
        extra = json.loads(extra_census.read_text())
        assert extra['candidateCount'] == 84 and extra['modules'] == 4151
        targets.update((r['name'], r['module']) for r in extra['members'])
        targets.update((r['name'], r['module']) for r in extra['ownershipIssues'])
        bind(extra_census)
        bind(extra_result)
        for name, expected in result['input_bindings'].items():
            assert sha(Path(name)) == expected
            bind(Path(name))
    assert len(chosen) == deletion['selected_declarations'] and chosen <= {n for n, _ in targets}
    roots = prior_plan['kernel_roots']
    covered, todo = set(), list(roots)
    while todo:
        name = todo.pop()
        if name in manifest and name not in covered:
            covered.add(name)
            todo.extend(manifest[name]['imports'])
    assert covered == set(manifest) and len(covered) == 4151
    module_file, request_file = output / 'retirement-modules.txt', output / 'retirement-targets.tsv'
    module_file.write_text('\n'.join(sorted(manifest)) + '\n')
    request_file.write_text(''.join(n + '\t' + owner + '\n' for n, owner in sorted(targets)))
    template_path = here.parent / 'wu-unused-proof-audit/RetiredAbsentTemplate.lean'
    for path in [census_path, census_path.with_name('execution-result.json'), module_file, request_file, template_path]:
        bind(path)
    source = template_path.read_text().replace('  let requested : Array (String × String) := @@REQUESTED@@', '  let requestedText ← Lean.Elab.Command.liftIO <| IO.FS.readFile ' + json.dumps(str(request_file)) + '\n  let mut requested : Array (String × String) := #[]\n  for line in requestedText.splitOn "\\n" do\n    if line != "" then\n      match line.splitOn "\\t" with\n      | [n, owner] => requested := requested.push (n, owner)\n      | _ => throwError "Malformed retirement request"')
    source = source.replace('  let expectedModules : Array String := @@LOCAL_MODULES@@', '  let moduleText ← Lean.Elab.Command.liftIO <| IO.FS.readFile ' + json.dumps(str(module_file)) + '\n  let expectedModules := ((moduleText.splitOn "\\n").filter (· != "")).toArray')
    destination = output / 'retirement-after-absent.json'
    source = source.replace('@@MODULE_IMPORTS@@', '\n'.join('import ' + r for r in roots)).replace('@@OUTPUT_PATH@@', json.dumps(str(destination)))
    assert '@@' not in source
    query('retirement-after-absent', source, destination)
    union = 'WuPruningKernelUnion'
    query(union, '\n'.join('import ' + r for r in roots) + '\n')
    steps.append(dict(label='fresh-kernel-union', command=[str(Path(lean).with_name('leanchecker')), '--verbose', '--fresh', union], library=str(output) + ':' + str(run / 'build/lib'), expected_exit_code=0, timeout_seconds=14400))
    for old in prior_plan['steps']:
        if old['label'] in ['hf4-producer-check', 'c-eighth-producer-check']:
            steps.append({**old, 'command': [x.replace(str(Path(prior_plan['run'])), str(run)) for x in old['command']], 'library': str(run / 'build/lib')})
    assert len(steps) == len({s['label'] for s in steps}) == 10
    result = dict(status='PREPARED_UNEXECUTED_PRUNING_VALIDATION_NOT_ACCEPTED', run=str(run), baseline=str(canonical), baseline_run=preflight['baseline'], lean=lean, package_paths=prior_plan['package_paths'], steps=steps, comparisons=comparisons, retirement_targets=len(targets), retirement_expected_modules=len(manifest), selected_source_declarations=len(chosen), fresh_kernel_module=union, kernel_roots=roots, bindings=bindings, baseline_exports_reused_from_successful_actual_validation=True, required_checks=['Terminal successful incremental build and exact recursive receipt/context audit', 'Pinned tools, packages and generator inputs before/after', 'Four exact type/value comparisons, literals, standard axioms, private-inclusive family retirement', 'One fresh full imported-environment replay after all source compilation', 'Both producers and complete source/context audit after checks; no automatic installation'])
    (output / 'validation-plan.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(status=result['status'], steps=len(steps), retirement_targets=len(targets), directory=str(output))))


if __name__ == '__main__':
    main()
