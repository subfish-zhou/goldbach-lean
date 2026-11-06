#!/usr/bin/env python3
"""Stage a mixed-kind reference query, or conservatively select its families.

Neither operation executes Lean or deletes sources. A definition root is
eligible only after its actual constant kind matches its frozen source header.
Generated non-theorem auxiliaries still require separate ownership review.
"""
import argparse
import collections
import copy
import json
import re
from pathlib import Path

from dead_family_census import save, select_families, sha


def prepare(args):
    original_plan = args.theorem_plan.resolve()
    old = json.loads(original_plan.read_text())
    model_path, output = args.opportunities.resolve(), args.output_dir.resolve()
    model = json.loads(model_path.read_text())
    assert model['status'] == 'LEXICAL_COMBINED_DECLARATION_OPPORTUNITIES_ONLY_NOT_REFERENCES_DELETION_OR_PROOF_ACCEPTANCE'
    run = Path(old['run'])
    assert model['source_manifest_sha256'] == sha(run / 'source-manifest.json')
    assert not output.exists() and output != run and run not in output.parents
    for filename, expected in old['bindings'].items():
        assert sha(Path(filename)) == expected, filename
    expected = {}
    for row in model['candidates']:
        source = run / 'src' / Path(*row['module'].split('.')).with_suffix('.lean')
        assert sha(source) == row['original_source_sha256']
        line = source.read_text().splitlines()[row['original_line'] - 1]
        match = re.match(r'^(?:(?:private|noncomputable)\s+)*(theorem|lemma|def|abbrev)\b', line)
        assert match, (row['module'], row['original_line'])
        base = row['written_name'].split('.')[-1]
        assert base not in expected
        expected[base] = (row['module'], 'theorem' if match[1] in ['theorem', 'lemma'] else 'definition')
    output.mkdir(parents=True)
    request = output / 'requested.tsv'
    request.write_text(''.join(base + '\t' + owner + '\t' + kind + '\n' for base, (owner, kind) in sorted(expected.items())))
    source = (original_plan.parent / 'Probe.lean').read_text()

    def replace(before, after):
        nonlocal source
        assert source.count(before) == 1, before
        source = source.replace(before, after)

    replace(json.dumps(str(original_plan.parent / 'requested.tsv')), json.dumps(str(request)))
    replace(json.dumps(str(original_plan.parent / 'census.json')), json.dumps(str(output / 'census.json')))
    replace('  let mut wanted : Std.HashMap String String := {}',
            '  let mut wanted : Std.HashMap String String := {}\n  let mut expectedKinds : Std.HashMap String String := {}')
    replace('    | [base, owner] =>', '    | [base, owner, expectedKind] =>\n      unless expectedKind == "theorem" || expectedKind == "definition" do\n        throwError "Unexpected source declaration kind: {expectedKind}"')
    replace('      wanted := wanted.insert base owner',
            '      wanted := wanted.insert base owner\n      expectedKinds := expectedKinds.insert base expectedKind')
    replace('        unless kind ci == "theorem" do', '        unless expectedKinds[lastString n]? == some (kind ci) do')
    replace('Source proof resolves to a non-theorem:', 'Source declaration resolves to an unexpected constant kind:')
    replace('("basename", toJson base), ("module", toJson owner), ("name", toJson n.toString)]',
            '("basename", toJson base), ("module", toJson owner), ("name", toJson n.toString),\n      ("kind", toJson (expectedKinds[base]?.getD ""))]')
    replace('wu-dead-proof-family-census-v1', 'wu-dead-declaration-family-census-v1')
    query = output / 'Probe.lean'
    query.write_text(source)
    bindings = {**old['bindings'], **{str(p): sha(p) for p in [Path(__file__).resolve(), original_plan, model_path, request, query]}}
    plan = {'status': 'PREPARED_UNCOMPILED_MIXED_KIND_CENSUS_NOT_RETIREMENT_ACCEPTANCE',
            'run': str(run), 'candidate_count': len(expected), 'research_modules': old['research_modules'],
            'source_kind_counts': dict(collections.Counter(k for _, k in expected.values())),
            'roots': old['roots'], 'opportunities': str(model_path), 'bindings': bindings,
            'requires_before_execution': ['Successful completed source build and all 34 validation gates', 'Pinned tools, exact library context and exclusive Lean lock'],
            'requires_after_selection': old['requires_after_selection']}
    save(output / 'plan.json', plan)
    print(json.dumps({'status': plan['status'], 'candidates': len(expected), 'source_kind_counts': plan['source_kind_counts']}))


def select_mixed(census):
    assert census['schema'] == 'wu-dead-declaration-family-census-v1'
    targets = {r['name']: r for r in census['candidates']}
    assert len(targets) == census['candidateCount']
    roots = [r for r in census['members'] if r['name'] == r['family']]
    assert len(roots) == len(targets) and {r['name'] for r in roots} == set(targets)
    for row in roots:
        target = targets[row['name']]
        assert target['kind'] in ['theorem', 'definition']
        assert row['kind'] == target['kind'] and row['module'] == target['module']
    # The shared boundary algorithm pins non-theorem members. Definition roots
    # have now been validated separately; omit only those roots from that test.
    # Keep every generated auxiliary in the test and preserve the raw census.
    working = copy.deepcopy(census)
    working['schema'] = 'wu-dead-proof-family-census-v1'
    working['members'] = [r for r in working['members'] if not
                          (r['name'] == r['family'] and targets[r['name']]['kind'] == 'definition')]
    result = select_families(working)
    result['status'] = 'MIXED_KIND_REFERENCE_BOUNDARY_ONLY_NOT_SOURCE_RETIREMENT_OR_PROOF_ACCEPTANCE'
    result['validated_source_definition_roots'] = sum(r['kind'] == 'definition' for r in roots)
    result['raw_census_kinds_preserved'] = True
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest='operation', required=True)
    pre = sub.add_parser('prepare')
    pre.add_argument('--theorem-plan', type=Path, required=True)
    pre.add_argument('--opportunities', type=Path, required=True)
    pre.add_argument('--output-dir', type=Path, required=True)
    sel = sub.add_parser('select')
    sel.add_argument('--census', type=Path, required=True)
    sel.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    if args.operation == 'prepare':
        prepare(args)
    else:
        result = select_mixed(json.loads(args.census.read_text()))
        result['census_sha256'] = sha(args.census)
        save(args.output, result)
        print(json.dumps({'selected': len(result['selected']), 'retained': len(result['retained'])}))


if __name__ == '__main__':
    main()
