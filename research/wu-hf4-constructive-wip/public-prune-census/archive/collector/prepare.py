"""Prepare an uncompiled whole-environment use probe; never invokes Lean."""
from pathlib import Path
import hashlib
import json
import re
import argparse

HERE = Path(__file__).resolve().parent
AUDIT = Path('/tmp/wu-next-public-prune-audit-v2/opportunities.json')
AUDIT_SHA = 'a934e7ba252b2b378f153017578d1ad666b75d635fa2666f98923a52fb5e935d'
PLAN = Path('/tmp/wu-structural-integration-plan-v7/preview/plan.json')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
quote = lambda s: json.dumps(s, ensure_ascii=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=HERE/'prepared-scope-cover')
    args = parser.parse_args()
    assert sha(AUDIT) == AUDIT_SHA
    audit = json.loads(AUDIT.read_text())
    for name, digest in audit['bindings'].items():
        assert sha(Path(name)) == digest, name
    plan = json.loads(PLAN.read_text())
    graph = plan['effective_graph']
    modules = sorted(graph)
    assert len(modules) == 4151
    assert all(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*', m) for m in modules)
    rows = audit['candidates']
    assert len(rows) == 2096
    wanted = [(r['written_name'].split('.')[-1], r['module']) for r in rows]
    assert len(set(n for n, _ in wanted)) == len(wanted)
    assert all(re.fullmatch(r"[A-Za-z_][\w']*", n) and m in modules for n, m in wanted)
    def closure(root):
        seen, todo = set(), [root]
        while todo:
            n = todo.pop()
            if n not in graph or n in seen: continue
            seen.add(n); todo.extend(graph[n])
        return seen
    primary = 'WR2ClassicalCertificate'
    classical = closure(primary)
    assert len(classical) == 3764
    outside = set(graph) - classical
    consumed = {d for n in outside for d in graph[n] if d in outside}
    roots = [primary, *sorted(outside-consumed)]
    assert len(roots) == 21
    template = HERE/'Template.lean'
    output = args.out.resolve()
    assert not output.is_relative_to(Path('/home/azureuser/goldbach-lean'))
    output.mkdir(exist_ok=True)
    names_array = lambda values: '#[\n' + ',\n'.join('  '+quote(m) for m in values) + '\n]'
    probes, covered = [], set()
    for i, root in enumerate(roots):
        imported = closure(root)
        assigned = imported-covered
        assert assigned
        covered.update(imported)
        selected = [(n,m) for n,m in wanted if m in imported]
        if i == 0: assert len(selected) == 2096
        requested = '#[\n' + ',\n'.join('  ('+quote(n)+', '+quote(m)+')' for n,m in selected) + '\n]'
        directory = output/f'{i:02}'
        directory.mkdir(exist_ok=True)
        text = template.read_text()
        replacements = {'@@MODULE_IMPORTS@@': 'import '+root,
                        '@@REQUESTED@@': requested, '@@LOCAL_MODULES@@': names_array(sorted(imported)),
                        '@@SCAN_MODULES@@': names_array(sorted(assigned)),
                        '@@OUTPUT_PATH@@': quote(str(directory/'uses.json'))}
        for marker, replacement in replacements.items():
            assert text.count(marker) == 1
            text = text.replace(marker, replacement)
        assert '@@' not in text
        source = directory/'Probe.lean'
        source.write_text(text)
        probes.append(dict(import_root=root, imported_modules=len(imported), assigned_scan_modules=sorted(assigned),
                           requested_candidates=len(selected), source=str(source), source_sha256=sha(source),
                           expected_output=str(directory/'uses.json')))
    assert covered == set(modules)
    assert sum(len(p['assigned_scan_modules']) for p in probes) == 4151
    manifest = dict(status='SOURCE_PREPARED_UNCOMPILED_NOT_CONSTANT_USE_EVIDENCE',
        Lean_executed=False, probes=probes,
        template_sha256=sha(template), preparer_sha256=sha(Path(__file__)),
        audit_sha256=AUDIT_SHA, candidate_count=2096, covered_research_modules=4151,
        assigned_scans_pairwise_disjoint=True, separate_environments=21,
        source_data_modified=False, existing_frozen_pipeline_modified=False,
        remaining='After current serial pipeline terminal, create a fresh isolated actual invocation with complete verified4151 library, pinned4.33 SYSROOT/Init, package/context/input bindings, shared sole-worker lock and owned cleanup; compile probe and verify all rows. No production fallback or candidate retirement yet.')
    (output/'preparation.json').write_text(json.dumps(manifest, indent=2)+'\n')
    print(json.dumps(dict(status=manifest['status'], manifest=str(output/'preparation.json'),
                         manifest_sha256=sha(output/'preparation.json'), candidate_count=2096,
                         separate_environments=21, covered_modules=4151, scans_disjoint=True)))


if __name__ == '__main__':
    main()
