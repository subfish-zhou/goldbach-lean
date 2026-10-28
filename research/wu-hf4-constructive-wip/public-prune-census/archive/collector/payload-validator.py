"""Pure Python census payload consistency checks; never invokes Lean or accepts retirement."""
from __future__ import annotations
import argparse
import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

STATUS = 'PAYLOAD_CONSISTENCY_NOT_RUNTIME_OR_RETIREMENT_ACCEPTANCE'
SCHEMA = 'wu-candidate-constant-use-v2-raw-module-data'
PAYLOAD_STATUS = 'ELABORATED_USE_INVENTORY_NOT_RETIREMENT_OR_PROOF_ACCEPTANCE'
INVENTORY = 'unmerged private-inclusive ModuleData.constants; provenance from raw module index'
SCOPE = 'all research constant types and opaque-inclusive values; direct constant references'
BASE = Path('/tmp/wu-public-constant-use-probe-v2')
PREP = BASE/'prepared-scope-cover/preparation.json'
PREP_SHA = 'c6439a0a10a14d7edb000880def7f651e9856902b0b777e64d4261228a73df27'
AUDIT = Path('/tmp/wu-next-public-prune-audit-v2/opportunities.json')
AUDIT_SHA = 'a934e7ba252b2b378f153017578d1ad666b75d635fa2666f98923a52fb5e935d'
GRAPH = Path('/tmp/wu-structural-integration-plan-v7/preview/plan.json')

class Invalid(ValueError):
    pass

def need(ok: bool, message: str) -> None:
    if not ok:
        raise Invalid(message)

def obj(value: Any, fields: set[str], label: str) -> None:
    need(type(value) is dict and set(value) == fields, label+' fields')

def nat(value: Any, label: str) -> int:
    need(type(value) is int and value >= 0, label+' must be a nonnegative integer (not Boolean)')
    return value

def nonempty(value: Any, label: str) -> str:
    need(type(value) is str and bool(value.strip()), label+' must be a nonempty string')
    return value

def _pairs(pairs):
    result = {}
    for k, v in pairs:
        need(k not in result, 'duplicate JSON key: '+k)
        result[k] = v
    return result

def parse_json(raw: bytes):
    return json.loads(raw.decode('utf-8'), object_pairs_hook=_pairs,
                      parse_constant=lambda x: (_ for _ in ()).throw(Invalid('nonfinite JSON number: '+x)))

def read_json(path: Path):
    return parse_json(path.read_bytes())

def read_bound_json(path: Path, expected: str):
    raw = path.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    need(type(expected) is str and digest == expected, 'hash mismatch: '+str(path))
    return parse_json(raw), digest

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def bound(path: Path, expected: str) -> None:
    need(type(expected) is str and len(expected) == 64 and sha(path) == expected, 'hash mismatch: '+str(path))

@dataclass(frozen=True)
class Candidate:
    basename: str
    module: str
    provisional_code_lines: int

@dataclass(frozen=True)
class Spec:
    root: str
    imported: frozenset[str]
    assigned: tuple[str, ...]
    requested: tuple[Candidate, ...]

def closure(graph: dict[str, list[str]], root: str) -> frozenset[str]:
    seen, todo = set(), [root]
    while todo:
        n = todo.pop()
        if n in graph and n not in seen:
            seen.add(n)
            todo.extend(graph[n])
    return frozenset(seen)

def derive_specs(graph: dict[str, list[str]], candidates: tuple[Candidate, ...], roots: list[str]) -> tuple[Spec, ...]:
    need(type(graph) is dict and bool(graph), 'empty or invalid graph')
    for n, deps in graph.items():
        nonempty(n, 'graph module')
        need(type(deps) is list and all(type(d) is str and d for d in deps), 'invalid graph dependencies')
    need(len(set(roots)) == len(roots) and all(r in graph for r in roots), 'duplicate or unknown roots')
    need(len({c.basename for c in candidates}) == len(candidates), 'duplicate candidate basename')
    for c in candidates:
        nonempty(c.basename, 'candidate basename')
        need(c.module in graph, 'candidate source module missing')
        nat(c.provisional_code_lines, 'provisional code lines')
    covered, specs = set(), []
    for root in roots:
        imported = closure(graph, root)
        assigned = tuple(sorted(imported-covered))
        need(bool(assigned), 'empty assigned scope: '+root)
        covered.update(imported)
        specs.append(Spec(root, imported, assigned, tuple(c for c in candidates if c.module in imported)))
    need(covered == set(graph), 'roots do not cover the complete graph')
    need(sum(len(s.assigned) for s in specs) == len(graph), 'overlapping assigned scopes')
    return tuple(specs)

PAYLOAD_FIELDS = {'schema', 'status', 'requestedCount', 'expectedResearchModules', 'assignedScanModules',
                  'constantInventory', 'importedResearchConstants', 'scannedResearchConstants',
                  'scannedValuesIncludingTheoremsAndOpaque', 'scope', 'candidates'}
ROW_FIELDS = {'basename', 'module', 'name', 'privateRuntimeName', 'incomingCount', 'incomingUsers'}

def validate_payloads(specs: tuple[Spec, ...], candidates: tuple[Candidate, ...],
                      outputs: list[tuple[str, Any]]) -> dict:
    """Pure function. Validates payloads and unions *all* scopes before zero classification."""
    need(type(outputs) is list and len(outputs) == len(specs), 'missing or extra probe outputs')
    need([r for r, _ in outputs] == [s.root for s in specs], 'duplicate, missing, or out-of-order probe root')
    names, flags = {}, {}
    edges = {c.basename: set() for c in candidates}
    stats = []
    for spec, (_, payload) in zip(specs, outputs):
        obj(payload, PAYLOAD_FIELDS, 'payload '+spec.root)
        for key, expected in [('schema', SCHEMA), ('status', PAYLOAD_STATUS),
                              ('constantInventory', INVENTORY), ('scope', SCOPE)]:
            need(payload[key] == expected, 'wrong '+key+': '+spec.root)
        need(nat(payload['requestedCount'], 'requestedCount') == len(spec.requested), 'requestedCount mismatch')
        need(nat(payload['expectedResearchModules'], 'expectedResearchModules') == len(spec.imported), 'imported module count mismatch')
        need(type(payload['assignedScanModules']) is list and payload['assignedScanModules'] == list(spec.assigned), 'assigned module scope/order mismatch')
        imported = nat(payload['importedResearchConstants'], 'importedResearchConstants')
        scanned = nat(payload['scannedResearchConstants'], 'scannedResearchConstants')
        values = nat(payload['scannedValuesIncludingTheoremsAndOpaque'], 'scannedValuesIncludingTheoremsAndOpaque')
        need(imported >= scanned >= values, 'inconsistent constant statistics')
        need(imported >= len(spec.requested), 'too few imported constants for resolved candidates')
        rows = payload['candidates']
        need(type(rows) is list and len(rows) == len(spec.requested), 'candidate row count mismatch')
        assigned = set(spec.assigned)
        for candidate, row in zip(spec.requested, rows):
            obj(row, ROW_FIELDS, 'candidate row')
            base = candidate.basename
            need((row['basename'], row['module']) == (base, candidate.module), 'candidate collection/order mismatch')
            name = nonempty(row['name'], 'runtime QName')
            need(name.rsplit('.', 1)[-1] == base, 'runtime QName basename mismatch')
            flag = row['privateRuntimeName']
            need(type(flag) is bool and flag == name.startswith('_private.'), 'privateRuntimeName flag mismatch')
            if base in names:
                need(names[base] == name and flags[base] == flag, 'inconsistent runtime QName across probes: '+base)
            names[base], flags[base] = name, flag
            users = row['incomingUsers']
            need(type(users) is list, 'incomingUsers must be an array')
            need(nat(row['incomingCount'], 'incomingCount') == len(users), 'incomingCount mismatch')
            need(len(users) <= scanned, 'more incoming users than scanned constants')
            local_edges = set()
            for user in users:
                obj(user, {'name', 'module'}, 'incoming user')
                qname = nonempty(user['name'], 'incoming QName')
                module = nonempty(user['module'], 'incoming module')
                need(module in assigned, 'incoming user outside assigned scope')
                edge = (module, qname)
                need(edge not in local_edges, 'duplicate incoming user (module,QName)')
                local_edges.add(edge)
            need(not (edges[base] & local_edges), 'duplicate incoming edge across assigned scopes')
            edges[base].update(local_edges)
        stats.append(dict(import_root=spec.root, importedResearchConstants=imported,
                          scannedResearchConstants=scanned, scannedValuesIncludingTheoremsAndOpaque=values))
    need(set(names) == set(edges), 'candidate resolution coverage incomplete')
    merged = []
    for c in candidates:
        users = [dict(module=m, name=n) for m, n in sorted(edges[c.basename])]
        merged.append(dict(basename=c.basename, module=c.module, name=names[c.basename],
                           privateRuntimeName=flags[c.basename], incomingCount=len(users), incomingUsers=users,
                           provisional_code_lines=c.provisional_code_lines))
    zeros = [r.copy() for r in merged if r['incomingCount'] == 0]
    return dict(status=STATUS, schema='wu-census-payload-consistency-v1', runtimeEvidenceAccepted=False,
                retirementAccepted=False, privateRuntimeNameIsPublicVisibility=False, probeCount=len(specs),
                candidateCount=len(candidates), assignedModuleCount=sum(len(s.assigned) for s in specs),
                probeStatistics=stats, candidates=merged, zeroIncomingCandidates=zeros,
                provisionalZeroIncomingCodeLines=sum(r['provisional_code_lines'] for r in zeros),
                limitations=['Payload shape/scope consistency only; JSON is not execution evidence.',
                             'Zero incoming edges are not API retirement permission or proof acceptance.',
                             'privateRuntimeName is a prefix flag, not module visibility.',
                             'Future actual runner must bind rc=0, fresh paths, source/output/log/library/context hashes.'])

def load_real_specs() -> tuple[tuple[Spec, ...], tuple[Candidate, ...], dict]:
    """Fail closed on all pinned real source/preparation bindings; no proof subprocesses."""
    bound(PREP, PREP_SHA)
    bound(AUDIT, AUDIT_SHA)
    prep, audit = read_json(PREP), read_json(AUDIT)
    for name, digest in audit['bindings'].items():
        bound(Path(name), digest)
    need(str(GRAPH) in audit['bindings'], 'graph not bound by audit')
    bound(GRAPH, audit['bindings'][str(GRAPH)])
    graph = read_json(GRAPH)['effective_graph']
    need(len(graph) == 4151 and len(audit['candidates']) == 2096, 'real graph/candidate counts mismatch')
    need(prep['status'] == 'SOURCE_PREPARED_UNCOMPILED_NOT_CONSTANT_USE_EVIDENCE' and prep['Lean_executed'] is False, 'unexpected preparation status')
    need(prep['audit_sha256'] == AUDIT_SHA, 'prep audit binding mismatch')
    bound(BASE/'Template.lean', prep['template_sha256'])
    bound(BASE/'prepare.py', prep['preparer_sha256'])
    candidates = tuple(Candidate(r['written_name'].split('.')[-1], r['module'], r['code_lines']) for r in audit['candidates'])
    need(sum(c.provisional_code_lines for c in candidates) == 31152, 'provisional audit total mismatch')
    main = closure(graph, 'WR2ClassicalCertificate')
    need(len(main) == 3764, 'primary closure mismatch')
    outside = set(graph)-main
    need(len(outside) == 387, 'outside module count mismatch')
    roots = ['WR2ClassicalCertificate', *sorted(outside-{d for n in outside for d in graph[n] if d in outside})]
    specs = derive_specs(graph, candidates, roots)
    need(len(specs) == len(prep['probes']) == 21, 'real probe count mismatch')
    need(prep['candidate_count'] == 2096 and prep['covered_research_modules'] == 4151 and
         prep['separate_environments'] == 21 and prep['assigned_scans_pairwise_disjoint'] is True, 'preparation coverage fields mismatch')
    template = (BASE/'Template.lean').read_text()
    quote = lambda s: json.dumps(s, ensure_ascii=False)
    array = lambda xs: '#[\n'+',\n'.join('  '+quote(x) for x in xs)+'\n]'
    for i, (spec, row) in enumerate(zip(specs, prep['probes'])):
        directory = BASE/'prepared-scope-cover'/f'{i:02}'
        need(row['import_root'] == spec.root and row['imported_modules'] == len(spec.imported) and
             row['assigned_scan_modules'] == list(spec.assigned) and row['requested_candidates'] == len(spec.requested), 'prepared probe scope mismatch')
        need(row['source'] == str(directory/'Probe.lean') and row['expected_output'] == str(directory/'uses.json'), 'prepared source/output path mismatch')
        source = Path(row['source'])
        bound(source, row['source_sha256'])
        requested = '#[\n'+',\n'.join('  ('+quote(c.basename)+', '+quote(c.module)+')' for c in spec.requested)+'\n]'
        replacements = {'@@MODULE_IMPORTS@@': 'import '+spec.root, '@@REQUESTED@@': requested,
                        '@@LOCAL_MODULES@@': array(sorted(spec.imported)), '@@SCAN_MODULES@@': array(spec.assigned),
                        '@@OUTPUT_PATH@@': quote(row['expected_output'])}
        text = template
        for marker, value in replacements.items():
            need(text.count(marker) == 1, 'template substitution mismatch')
            text = text.replace(marker, value)
        need(source.read_text() == text and '@@' not in text, 'prepared source differs from independently derived probe')
    return specs, candidates, dict(preparation_sha256=PREP_SHA, audit_sha256=AUDIT_SHA,
                                  graph_sha256=sha(GRAPH), template_sha256=sha(BASE/'Template.lean'),
                                  preparer_sha256=sha(BASE/'prepare.py'), audited_input_bindings=len(audit['bindings']))

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument('--input-index', type=Path, help='JSON array of {import_root, output, output_sha256}; all 21 in prepared order')
    action.add_argument('--check-inputs-only', action='store_true', help='check static real inputs; no census payload validation')
    parser.add_argument('--report', type=Path, help='new output file only; refuses overwrite and input-tree destinations')
    args = parser.parse_args()
    specs, candidates, bindings = load_real_specs()
    if args.check_inputs_only:
        report = dict(status=STATUS, mode='STATIC_INPUT_BINDINGS_ONLY_NO_PAYLOADS', runtimeEvidenceAccepted=False,
                      retirementAccepted=False, probeCount=len(specs), candidateCount=len(candidates), bindings=bindings)
    else:
        index_raw = args.input_index.read_bytes()
        index = parse_json(index_raw)
        index_digest = hashlib.sha256(index_raw).hexdigest()
        need(type(index) is list and len(index) == 21, 'input index must contain exactly 21 records')
        outputs, paths, payload_bindings = [], set(), []
        for spec, row in zip(specs, index):
            obj(row, {'import_root', 'output', 'output_sha256'}, 'input index row')
            need(row['import_root'] == spec.root, 'input index root/order mismatch')
            path = Path(nonempty(row['output'], 'output path')).resolve()
            need(path not in paths, 'duplicate output path')
            paths.add(path)
            payload, digest = read_bound_json(path, row['output_sha256'])
            outputs.append((spec.root, payload))
            payload_bindings.append(dict(import_root=spec.root, path=str(path), sha256=digest))
        report = validate_payloads(specs, candidates, outputs)
        report.update(bindings=bindings, input_index_sha256=index_digest, payload_bindings=payload_bindings)
    encoded = json.dumps(report, indent=2)+'\n'
    if args.report:
        dest = args.report.resolve()
        need(not dest.is_relative_to(BASE) and not dest.is_relative_to(Path('/home/azureuser/goldbach-lean')),
             'report must not alter input or production tree')
        with dest.open('x') as f:
            f.write(encoded)
    else:
        print(encoded, end='')

if __name__ == '__main__':
    try:
        main()
    except (Invalid, OSError, KeyError, TypeError, UnicodeError, json.JSONDecodeError) as exc:
        raise SystemExit('REJECTED: '+str(exc)) from None
