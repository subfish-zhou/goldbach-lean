#!/usr/bin/env python3
"""Read the existing Chen objects and reproduce the redundancy measurements.

Run from a checkout with the accepted full main build. Output must be a new
directory. This tool never edits or rebuilds a project proof module.
"""
from pathlib import Path
import argparse
import collections
import hashlib
import importlib.util
import json
import os
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]


def load_script(name, relative):
    spec = importlib.util.spec_from_file_location(name, ROOT / relative)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def local_closure(graph, roots):
    seen, pending = set(), list(roots)
    while pending:
        name = pending.pop()
        if name in seen or name not in graph:
            continue
        seen.add(name)
        pending.extend(graph[name])
    return seen


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--experiments', action='store_true',
                        help='Run the three historical experiments in the matching pre-cleanup checkout.')
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    (output / 'raw').mkdir()
    checks = load_script('chen_checks', 'scripts/check.py')
    exporter = load_script('chen_exporter', 'scripts/build_project_structure.py')
    sources = {str(p.relative_to(ROOT).with_suffix('')).replace('/', '.'): p
               for p in checks.source_files()}
    pattern = re.compile(r'^\s*(?:(?:public|meta)\s+)*import\s+(.+)', re.M)
    graph = {name: [item for match in pattern.finditer(checks.code_only(path.read_text()))
                    for item in match.group(1).split() if item in sources]
             for name, path in sources.items()}
    modules = sorted(local_closure(graph, ['Goldbach.Theorem']))
    inputs, manifest = {}, []
    for i, name in enumerate(modules):
        source = sources[name]
        obj = ROOT / '.lake/build/lib/lean' / Path(*name.split('.')).with_suffix('.olean')
        assert obj.is_file(), 'Build the main libraries first: ' + name
        parts = [source, obj]
        parts.extend(p for suffix in ['.server', '.private']
                     if (p := Path(str(obj) + suffix)).exists())
        if obj.with_suffix('.ir.sig').exists():
            parts.extend([obj.with_suffix('.ir.sig'), obj.with_suffix('.ir')])
        for path in parts:
            inputs[str(path.relative_to(ROOT))] = digest(path)
        manifest.append(f'{source}\t{obj}\t{output}/raw/{i}.json')
    (output / 'manifest.tsv').write_text('\n'.join(manifest) + '\n')
    env = os.environ.copy()
    env.pop('LEAN_PATH', None)
    env.pop('LEAN_SRC_PATH', None)
    with (output / 'extraction.log').open('w') as log:
        subprocess.run(['lake', 'env', 'lean', '--run', 'tools/ProjectStructure.lean',
                        str(output / 'manifest.tsv')], cwd=ROOT, env=env,
                       stdout=log, stderr=subprocess.STDOUT, check=True)
    declarations, owners, stats, import_graph = {}, collections.defaultdict(set), {}, {}
    generated_equation_variants = {}
    for i, name in enumerate(modules):
        raw = json.loads((output / f'raw/{i}.json').read_text())
        rows = exporter.normalize_declarations(raw)
        for row in rows:
            old = declarations.get(row['name'])
            if old is not None and old != row:
                # Lean can realize the same generated equation theorem in
                # separate consumers, using different private match splitters.
                # Keep the actual stored variants and conservatively union their
                # references. Never accept a conflicting ordinary declaration.
                assert row['name'].endswith('.eq_def'), row['name']
                assert {k:v for k,v in old.items() if k!='value'} == {
                    k:v for k,v in row.items() if k!='value'}, row['name']
                variants = generated_equation_variants.setdefault(row['name'], [])
                if not variants:
                    variants.append({'modules': sorted(owners[row['name']]),
                                     'declaration': old})
                variants.append({'modules': [name], 'declaration': row})
                row = dict(row, value=sorted(set(old['value']) | set(row['value'])))
            declarations[row['name']] = row
            owners[row['name']].add(name)
        import_graph[name] = [dep for dep in raw['sourceImports'] if dep in modules]
        text = sources[name].read_text()
        stats[name] = {'physical_lines': len(text.splitlines()),
                       'code_lines': checks.count_code_lines(text),
                       'bytes': len(text.encode()), 'declarations': len(rows)}
    references = {name: set(row['type'] + row['value'] + row['recursorRHS'])
                  for name, row in declarations.items()}

    def references_from(roots):
        seen, pending = set(), list(roots)
        while pending:
            name = pending.pop()
            if name in seen:
                continue
            seen.add(name)
            pending.extend(references.get(name, []))
        return seen

    def providers(names):
        return {module for name in names for module in owners.get(name, [])}

    def summarize(names):
        return {'modules': len(names), **{key: sum(stats[m][key] for m in names)
                for key in ['physical_lines', 'code_lines', 'bytes', 'declarations']}}

    existence = references_from(['Goldbach.chen_theorem'])
    count = references_from(['Goldbach.representation_lower_bound'])
    both = existence | count
    used = providers(both)
    unused = set(modules) - used
    unknown = sorted(name for name in both if name not in declarations
                     and name.startswith(('MathlibNt.', 'Goldbach.',
                                          'AnalyticNumberTheory.', 'PrimeNumberTheoremAnd.')))
    implied_imports = []
    for consumer, dependencies in import_graph.items():
        for dependency in dependencies:
            if dependency in local_closure(import_graph, [d for d in dependencies if d != dependency]):
                implied_imports.append({'consumer': consumer, 'import': dependency})
    result = {
        'revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        'revision_role': 'HEAD identifies the checkout base; inputs_sha256 identifies the measured working-tree sources and objects.',
        'import_closure': summarize(set(modules)),
        'existence_reference_closure': summarize(providers(existence)),
        'count_reference_closure': summarize(providers(count)),
        'both_reference_closure': summarize(used),
        'modules_with_no_reached_declarations': summarize(unused),
        'existence_local_declarations': len(existence & declarations.keys()),
        'count_local_declarations': len(count & declarations.keys()),
        'both_local_declarations': len(both & declarations.keys()),
        'census_local_declarations': len(declarations),
        'unresolved_local_references': unknown,
        'unused_modules': sorted(unused),
        'direct_imports_implied_transitively': implied_imports,
        'inputs_sha256': inputs,
        'generated_equation_variants': generated_equation_variants,
        'method': 'Union of compiled type, value and recursor-RHS references; external declarations are leaves. Generated same-name equation theorem variants union their recorded value references conservatively; variants are listed separately. Import-only modules are candidates; elaboration effects still require compile checks.',
    }
    assert not unknown, unknown
    if args.experiments:
        # Historical experiments require the exact source snapshot recorded by the
        # original audit; the core measurement above also works after cleanup.
        baseline = json.loads(Path(__file__).with_name('analysis.json').read_text())
        for row in baseline['module_details']:
            source = ROOT / Path(*row['module'].split('.')).with_suffix('.lean')
            assert source.exists() and digest(source) == row['source_sha256'], (
                'Historical experiments require the pre-cleanup c4e1b8d0 source snapshot')
        sharp = (ROOT / 'MathlibNt/AnalyticNumberTheory/Chen1973/Chen1973Lemma6Equation19UniformMoments.lean').read_text()
        sharp = sharp[:sharp.index('private lemma eq19_pair_shell_data')]
        sharp = sharp.replace('import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation19MomentTransport',
                              'import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma2PrimitiveLargeSieve')
        sharp += '\nend AnalyticNumberTheory.LargeSieve\n'
        bridge = (ROOT / 'MathlibNt/SieveTheory/Selberg/Liu/LiuSelbergCorrectedChenBridge.lean').read_text()
        bridge = bridge[:bridge.index('/-- Backward-compatible wrapper for the stronger canonical source contract. -/')]
        for dependency in ['MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanCombinedAbelDeterministic',
                           'MathlibNt.SieveTheory.LinearSieve.LevelSupported.Q1LevelSupportedSieve']:
            bridge = bridge.replace('import ' + dependency + '\n', '')
        bridge += '\nend MathlibNt.SieveTheory.LiuWeight\n'
        experiments = {'SharpPrimitiveCore': sharp, 'ProductionBridge': bridge,
                       'ExistenceFromCount': Path(__file__).with_name('ExistenceFromCount.lean').read_text()}
        for name, text in experiments.items():
            source = output / (name + '.lean')
            source.write_text(text)
            with (output / (name + '.log')).open('w') as log:
                subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true', str(source)],
                               cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
    for relative, expected in inputs.items():
        assert digest(ROOT / relative) == expected, 'Input changed: ' + relative
    result['isolated_experiments'] = ('all three passed; production source and object hashes unchanged'
                                      if args.experiments else 'not requested; core measurement only')
    (output / 'analysis.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['import_closure', 'both_reference_closure',
                     'modules_with_no_reached_declarations', 'isolated_experiments']}, indent=2))


if __name__ == '__main__':
    main()
