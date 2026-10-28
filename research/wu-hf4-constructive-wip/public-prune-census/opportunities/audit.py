"""Read-only public proof opportunity audit, not an API retirement decision."""
from pathlib import Path
import bisect
import collections
import hashlib
import importlib.util
import json
import re
import runpy
import subprocess

ROOT = Path('/home/azureuser/goldbach-lean')
SOURCE = ROOT/'research/wu2008/src'
PREVIEW = Path('/tmp/wu-structural-integration-plan-v7/preview')
SELECTED = Path('/tmp/wu-structural-interface-selection-v2/selected.json')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
words = lambda s: re.findall(r"[A-Za-z_][\w']*", s)


def main():
    planfile = PREVIEW/'plan.json'
    plan = json.loads(planfile.read_text())
    graph = plan['effective_graph']
    assert len(graph) == 4151
    closure = set()
    def visit(n):
        if n not in graph or n in closure: return
        closure.add(n)
        for d in graph[n]: visit(d)
    visit('WR2ClassicalCertificate')
    assert len(closure) == 3764
    lexer = Path('/tmp/wu-structural-full-probe/lexical.py')
    code = runpy.run_path(str(lexer))['code_only']
    spec = importlib.util.spec_from_file_location('counter', ROOT/'scripts/check.py')
    counter = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(counter)
    bindings = {str(p): sha(p) for p in [Path(__file__), planfile, lexer, ROOT/'scripts/check.py', SELECTED]}
    selected = json.loads(SELECTED.read_text())
    assert len(selected) == 736
    protected = {r['qname'].split('.')[-1] for r in selected}
    protected.update(['one8938', 'one894', 'classical_lower'])
    # Protect names mentioned by repository documentation and Python consumers,
    # including diagnostic generators and literal-theorem entrypoint probes.
    paths = subprocess.check_output(['rg', '--files', '-g', '*.md', '-g', '*.py'], cwd=ROOT, text=True).splitlines()
    for name in paths:
        p = ROOT/name
        assert p.resolve().is_relative_to(ROOT)
        bindings[str(p)] = sha(p)
        protected.update(words(p.read_text()))
    lean_paths = subprocess.check_output(['rg', '--files', '-g', '*.lean'], cwd=ROOT, text=True).splitlines()
    external_lean = []
    for name in lean_paths:
        p = ROOT/name
        if p.is_relative_to(SOURCE): continue
        assert p.resolve().is_relative_to(ROOT)
        external_lean.append(name)
        bindings[str(p)] = sha(p)
        protected.update(words(p.read_text()))
    overlays = {r['module']: r for r in plan['overlay']}
    actual = plan['actual_post_first_baseline']['source_inventory']
    texts, clean, tokens = {}, {}, collections.Counter()
    for n in sorted(graph):
        if n in overlays:
            r = overlays[n]; p, digest = PREVIEW/'overlay'/r['file'], r['candidate_sha256']
        else:
            p, digest = SOURCE/Path(*n.split('.')).with_suffix('.lean'), actual[n]
        assert sha(p) == digest
        bindings[str(p)] = digest
        t = p.read_text(); texts[n], clean[n] = t, code(t)
        tokens.update(words(code(t, keep_strings=True)))
    pattern = re.compile(r"^(?:theorem|lemma)\s+([A-Za-z_][\w.']*)(?![\w.'])", re.M)
    candidates, excluded = [], collections.Counter()
    for n in sorted(closure - set(overlays)):
        text, masked = texts[n], clean[n]
        starts = [m.start() for m in re.finditer(r'^\S', masked, re.M)]
        for m in pattern.finditer(masked):
            name = m[1].split('.')[-1]
            if tokens[name] != 1: continue
            if name in protected:
                excluded['documented_or_selected_name'] += 1
                continue
            index = bisect.bisect_left(starts, m.start())
            previous = masked[starts[index-1]:m.start()].lstrip() if index else ''
            if previous.startswith('@['):
                excluded['attributed_declaration'] += 1
                continue
            end = starts[index+1] if index+1 < len(starts) else len(text)
            fragment = text[m.start():end]
            candidates.append(dict(module=n, written_name=m[1], line=text.count('\n',0,m.start())+1,
                start_character=m.start(), provisional_end_character=end,
                code_lines=counter.count_code_lines(fragment), bytes=len(fragment.encode()),
                fragment_sha256=hashlib.sha256(fragment.encode()).hexdigest()))
    groups = collections.defaultdict(lambda: dict(declarations=0, code_lines=0, bytes=0))
    for r in candidates:
        g = groups[r['module']]
        g['declarations'] += 1; g['code_lines'] += r['code_lines']; g['bytes'] += r['bytes']
    totals = dict(declarations=len(candidates), modules=len(groups),
                  provisional_code_lines=sum(r['code_lines'] for r in candidates),
                  provisional_bytes=sum(r['bytes'] for r in candidates))
    report = dict(status='LEXICAL_PUBLIC_PROOF_OPPORTUNITIES_NOT_API_RETIREMENT_OR_LEAN_ACCEPTANCE',
        effective_source_modules=4151, final_closure_modules=3764, bindings=bindings,
        protected_documentation_python_files=len(paths), protected_names=len(protected),
        protected_other_repository_lean_files=len(external_lean),
        protected_explicit_interface_names=736, changed_modules_excluded=64,
        candidates=candidates, totals=totals, excluded=dict(excluded),
        module_totals=dict(sorted(groups.items(), key=lambda r: -r[1]['code_lines'])),
        limitations=['No source deletion or compiler execution performed.',
            'Singleton basename occurrences do not prove absence of implicit tactic/library search dependencies.',
            'Public API retirement still needs explicit scope review; consumers outside this repository are unknown.',
            'Repository docs/Python, other repository Lean sources and736 selected interfaces protected; this is not an exhaustive external API inventory.',
            'Current64 V7 changes excluded; no frozen input modified.',
            'Any eventual patch requires exact declaration/doc/attribute intervals and real downstream/full-project checks.'])
    out = Path(__file__).with_name('opportunities.json')
    out.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(dict(path=str(out), sha256=sha(out), totals=totals, excluded=dict(excluded),
                         protected_docs_python=len(paths), protected_other_lean=len(external_lean), top_modules=list(report['module_totals'].items())[:12])))


if __name__ == '__main__':
    main()
