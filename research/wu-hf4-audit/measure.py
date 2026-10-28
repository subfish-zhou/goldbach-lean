"""Measure the Hf4 replacement and check preservation of all 40 panel bounds."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SRC = ROOT / 'research/wu2008/src'
spec = importlib.util.spec_from_file_location('checks', ROOT / 'scripts/check.py')
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)
before = json.loads((HERE / 'baseline-source-index.json').read_text())
after = {}
for p in SRC.rglob('*.lean'):
    name = '.'.join(p.relative_to(SRC).with_suffix('').parts)
    raw = p.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if name in before and digest == before[name]['sha256']:
        after[name] = before[name]
        continue
    text = raw.decode()
    after[name] = dict(sha256=digest, code_lines=checks.count_code_lines(text),
        physical_lines=len(text.splitlines()), utf8_bytes=len(raw),
        imports=re.findall(r'^import (\S+)', checks.code_only(text), re.M))
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b|debug\.skipKernelTC',
        checks.code_only(text)), name

def closure(data):
    seen, todo = set(), ['WR2ClassicalCertificate']
    while todo:
        name = todo.pop()
        if name in seen or name not in data:
            continue
        seen.add(name)
        todo.extend(data[name]['imports'])
    return seen

def stat(data, names):
    return dict(modules=len(names), **{k: sum(data[n][k] for n in names)
        for k in ['code_lines', 'physical_lines', 'utf8_bytes']})

report = {}
for scope, select in [('whole_tree', set), ('theorem_closure', closure)]:
    a, b = stat(before, select(before)), stat(after, select(after))
    report[scope] = dict(before=a, after=b, reduction={k: a[k]-b[k] for k in a})
report['modified_modules'] = sorted(n for n in before.keys() & after.keys()
    if before[n]['sha256'] != after[n]['sha256'])
report['added_modules'] = sorted(after.keys() - before.keys())
report['removed_modules'] = sorted(before.keys() - after.keys())
allowed = {'Hf4QuadPanel0', *[f'Hf4QuadBatch{i}' for i in range(13)]}
assert set(report['modified_modules']) <= allowed
assert set(report['removed_modules']) <= {'Hf4QuadDag'}
assert set(report['added_modules']) <= {
    'Hf4QuadCompactKernel', 'Hf4QuadCompactIntegral', 'Hf4QuadRationalModel', 'Hf4QuadCompactDag'}
report['unchanged_modules'] = len(before) - len(report['modified_modules']) - len(report['removed_modules'])
bounds = {}
for name in allowed:
    text = (SRC / f'{name}.lean').read_text()
    for m in re.finditer(r'namespace Hf4Quad.Panel(\d+)(.*?)(?=end Hf4Quad.Panel\d+)', text, re.S):
        b = re.search(r'theorem mass_bounds\s*:(.*?) := by', m[2], re.S)
        assert b, m[1]
        bounds[m[1]] = ' '.join(b[1].split())
assert bounds == json.loads((HERE / 'baseline-panel-statements.json').read_text())
report['unchanged_panel_bound_statements'] = len(bounds)
report['aggregate_and_endpoint_sources_byte_identical'] = all(
    before[n]['sha256'] == after[n]['sha256'] for n in
    ['Hf4QuadAggregate', 'Hf4QuadKernel', 'Hf4QuadIntegral', 'WR2ClassicalCertificate'])
assert report['aggregate_and_endpoint_sources_byte_identical']
(HERE / 'source-size.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
