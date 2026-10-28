"""Count this phase and check source scope and retained mathematical statements."""
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
    code = checks.code_only(text)
    after[name] = dict(sha256=digest, code_lines=checks.count_code_lines(text),
        physical_lines=len(text.splitlines()), utf8_bytes=len(raw),
        imports=re.findall(r'^import (\S+)', code, re.M))
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b|debug\.skipKernelTC', code), name

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

def comparison(a, b):
    return dict(before=a, after=b, reduction={k: a[k]-b[k] for k in a})

report = {}
for scope, select in [('whole_tree', set), ('theorem_closure', closure)]:
    report[scope] = comparison(stat(before, select(before)), stat(after, select(after)))
report['modified_modules'] = sorted(n for n in before.keys() & after.keys()
    if before[n]['sha256'] != after[n]['sha256'])
report['added_modules'] = sorted(after.keys() - before.keys())
report['removed_modules'] = sorted(before.keys() - after.keys())
def family(n):
    if n.startswith('WR2ClassicalFourth') or n.startswith('WR2ClassicalCumulative'):
        return 'fourth_derived'
    if n.startswith('WR2ClassicalEighthCorrection'):
        return 'eighth_correction'
    return None
for n in report['modified_modules'] + report['added_modules'] + report['removed_modules']:
    assert family(n), n
report['families'] = {f: comparison(
    stat(before, {n for n in before if family(n) == f}),
    stat(after, {n for n in after if family(n) == f}))
    for f in ['fourth_derived', 'eighth_correction']}
report['unchanged_modules'] = len(before) - len(report['modified_modules']) - len(report['removed_modules'])
statements = json.loads((HERE / 'baseline-statements.json').read_text())
for key, expected in statements.items():
    module, name = key.split(':')
    text = (SRC / f'{module}.lean').read_text()
    found = re.search(r'theorem '+name+r'\b(.*?)\s*:=', text, re.S)
    assert found and ''.join(found[1].split()) == expected, key
report['preserved_public_statements'] = len(statements)
for n, digest in json.loads((HERE / 'preserved-data.json').read_text()).items():
    assert after[n]['sha256'] == digest, n
assert before['WR2ClassicalCertificate'] == after['WR2ClassicalCertificate']
(HERE / 'source-size.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
