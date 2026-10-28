"""Measure this phase against its preserved, per-module source index.

Capturing an index requires the previous accepted source archive; ordinary runs
only read the existing index and measure the current Wu source tree.
"""
from pathlib import Path
import argparse, json, hashlib, importlib.util, re, tarfile, datetime
root = Path(__file__).resolve().parents[2]
wu = root/'research/wu2008'
out = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--capture-baseline', type=Path)
args = parser.parse_args()
spec = importlib.util.spec_from_file_location('checks', root/'scripts/check.py')
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)
pat = re.compile(r'^\s*(?:(?:public|meta)\s+)*import\s+(.+)', re.M)
def entry(raw):
    t = raw.decode()
    return {'code_lines':checks.count_code_lines(t), 'physical_lines':len(t.splitlines()),
            'utf8_bytes':len(raw), 'sha256':hashlib.sha256(raw).hexdigest(),
            'imports':[n for m in pat.finditer(checks.code_only(t)) for n in m.group(1).split()]}
if args.capture_baseline:
    assert not (out/'baseline-source-index.json').exists(), 'Baseline already captured'
    old = {}
    with tarfile.open(args.capture_baseline) as tf:
        for m in tf:
            if m.name.startswith('src/') and m.name.endswith('.lean'):
                old[m.name[4:-5].replace('/','.')] = entry(tf.extractfile(m).read())
    (out/'baseline-source-index.json').write_text(json.dumps(old,indent=2)+'\n')
else:
    old = json.loads((out/'baseline-source-index.json').read_text())
new = {str(p.relative_to(wu/'src').with_suffix('')).replace('/','.'):entry(p.read_bytes()) for p in (wu/'src').rglob('*.lean')}
def closure(data):
    seen=set();todo=['WR2ClassicalCertificate']
    while todo:
        n=todo.pop()
        if n in seen:continue
        seen.add(n);todo.extend(x for x in data[n]['imports'] if x in data)
    return seen
def stat(data, names):
    return {'modules':len(names), **{k:sum(data[m][k] for m in names) for k in ['code_lines','physical_lines','utf8_bytes']}}
r={'measured_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
   'baseline':'Previous accepted precision-preserving phase: 5441 modules, 755925 closure code lines.',
   'root':'WR2ClassicalCertificate','endpoint':'WuPaper.ClassicalSlots.one8938',
   'method':'Local whole-module counts; comments and blank lines excluded from effective code, strings retained; all new helpers and endpoint declarations included; external Lake dependencies excluded.'}
for scope,select in [('whole_tree',lambda d:set(d)),('theorem_closure',closure)]:
    a=stat(old,select(old));b=stat(new,select(new))
    r[scope]={'before':a,'after':b,'reduction':{k:a[k]-b[k] for k in a},'code_reduction_percent':100*(a['code_lines']-b['code_lines'])/a['code_lines']}
r['modified_modules']=sorted(n for n in old.keys()&new.keys() if old[n]['sha256']!=new[n]['sha256'])
r['added_modules']=sorted(new.keys()-old.keys());r['removed_modules']=sorted(old.keys()-new.keys())
plan=json.loads((out/'generated-change-plan.json').read_text())
allowed=set(plan['before'])|{'WR2XiSourceRefinedTarget','WR2ClassicalCertificate'}
assert not set(r['modified_modules'])-allowed
assert not set(r['removed_modules'])-set(plan['before'])
r['unchanged_outside_cohort']=sum(n not in allowed and old[n]['sha256']==new[n]['sha256'] for n in old.keys()&new.keys())
r['unchanged_payment_tables']={n:new[n]['sha256'] for n in ['WR2ClassicalCPayments','WR2ClassicalEighthRawPayments']}
for n,h in r['unchanged_payment_tables'].items():assert old[n]['sha256']==h
r['cumulative_from_original']={k:json.loads((out/'previous-stage-size.json').read_text())['theorem_closure']['before'][k]-r['theorem_closure']['after'][k] for k in r['theorem_closure']['after']}
(out/'source-size.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:v for k,v in r.items() if not isinstance(v,list)},indent=2))
