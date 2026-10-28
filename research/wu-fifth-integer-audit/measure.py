"""Count this phase against its frozen source index; not Lean acceptance."""
from pathlib import Path
import json,hashlib,importlib.util,re
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];SRC=ROOT/'research/wu2008/src'
spec=importlib.util.spec_from_file_location('checks',ROOT/'scripts/check.py');checks=importlib.util.module_from_spec(spec);spec.loader.exec_module(checks)
before=json.loads((HERE/'baseline-source-index.json').read_text());after={}
for p in SRC.rglob('*.lean'):
 n='.'.join(p.relative_to(SRC).with_suffix('').parts);raw=p.read_bytes();h=hashlib.sha256(raw).hexdigest()
 if n in before and before[n]['sha256']==h:after[n]=before[n];continue
 t=raw.decode();code=checks.code_only(t);assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b|debug\.skipKernelTC',code),n
 after[n]=dict(sha256=h,code_lines=checks.count_code_lines(t),physical_lines=len(t.splitlines()),utf8_bytes=len(raw),imports=re.findall(r'^import (\S+)',code,re.M))
def closure(data):
 seen=set();todo=['WR2ClassicalCertificate']
 while todo:
  n=todo.pop()
  if n in seen or n not in data:continue
  seen.add(n);todo.extend(data[n]['imports'])
 return seen
def stat(data,ns):return dict(modules=len(ns),**{k:sum(data[n][k] for n in ns) for k in ['code_lines','physical_lines','utf8_bytes']})
report={}
for scope,select in [('whole_tree',set),('theorem_closure',closure)]:
 a=stat(before,select(before));b=stat(after,select(after));report[scope]=dict(before=a,after=b,reduction={k:a[k]-b[k] for k in a})
plan=json.loads((HERE/'adoption.json').read_text());changed={n for n in before.keys()&after.keys() if before[n]['sha256']!=after[n]['sha256']};added=after.keys()-before.keys();removed=before.keys()-after.keys()
assert changed|added=={Path(r['name']).stem for r in plan['adopt']}
assert removed=={Path(n).stem for n in plan['retire']}
for r in plan['adopt']:assert after[Path(r['name']).stem]['sha256']==r['new_sha256'],r['name']
report.update(modified_modules=sorted(changed),added_modules=sorted(added),removed_modules=sorted(removed),unchanged_modules=len(before)-len(changed)-len(removed))
(HERE/'source-size.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({s:report[s] for s in ['whole_tree','theorem_closure']},indent=2))
