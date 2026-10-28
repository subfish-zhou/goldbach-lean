"""Verify the exact source inventory, preserved numeric tables and source bans."""
from pathlib import Path
import json, hashlib, importlib.util, re
root=Path(__file__).resolve().parents[2];wu=root/'research/wu2008';out=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('checks',root/'scripts/check.py');checks=importlib.util.module_from_spec(spec);spec.loader.exec_module(checks)
old=json.loads((out/'baseline-source-index.json').read_text());plan=json.loads((out/'generated-change-plan.json').read_text());allowed=set(plan['before'])|{'WR2XiSourceRefinedTarget','WR2ClassicalCertificate'}
new={'.'.join(p.relative_to(wu/'src').with_suffix('').parts):p for p in (wu/'src').rglob('*.lean')}
unchanged=0
for name,row in old.items():
 if name not in allowed:
  assert hashlib.sha256(new[name].read_bytes()).hexdigest()==row['sha256'],name
  unchanged+=1
bad=[]
for name,p in new.items():
 if re.search(r'\b(?:sorry|admit|native_decide|axiom|unsafe)\b',checks.code_only(p.read_text())):bad.append(name)
assert not bad,bad
previous=json.loads((root/'research/wu-precision-audit/source-invariants.json').read_text())['unchanged_numeric_tables']
tables={p[4:-5].replace('/','.'):h for p,h in previous.items()}
tables.update({n:old[n]['sha256'] for n in ['WR2ClassicalCPayments','WR2ClassicalEighthRawPayments']})
for n,h in tables.items():assert hashlib.sha256(new[n].read_bytes()).hexdigest()==h,n
result={'status':'pass','modules':len(new),'unchanged_outside_cohort':unchanged,'unchanged_numeric_tables':tables,'prohibited_tokens':bad}
(out/'source-invariants.json').write_text(json.dumps(result,indent=2)+'\n');print('SOURCE_INVARIANTS_PASS',len(new),'modules;',len(tables),'byte-identical tables')
