from pathlib import Path
import json,hashlib,importlib.util,re,subprocess,tarfile,io
repo=Path(__file__).resolve().parents[2];wu=repo/'research/wu2008';base=repo/'research/wu-precision-audit';plan=json.loads((base/'generated-change-plan.json').read_text());old={}
archive=subprocess.check_output(['git','archive','c4e1b8d00dda9661140f95e0f03f0d5a08d636c2','research/wu2008/src'],cwd=repo)
with tarfile.open(fileobj=io.BytesIO(archive)) as tf:
 for m in tf:
  if m.isfile() and m.name.endswith('.lean'):old[m.name[len('research/wu2008/'):]]=hashlib.sha256(tf.extractfile(m).read()).hexdigest()
spec=importlib.util.spec_from_file_location('checks',repo/'scripts/check.py');checks=importlib.util.module_from_spec(spec);spec.loader.exec_module(checks)
generated={f'src/{m.replace(".","/")}.lean' for m in plan['before']};unchanged=0;bad=[]
for p,h in old.items():
 if not p.startswith('src/') or p in generated:continue
 assert hashlib.sha256((wu/p).read_bytes()).hexdigest()==h,p
 unchanged+=1
for p in (wu/'src').rglob('*.lean'):
 code=checks.code_only(p.read_text())
 if re.search(r'\b(?:sorry|admit|native_decide|axiom|unsafe)\b',code):bad.append(str(p.relative_to(wu)))
assert not bad,bad
result={'status':'pass','unchanged_non_generated_original_modules':unchanged,'scanned_current_modules':len(list((wu/'src').rglob('*.lean'))),'prohibited_tokens':bad,'unchanged_numeric_tables':{p:hashlib.sha256((wu/p).read_bytes()).hexdigest() for p in old if p.startswith('src/') and ('ClassicalFourthData' in p or re.search(r'WR2Classical(?:Fifth|Sixth).*Payments\.lean$',p))}}
assert len(result['unchanged_numeric_tables'])==11
for p,h in result['unchanged_numeric_tables'].items():assert h==old[p],p
(repo/'research/wu-precision-audit/source-invariants.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
