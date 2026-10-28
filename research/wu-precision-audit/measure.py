from pathlib import Path
import json,tarfile,importlib.util,re,hashlib,datetime,subprocess,io
root=Path(__file__).resolve().parents[2];wu=root/'research/wu2008';base=root/'research/wu-precision-audit'
spec=importlib.util.spec_from_file_location('checks',root/'scripts/check.py');checks=importlib.util.module_from_spec(spec);spec.loader.exec_module(checks)
old={}
archive=subprocess.check_output(['git','archive','c4e1b8d00dda9661140f95e0f03f0d5a08d636c2','research/wu2008/src'],cwd=root)
with tarfile.open(fileobj=io.BytesIO(archive)) as tf:
 for m in tf:
  if m.name.startswith('research/wu2008/src/') and m.name.endswith('.lean'):old[m.name[len('research/wu2008/src/'):-5].replace('/','.')]=tf.extractfile(m).read().decode()
new={str(p.relative_to(wu/'src').with_suffix('')).replace('/','.'):p.read_text() for p in (wu/'src').rglob('*.lean')}
pat=re.compile(r'^\s*(?:(?:public|meta)\s+)*import\s+(.+)',re.M)
def closure(texts):
 seen=set();todo=['WR2ClassicalCertificate']
 while todo:
  m=todo.pop()
  if m in seen:continue
  seen.add(m);todo.extend(x for a in pat.finditer(checks.code_only(texts[m])) for x in a.group(1).split() if x in texts)
 return seen
metrics={}
def stat(texts,mods):
 key=id(texts)
 if key not in metrics:
  metrics[key]={m:(checks.count_code_lines(t),len(t.splitlines()),len(t.encode())) for m,t in texts.items()}
 counts=metrics[key]
 return dict(modules=len(mods),code_lines=sum(counts[m][0] for m in mods),physical_lines=sum(counts[m][1] for m in mods),utf8_bytes=sum(counts[m][2] for m in mods))
result={'measured_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_commit':'c4e1b8d00dda9661140f95e0f03f0d5a08d636c2','method':'Local Lean source inventory and transitive WR2ClassicalCertificate import closure; comments and blank lines excluded from code lines, strings retained. All four new helper modules included; external Lake dependencies excluded.'}
for key,select in [('whole_tree',lambda t:set(t)),('theorem_closure',closure)]:
 a=stat(old,select(old));b=stat(new,select(new));result[key]={'before':a,'after':b,'reduction':{k:a[k]-b[k] for k in a},'code_reduction_percent':100*(a['code_lines']-b['code_lines'])/a['code_lines']}
result['unchanged_retained_modules']=sum(old[m]==new[m] for m in old.keys()&new.keys())
result['modified_modules']=sorted(m for m in old.keys()&new.keys() if old[m]!=new[m]);result['new_modules']=sorted(new.keys()-old.keys());result['removed_modules']=sorted(old.keys()-new.keys())
plan=json.loads((base/'generated-change-plan.json').read_text());result['unchanged_tables']=json.loads((base/'source-invariants.json').read_text())['unchanged_numeric_tables']
out=root/'research/wu-precision-audit';out.mkdir(exist_ok=True);(out/'source-size.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if not isinstance(v,list)},indent=2));print('changed',len(result['modified_modules']),'added',result['new_modules'],'removed',len(result['removed_modules']));print('plan keys',plan.keys())
