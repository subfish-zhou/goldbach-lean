"""Explicit one-time receipt migration; never certify the invalidated closure."""
from pathlib import Path
import json,re,hashlib,tarfile,collections
root=Path('/home/azureuser/goldbach-lean');wu=root/'research/wu2008';out=Path('/tmp/wu-light-layer-production');audit=root/'research/wu-light-layer-audit'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
archive=out/'baseline.tar';manifest_path=wu/'source-manifest.json';current={r['module']:r for r in json.loads(manifest_path.read_text())}
with tarfile.open(archive) as t:
 oldbytes=t.extractfile('source-manifest.json').read();old={r['module']:r for r in json.loads(oldbytes)}
acceptpath=root/'research/wu-fourth-bq-audit/validation.json';accept=json.loads(acceptpath.read_text());assert accept['status']=='pass' and accept['modules']==4267 and accept['manifest_sha256']==hashlib.sha256(oldbytes).hexdigest()
assert not (out/'receipts-pre-context.tar').exists(),'Migration already begun; inspect before retry'
changed={n for n,r in current.items() if n not in old or any(r[k]!=old[n][k] for k in ['source_sha256','imports'])}
reverse=collections.defaultdict(set)
for n,r in current.items():
 for d in r['imports']:reverse[d].add(n)
def descendants(seeds):
 seen=set(seeds);todo=list(seeds)
 while todo:
  for n in reverse[todo.pop()]-seen:seen.add(n);todo.append(n)
 return seen
affected=descendants(changed);lines=(out/'full-build.log').read_text();assert 'BUILD_PASS 4181' in lines
compiled={m[1]:float(m[2]) for m in re.finditer(r'^(\S+) 0 ([0-9.]+)$',lines,re.M)};assert set(compiled)<=affected
invalid=descendants(affected-set(compiled));allowed=current.keys()-invalid;unaffected=current.keys()-affected
assert len(invalid)==55 and len(allowed)==4126 and len(unaffected)==4011
order=[];seen=set()
def visit(n):
 if n not in current or n in seen:return
 seen.add(n)
 for d in current[n]['imports']:visit(d)
 order.append(n)
for n in current:visit(n)
contexts={};records={};evidence={};receipt_inputs={};manifest_digest=sha(manifest_path)
for n in order:
 rel=Path(*n.split('.'));rp=(wu/'build/receipts'/rel).with_suffix('.json');source=(wu/'src'/rel).with_suffix('.lean');obj=(wu/'build/lib'/rel).with_suffix('.olean');r=json.loads(rp.read_text());receipt_inputs[rp]=sha(rp)
 assert r['exit_code']==0 and not r.get('direct_check_only'),n
 assert r['source_sha256']==current[n]['source_sha256']==sha(source),n
 assert r['object_sha256']==sha(obj),n
 deps={d:json.loads((wu/'build/receipts'/Path(*d.split('.'))).with_suffix('.json').read_text())['object_sha256'] for d in current[n]['imports'] if d in current}
 assert r['dependencies']==deps,n
 log=wu/r['log'];assert sha(log)==r['log_sha256'],n
 logged=json.loads(log.with_suffix('.json').read_text())
 for k in ['source_sha256','object_sha256','dependencies','command','exit_code']:assert r[k]==logged[k],(n,k)
 assert r['command'][0].endswith('/leanprover--lean4---v4.33.0-rc1/bin/lean') and '-DwarningAsError=true' in r['command'],n
 if n.startswith(('W','R2')):assert '-DautoImplicit=false' in r['command'],n
 if n in invalid:continue
 assert all(d in contexts for d in deps),n
 if n in unaffected:
  assert all(d in unaffected for d in deps),n
  assert old[n]['source_sha256']==r['source_sha256'] and old[n]['imports']==current[n]['imports'],n
  basis='same full source/import closure as accepted4267; strict unchanged receipts verified'
 else:
  assert n in compiled and abs(r['seconds']-compiled[n])<=0.0051,n
  assert int(re.search(r'-(\d+)\.log$',str(log))[1])>archive.stat().st_mtime_ns,n
  basis='compiled in current completed build; every local ancestor independently admitted'
 parents={d:contexts[d] for d in deps};payload={'source_sha256':r['source_sha256'],'object_sha256':r['object_sha256'],'dependency_contexts':parents};digest=hashlib.sha256(json.dumps(payload,sort_keys=True,separators=(',',':')).encode()).hexdigest()
 evidence[n]={'basis':basis,'old_receipt_sha256':sha(rp),'source_sha256':r['source_sha256'],'object_sha256':r['object_sha256'],'log_sha256':r['log_sha256'],'context_sha256':digest}
 r.update(dependency_contexts=parents,context_sha256=digest,context_migration={'basis':basis,'accepted_baseline_manifest':accept['manifest_sha256'],'original_receipt_sha256':sha(rp)})
 contexts[n]=digest;records[rp]=r
assert len(records)==4126
# No mutation before all evidence and ancestor-closure checks have passed.
assert sha(manifest_path)==manifest_digest
for rp,h in receipt_inputs.items():assert sha(rp)==h, str(rp)
with tarfile.open(out/'receipts-pre-context.tar','w') as t:t.add(wu/'build/receipts',arcname='receipts')
for rp,r in records.items():rp.write_text(json.dumps(r,indent=2)+'\n')
for n in invalid:(wu/'build/receipts'/Path(*n.split('.'))).with_suffix('.json').unlink()
report={'status':'migration_complete_pending_rebuild_and_kernel_acceptance','manifest_sha256':sha(manifest_path),'baseline_archive_sha256':sha(archive),'baseline_acceptance_path':str(acceptpath.relative_to(root)),'baseline_acceptance_sha256':sha(acceptpath),'baseline_assumption':'Previously accepted proof objects under the same pinned Lean/toolchain and package environment; source archive alone is not object acceptance. Every reused receipt/log/object/dependency independently checked.','fresh_success_log_sha256':sha(out/'full-build.log'),'receipt_backup_sha256':sha(out/'receipts-pre-context.tar'),'unaffected_baseline_modules':len(unaffected),'admitted_current_fresh_modules':len(allowed-unaffected),'invalidated_modules':sorted(invalid),'modules':evidence}
(audit/'context-migration.json').write_text(json.dumps(report,indent=2)+'\n');print('MIGRATED4126; INVALIDATED55; full rebuild+kernel still required',flush=True)
