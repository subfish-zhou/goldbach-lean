"""Read-only default; adopt only exact completed Hf4 proof and validation artifacts."""
from pathlib import Path
import argparse,ast,fcntl,hashlib,importlib.util,json,os,re,shutil,signal,sys,time
import core,sourceaudit,export_review,toolchain_review
ROOT=Path('/home/azureuser/goldbach-lean/research/wu2008');HERE=Path(__file__).resolve().parent
B=Path('/tmp/wu-hf4-installed-v7-resume-v1');PRODUCER=Path('/tmp/wu-hf4-portable-producer-v3');SUFFIXES=['.olean','.olean.server','.olean.private','.ir','.ir.sig'];sha=core.sha;save=core.save
SUCCESS='FULL_4151_CONTEXTS_696_TYPES_183_RAW_VALUES_19_KERNELS_LITERAL_AXIOMS_PRODUCER_PASS_NOT_ADOPTED'
def rel(n,s):return Path(*n.split('.')).with_suffix(s)
def load(name,p):
 s=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m

def gate_report(report,P,run):
 assert report['status']==SUCCESS and report['run']==str(run)
 assert report['types']==696 and report['values']==183 and report['kernels']==19
 assert report['source_proofs']==389 and report['reused_original_source_proofs']==53 and report['new_source_compilations']==336
 targets=[n for n in P['affected']if n in P['overlay']]+['WR2ClassicalCertificate'];assert len(targets)==19
 labels=['before-types','after-types','before-values','after-values','literal-axioms']+['kernel-'+n for n in targets]+['producer-check']
 assert [r['label']for r in report['steps']]==labels
 assert all(type(r['exit_code'])is int and r['exit_code']==0 for r in report['steps'])
 return targets

def collect(run,validation):
 P=json.loads((B/'plan.json').read_text());assert P==json.loads((run/'plan.json').read_text());pins=json.loads((B/'after-source-pins.json').read_text());assert pins['run']==str(run)and sha(B/'validate.py')==pins['validator_sha256'];assert sha(B/'plan.json')==pins['plan_sha256']
 report=json.loads((validation/'report.json').read_text());targets=gate_report(report,P,run);chain=toolchain_review.review(P);inputs=dict(chain['bindings']);capture=lambda p:inputs.setdefault(str(p),sha(p))
 for p in [B/'plan.json',B/'after-source-pins.json',B/'validate.py',run/'plan.json',run/'results.json',run/'verified-resume-prefix.json',validation/'report.json',HERE/'adopt.py',HERE/'core.py',HERE/'sourceaudit.py',HERE/'export_review.py',HERE/'toolchain_review.py']:capture(p)
 # Ensure the extracted audit body is precisely the validator's actual body.
 tree=ast.parse((B/'validate.py').read_text());main=next(n for n in tree.body if isinstance(n,ast.FunctionDef)and n.name=='main');expected=next(n for n in main.body if isinstance(n,ast.FunctionDef)and n.name=='audit');actual=next(n for n in ast.parse((HERE/'sourceaudit.py').read_text()).body if isinstance(n,ast.FunctionDef)and n.name=='audit');assert ast.dump(ast.Module(body=expected.body,type_ignores=[]))==ast.dump(ast.Module(body=actual.body,type_ignores=[]))
 facts=sourceaudit.audit(run,P);assert sourceaudit.digest(facts)==report['context_digest'];assert json.loads((validation/'context-before.json').read_text())==json.loads((validation/'context-after.json').read_text())==facts
 for p,h in report['bindings'].items():assert sha(Path(p))==h;capture(Path(p))
 for row in report['steps']:
  label=row['label'];log=validation/(label+'.log');resource=validation/(label+'.resources');assert sha(log)==row['log_sha256']and sha(resource)==row['resources_sha256'];inv=validation/(label+'.invocation.json');j=json.loads(inv.read_text());assert j['environment']['LEAN_SYSROOT']==P['sysroot'];assert j['command'][0]in[P['lean'],str(Path(P['sysroot'])/'bin/leanchecker'),sys.executable]
  for p in [log,resource,inv]:capture(p)
 for n in targets:
  j=json.loads((validation/('kernel-'+n+'.invocation.json')).read_text());assert j['command']==[str(Path(P['sysroot'])/'bin/leanchecker'),'--verbose',n];assert j['environment']['LEAN_PATH']==':'.join([str(run/'lib'),*P['package_paths']]);assert(validation/('kernel-'+n+'.log')).read_text().strip()=='replaying '+n
 for p,h in export_review.review(validation,P,run,ROOT).items():assert sha(Path(p))==h;capture(Path(p))
 for suffix in ['types','values']:
  before=validation/('before-'+suffix+'.json');after=validation/('after-'+suffix+'.json');assert json.loads(before.read_text())==json.loads(after.read_text());capture(before);capture(after)
 checks=load('release_checks',ROOT.parents[1]/'scripts/check.py');checks.check_axiom_output((validation/'literal-axioms.log').read_text(),{'WuPaper.ClassicalSlots.one8938','WuPaper.ClassicalSlots.one894','WuPaper.ClassicalSlots.classical_lower','WuLiteralAcceptance','WuLegacyLiteralAcceptance'})
 prodcheck=load('production_build_check',ROOT/'check_classical.py');oldobjects=prodcheck.verify_build();assert set(oldobjects)==set(P['production_sources'])
 for root,suffix in [('src','.lean'),('build/lib','.olean'),('build/receipts','.json')]:assert {str(p.relative_to(ROOT/root).with_suffix('')).replace('/','.')for p in(ROOT/root).rglob('*'+suffix)}==set(P['production_sources'])
 for n in P['production_sources']:
  p=ROOT/'build/receipts'/rel(n,'.json');r=json.loads(p.read_text());assert type(r['exit_code'])is int and r['exit_code']==0;capture(p)
 for name in ['source-manifest.json','build/STATUS.json','build/PLAN.json','build/classical-acceptance.json','build/classical-literal-axioms.log']:
  p=ROOT/name
  if p.exists():capture(p)
 producer=load('portable_constructive_producer',PRODUCER/'produce.py');outputs,_=producer.generate('constructive');assert len(outputs)==17
 for name,data in outputs.items():assert(run/'sources'/name).read_bytes()==data
 package={str(p.relative_to(PRODUCER)):sha(p)for p in PRODUCER.rglob('*')if p.is_file()and '__pycache__'not in p.parts and p.name!='test-actual.log'}
 for name,h in package.items():assert sha(PRODUCER/name)==h;capture(PRODUCER/name)
 retirement=Path('/tmp/wu-hf4-installed-v7-candidate-v1/retirement-review.json');review=json.loads(retirement.read_text());assert review['plan_sha256']==sha(B/'plan.json')and not review['retired_source_registration_commands']and not review['baseline_reference_audit']['unpreserved_resolved_references']and not review['new_reference_audit']['unpreserved_resolved_references'];capture(retirement)
 manifest=json.loads((ROOT/'source-manifest.json').read_text());old={r['module']:r for r in manifest};new=[]
 for n in sorted(P['order']):
  row=dict(old.get(n,dict(module=n)));row.update(source_sha256=P['candidate_sources'][n],object_sha256=facts[n]['object'])
  if n in P['overlay']:
   text=(run/'sources'/rel(n,'.lean')).read_text();imports=[x for line in re.findall(r'^\s*(?:(?:public|meta)\s+)*import\s+([^\n]+)',checks.code_only(text),re.M)for x in line.split()];row['imports']=['Init']+imports;row['source_binding']='isolated_constructive_hf4_exact_snapshot'
  assert [d for d in row['imports']if d in facts]==P['graph'][n];new.append(row)
 assert len(new)==4151
 for p,h in inputs.items():assert sha(Path(p))==h,p
 return dict(plan=P,report=report,facts=facts,manifest=new,inputs=inputs,package=package,retirement_review=str(retirement),toolchain_review=chain)

def transact(run,validation,V,tracker):
 P=V['plan'];facts=V['facts'];tx=ROOT/'build/adoptions'/('hf4-constructive-v1-'+str(time.time_ns()));tx.mkdir();E=tx/'evidence';E.mkdir();items=[];staged=set()
 def evidence(p,name):
  p=Path(p);q=E/name;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q);assert sha(q)==sha(p);return str(q.relative_to(ROOT))
 def stage(name,origin=None,data=None):
  assert name not in staged;staged.add(name);target=ROOT/name;assert not target.is_symlink()and not target.is_dir();q=tx/'stage'/name
  if origin is not None or data is not None:
   q.parent.mkdir(parents=True,exist_ok=True)
   if origin is not None:shutil.copyfile(origin,q);assert sha(q)==sha(Path(origin))
   else:q.write_bytes(data)
  items.append(dict(target=name,old_sha256=sha(target)if target.exists()else None,new_sha256=sha(q)if q.exists()else None))
 for p,name in [(HERE/'adopt.py','adopt.py'),(HERE/'core.py','core.py'),(HERE/'sourceaudit.py','sourceaudit.py'),(HERE/'export_review.py','export_review.py'),(HERE/'toolchain_review.py','toolchain_review.py'),(B/'plan.json','plan.json'),(ROOT/'source-manifest.json','old-source-manifest.json'),(Path(V['retirement_review']),'retirement-review.json')]:evidence(p,name)
 save(E/'input-bindings.json',V['inputs']);save(E/'toolchain-review.json',V['toolchain_review'])
 for p in [B/'validate.py',B/'run.py',B/'resume-inputs.json',B/'after-source.py',B/'after-source-pins.json',ROOT/'build.py',ROOT/'check_classical.py',ROOT.parents[1]/'scripts/check.py',Path('/tmp/wu-hf4-safe-probes/dag-v2/owned_process.py')]:evidence(p,Path('tools')/p.name)
 for p in validation.rglob('*'):
  if p.is_file():evidence(p,Path('validation')/p.relative_to(validation))
 for p in [run/'results.json',run/'verified-base-receipts.json',run/'verified-resume-prefix.json',run/'STATUS.json']:evidence(p,p.name)
 rows=json.loads((run/'results.json').read_text())
 for r in rows:
  n=r['module'];source=evidence(run/'sources'/rel(n,'.lean'),Path('sources')/rel(n,'.lean'));original=evidence(run/'receipts'/rel(n,'.json'),Path('original-receipts')/rel(n,'.json'));log=evidence(Path(r['log']),Path('logs')/(n+'.log'));resource=evidence(Path(r['resource_log']),Path('logs')/(n+'.resources'))
  promoted={**r,'log':log,'resource_log':resource,'adoption':dict(kind='exact_constructive_hf4_source_proof_adoption_not_recompilation',archived_source=source,original_receipt=original,original_receipt_sha256=sha(run/'receipts'/rel(n,'.json')),source_carrier_run=str(run),validation_report_sha256=sha(validation/'report.json'))}
  assert promoted['command']==r['command']and promoted['execution_command']==r['execution_command'];stage(str(Path('build/receipts')/rel(n,'.json')),data=(json.dumps(promoted,indent=2)+'\n').encode())
  for suffix in SUFFIXES:
   src=run/'lib'/rel(n,suffix);name=str(Path('build/lib')/rel(n,suffix))
   if src.exists():stage(name,origin=src)
   elif(ROOT/name).exists():stage(name)
  if 'resumed_proof_origin'in r:
   origin=r['resumed_proof_origin'];evidence(Path(origin['original_receipt']),Path('prefix-original-receipts')/rel(n,'.json'));evidence(Path(origin['original_invocation']),Path('prefix-original-invocations')/(n+'.json'))
 for n in P['overlay']:stage(str(Path('src')/rel(n,'.lean')),origin=run/'sources'/rel(n,'.lean'))
 for n in P['retired']:
  evidence(ROOT/'src'/rel(n,'.lean'),Path('retired-sources')/rel(n,'.lean'));stage(str(Path('src')/rel(n,'.lean')));stage(str(Path('build/receipts')/rel(n,'.json')))
  for suffix in SUFFIXES:
   name=str(Path('build/lib')/rel(n,suffix))
   if(ROOT/name).exists():stage(name)
 for name,h in V['package'].items():
  dst=str(Path('diagnostics/hf4_constructive')/name);assert not(ROOT/dst).exists();stage(dst,origin=PRODUCER/name)
 stage('source-manifest.json',data=(json.dumps(V['manifest'],indent=2)+'\n').encode())
 stage('build/STATUS.json',data=(json.dumps(dict(status='adopted_pending_production_verification',transaction=str(tx),source_proofs=389,actual_original_prefix=53,new_source_compilations=336,verified_unchanged=3762),indent=2)+'\n').encode())
 # Include post-check metadata in the rollback set even though these start unchanged.
 for name in ['build/PLAN.json','build/classical-acceptance.json','build/classical-literal-axioms.log']:
  if(ROOT/name).exists():stage(name,origin=ROOT/name)
 core.ROOT=ROOT;core.ALLOWED=frozenset(staged);save(E/'allowed-targets.json',sorted(staged));journal=dict(phase='prepared',run=str(run),validation=str(validation),items=items);save(tx/'journal.json',journal)
 for item in items:
  p=core.valid_target(item['target']);assert(sha(p)if p.exists()else None)==item['old_sha256']
  if p.exists():q=tx/'backup'/item['target'];q.parent.mkdir(parents=True,exist_ok=True);os.link(p,q)
 for p,h in V['inputs'].items():assert sha(Path(p))==h,p
 assert sourceaudit.audit(run,P)==facts
 def installed():
  for area,suffix in [('src','.lean'),('build/lib','.olean'),('build/receipts','.json')]:assert {str(p.relative_to(ROOT/area).with_suffix('')).replace('/','.')for p in(ROOT/area).rglob('*'+suffix)}==set(P['order'])
  for n in P['order']:
   f=facts[n];r=json.loads((ROOT/'build/receipts'/rel(n,'.json')).read_text());assert sha(ROOT/'src'/rel(n,'.lean'))==f['source']==r['source_sha256'];assert sha(ROOT/'build/lib'/rel(n,'.olean'))==f['object']==r['object_sha256'];assert r['context_sha256']==f['context'];assert r['dependencies']=={d:facts[d]['object']for d in P['graph'][n]};assert r['dependency_contexts']=={d:facts[d]['context']for d in P['graph'][n]}
   assert {s:sha(ROOT/'build/lib'/rel(n,s))for s in SUFFIXES if(ROOT/'build/lib'/rel(n,s)).exists()}==f['bundle']
 core.commit_items(tx,journal,installed)
 env=os.environ.copy();env.pop('LEAN_PATH',None);env.pop('LEAN_SRC_PATH',None);env['LEAN_SYSROOT']=P['sysroot'];steps=[]
 def command(label,cmd,environment=None):
  log=E/(label+'.log');start=time.monotonic();en=environment or env
  with log.open('w')as f:p=tracker.Popen(cmd,cwd=ROOT,env=en,stdout=f,stderr=tracker.STDOUT,start_new_session=True);rc=p.wait(timeout=1800)
  tracker.cleanup();row=dict(label=label,command=cmd,environment={k:en.get(k)for k in ['LEAN_PATH','LEAN_SYSROOT']},exit_code=rc,seconds=time.monotonic()-start,log_sha256=sha(log));steps.append(row);save(E/'production-verification.json',dict(status='PENDING',steps=steps));assert type(rc)is int and rc==0,label;return log.read_text()
 try:
  command('production-producer-check',[sys.executable,str(ROOT/'diagnostics/hf4_constructive/produce.py'),'--route','constructive','--output-dir',str(ROOT/'src'),'--check'])
  text=command('production-build',[sys.executable,str(ROOT/'build.py'),'--all','--jobs','1','--lean-threads','1','--limit','0']);assert text.strip()=='BUILD_PASS 4151',text
  command('production-literal-axioms',[sys.executable,str(ROOT/'check_classical.py')]);en=env.copy();en['LEAN_PATH']=':'.join([str(ROOT/'build/lib'),*P['package_paths']]);text=command('production-final-kernel',[str(Path(P['sysroot'])/'bin/leanchecker'),'--verbose','WR2ClassicalCertificate'],en);assert text.strip()=='replaying WR2ClassicalCertificate';installed()
 except BaseException as exc:
  journal.update(phase='rollback_needed',error_type=type(exc).__name__,error=str(exc));save(tx/'journal.json',journal);core.restore(tx);raise
 save(E/'production-verification.json',dict(status='PRODUCTION_4151_PRODUCER_RECEIPTS_LITERAL_AXIOMS_FINAL_KERNEL_PASS',steps=steps,manifest_sha256=sha(ROOT/'source-manifest.json'),source_proofs=389,genuine_original_prefix=53,new_compilations=336,verified_unchanged=3762));journal.update(phase='production_verified',production_verification_sha256=sha(E/'production-verification.json'));save(tx/'journal.json',journal);print(json.dumps(dict(status='production_verified',transaction=str(tx),targets=len(items))))

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--run',type=Path,required=True);ap.add_argument('--validation',type=Path,required=True);ap.add_argument('--execute',action='store_true');a=ap.parse_args();run=a.run.resolve();validation=a.validation.resolve();V=collect(run,validation);size=sum((run/'lib'/rel(n,s)).stat().st_size for n in V['plan']['affected']for s in SUFFIXES if(run/'lib'/rel(n,s)).exists());required=2*size+300_000_000;free=shutil.disk_usage(ROOT).free;assert free>required
 if not a.execute:print(json.dumps(dict(status='READ_ONLY_FULL_DRY_RUN_PASS_NOT_ADOPTED',artifact_bytes=size,required_free=required,free=free,inputs=len(V['inputs']))));return
 helper=Path('/tmp/wu-hf4-safe-probes/dag-v2');sys.path.insert(0,str(helper));import owned_process;safe=load('safe',helper/'run.py');safe.no_live_lean()
 with Path('/tmp/wu-lean-exclusive.lock').open('a')as lock:
  fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);safe.no_live_lean();V=collect(run,validation);tracker=owned_process.TrackedSubprocess(run=ROOT);old={s:signal.getsignal(s)for s in [signal.SIGINT,signal.SIGTERM]}
  for s in old:signal.signal(s,owned_process.interrupted)
  try:transact(run,validation,V,tracker)
  finally:
   tracker.cleanup()
   for s,h in old.items():signal.signal(s,h)
if __name__=='__main__':main()
