"""Validate a completed isolated Hf4 source run; never install or relax data checks."""
from pathlib import Path
import argparse,hashlib,json,os,sys,importlib.util,fcntl,signal,time,subprocess
B=Path(__file__).resolve().parent;ROOT=Path('/home/azureuser/goldbach-lean/research/wu2008');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,d):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
def rel(n,s):return Path(*n.split('.')).with_suffix(s)
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def load(name,p):
 s=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--run',type=Path,required=True);ap.add_argument('--execute',action='store_true');args=ap.parse_args();run=args.run.resolve();P=json.loads((run/'plan.json').read_text());assert P==json.loads((B/'plan.json').read_text());status=json.loads((run/'STATUS.json').read_text());assert status['status']=='FULL_SOURCE_4151_COMPILED_NOT_KERNEL_INTERFACE_OR_ADOPTION_ACCEPTANCE'
 names0=json.loads(Path('/tmp/wu-structural-interface-selection-v2/types-unicode-names.json').read_text());retired=json.loads(Path('/tmp/wu-hf4-post-v5-integration-v2/retired-declarations.json').read_text());dropped={r['qname']for r in retired['declarations']if r['disposition']!='RELOCATED_EXACT40HEADER'}&set(names0);assert dropped=={f'Hf4Quad.Panel{i}.compact_model'for i in range(40)};names=[n for n in names0 if n not in dropped];assert len(names)==696
 mods=json.loads(Path('/tmp/wu-structural-interface-selection-v2/types-unicode-modules.json').read_text())['modules']['after'];beforemods=mods;aftermods=[m for m in mods if m not in P['retired']]+['Hf4ConstructiveTablePublic'];assert len(aftermods)==len(set(aftermods))
 def audit():
  fresh=json.loads((run/'results.json').read_text());base=json.loads((run/'verified-base-receipts.json').read_text());assert len(fresh)==389 and len(base)==3762;F={r['module']:r for r in fresh};assert set(F)==set(P['affected']);assert set(base)==set(P['unchanged']);assert set(F)|set(base)==set(P['order']);hashes={};contexts={};facts={}
  for n in P['order']:
   r=F.get(n,base.get(n));s=run/'sources'/rel(n,'.lean');o=run/'lib'/rel(n,'.olean');assert sha(s)==P['candidate_sources'][n]==r['source_sha256'];assert sha(o)==r['object_sha256'];deps={d:hashes[d]for d in P['graph'][n]};dcs={d:contexts[d]for d in deps};assert r['dependencies']==deps and r['dependency_contexts']==dcs;ctx=digest(dict(source_sha256=r['source_sha256'],object_sha256=r['object_sha256'],dependency_contexts=dcs));assert ctx==r['context_sha256']
   assert r['artifact_bundle_sha256']=={x:sha(run/'lib'/rel(n,x))for x in r['artifact_bundle_sha256']}
   if n in F:
    assert type(r['exit_code'])is int and r['exit_code']==0;assert sha(Path(r['log']))==r['log_sha256'];assert sha(Path(r['resource_log']))==r['resource_sha256'];cmd=r['command'];assert cmd[0]==P['lean']and '-j1'in cmd and '-DwarningAsError=true'in cmd;assert cmd[-1]==str(s)and cmd[cmd.index('-o')+1]==str(o);assert ([x for x in cmd if x.startswith('-DautoImplicit=')]==([P['policies'][n]]if P['policies'][n]else []))
   else:
    rp=Path(r['receipt_path']);assert sha(rp)==r['receipt_sha256'];orig=json.loads(rp.read_text());assert orig['exit_code']==0 and sha(ROOT/orig['log'])==orig['log_sha256'];assert orig['context_sha256']==ctx
   hashes[n]=r['object_sha256'];contexts[n]=ctx;facts[n]=dict(source=r['source_sha256'],object=hashes[n],context=ctx,bundle=r['artifact_bundle_sha256'])
  for n in P['retired']:assert not(run/'lib'/rel(n,'.olean')).exists() and not(run/'sources'/rel(n,'.lean')).exists()
  assert sha(ROOT/'source-manifest.json')==P['baseline_manifest_sha256']
  for n,h in P['production_sources'].items():assert sha(ROOT/'src'/rel(n,'.lean'))==h
  return facts
 initial=audit()
 if not args.execute:print('FULL_CONTEXT_AUDIT_PASS_NOT_GATES');return
 helper=Path('/tmp/wu-hf4-safe-probes/dag-v2');sys.path.insert(0,str(helper));import owned_process
 safe=load('safe',helper/'run.py');safe.no_live_lean()
 with Path('/tmp/wu-lean-exclusive.lock').open('a')as lock:
  fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);safe.no_live_lean();out=B/('validation-'+str(time.time_ns()));out.mkdir();save(out/'context-before.json',initial);save(out/'retired-previous-interfaces.json',sorted(dropped));report=dict(status='RUNNING_NOT_ADOPTED',run=str(run),steps=[],types=696,explicitly_retired_old_models=40,context_digest=digest(initial));save(out/'report.json',report)
  env=os.environ.copy()
  for k in ['LEAN_PATH','LEAN_SYSROOT','LEAN_SRC_PATH']:env.pop(k,None)
  env['LEAN_SYSROOT']=P['sysroot'];env['LEAN_PATH']=':'.join([str(run/'lib'),*P['package_paths']]);env['TMPDIR']=str(out/'tmp');(out/'tmp').mkdir()
  bindings={**P['bindings'],str(B/'validate.py'):sha(B/'validate.py'),str(B/'plan.json'):sha(B/'plan.json')};templatefile=Path('/tmp/wu-public-interface-audit-v2/InterfaceTemplate.lean');bindings[str(templatefile)]=sha(templatefile);template=templatefile.read_text();tracker=owned_process.TrackedSubprocess(run=out);old={s:signal.getsignal(s)for s in [signal.SIGINT,signal.SIGTERM]}
  for s in old:signal.signal(s,owned_process.interrupted)
  def command(label,cmd,environment=None):
   for p,h in bindings.items():assert sha(Path(p))==h,p
   log=out/(label+'.log');resources=out/(label+'.resources');wrapped=['/usr/bin/time','-v','-o',str(resources),*cmd];en=environment or env;save(out/(label+'.invocation.json'),dict(command=cmd,execution_command=wrapped,environment={k:en[k]for k in ['LEAN_PATH','LEAN_SYSROOT']},bindings=bindings));start=time.monotonic();report['current']=label;save(out/'report.json',report)
   with log.open('w')as f:
    p=tracker.Popen(wrapped,cwd=out,env=en,stdout=f,stderr=tracker.STDOUT,start_new_session=True);rc=p.wait(timeout=1800)
   tracker.cleanup();row=dict(label=label,exit_code=rc,seconds=time.monotonic()-start,log_sha256=sha(log),resources_sha256=sha(resources));report['steps'].append(row);save(out/'report.json',report);print(label,rc,round(row['seconds'],2),flush=True);assert rc==0,label;return log.read_text()
  def name_expr(n):
   ans='Name.anonymous'
   for p in n.split('.'):ans='(Name.str '+ans+' '+json.dumps(p,ensure_ascii=False)+')'
   return ans
  def export(label,ns,ms,library,values):
   dest=out/(label+'.lean');payload=out/(label+'.json');s=template.replace('@@MODULE_IMPORTS@@','\n'.join('import '+m for m in ms)).replace('@@NAMES@@','['+', '.join(name_expr(n)for n in ns)+']').replace('@@INCLUDE_DEFINITIONS@@',str(values).lower()).replace('@@OUTPUT_PATH@@',json.dumps(str(payload)));assert '@@'not in s;dest.write_text(s);bindings[str(dest)]=sha(dest);en=env.copy();en['LEAN_PATH']=':'.join([str(library),*P['package_paths']]);command(label,[P['lean'],'-j1','-DwarningAsError=true','-DautoImplicit=false','-o',str(out/(label+'.olean')),str(dest)],en);return json.loads(payload.read_text())
  try:
   a=export('before-types',names,beforemods,ROOT/'build/lib',False);b=export('after-types',names,aftermods,run/'lib',False);assert a==b,'retained types differ';save(out/'types-comparison.json',dict(status='exact',count=696))
   values=[r['name']for r in a['declarations']if r['kind']=='definition'];assert len(values)==183,len(values);a=export('before-values',values,beforemods,ROOT/'build/lib',True);b=export('after-values',values,aftermods,run/'lib',True);assert a==b,'raw data expressions differ';save(out/'values-comparison.json',dict(status='raw_exact',count=183))
   source=(ROOT/'check_classical.py').read_text();import ast;tree=ast.parse(source);probe=next(ast.literal_eval(n.value)for n in tree.body if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='PROBE'for t in n.targets));p=out/'WuLiteralAcceptance.lean';p.write_text(probe);bindings[str(p)]=sha(p);text=command('literal-axioms',[P['lean'],'-j1','-DwarningAsError=true','-DautoImplicit=false','-o',str(out/'WuLiteralAcceptance.olean'),str(p)]);checker=load('release',ROOT.parents[1]/'scripts/check.py');checker.check_axiom_output(text,{'WuPaper.ClassicalSlots.one8938','WuPaper.ClassicalSlots.one894','WuPaper.ClassicalSlots.classical_lower','WuLiteralAcceptance','WuLegacyLiteralAcceptance'})
   targets=[n for n in P['affected']if n in P['overlay']]+['WR2ClassicalCertificate'];assert len(targets)==19
   for n in targets:
    text=command('kernel-'+n,[str(Path(P['sysroot'])/'bin/leanchecker'),'--verbose',n]);assert text.strip()=='replaying '+n,n
   command('producer-check',[sys.executable,'/tmp/wu-hf4-portable-producer-v3/produce.py','--route','constructive','--output-dir',str(run/'sources'),'--check'])
   final=audit();assert final==initial;save(out/'context-after.json',final);report.update(status='FULL_4151_CONTEXTS_696_TYPES_183_RAW_VALUES_19_KERNELS_LITERAL_AXIOMS_PRODUCER_PASS_NOT_ADOPTED',current=None,values=183,kernels=19,bindings=bindings);save(out/'report.json',report);print('VALIDATION_PASS '+str(out),flush=True)
  except BaseException as e:
   report.update(status='VALIDATION_FAILED_NOT_ADOPTED',error_type=type(e).__name__,error=str(e));save(out/'report.json',report);raise
  finally:
   tracker.cleanup()
   for s,h in old.items():signal.signal(s,h)
if __name__=='__main__':main()
