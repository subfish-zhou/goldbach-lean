"""Serial isolated full-source trial on the installed V7 baseline; never adopts."""
from pathlib import Path
import argparse,hashlib,json,os,sys,importlib.util,shutil,fcntl,signal,time
ROOT=Path('/home/azureuser/goldbach-lean/research/wu2008');B=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,d):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2)+'\n')
def rel(n,suffix):return Path(*n.split('.')).with_suffix(suffix)
def context(s,o,ds):return hashlib.sha256(json.dumps(dict(source_sha256=s,object_sha256=o,dependency_contexts=ds),sort_keys=True,separators=(',',':')).encode()).hexdigest()
def bundle(lib,n):return {s:sha(lib/rel(n,s))for s in ['.olean','.olean.server','.olean.private','.ir','.ir.sig']if(lib/rel(n,s)).exists()}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--execute',action='store_true');args=ap.parse_args();planfile=B/'plan.json';P=json.loads(planfile.read_text());bindings={**P['bindings'],str(planfile):sha(planfile),str(Path(__file__)):sha(Path(__file__))}
 def verify_bindings():
  for p,h in bindings.items():assert sha(Path(p))==h,p
 def verify_production():
  for n,h in P['production_sources'].items():assert sha(ROOT/'src'/rel(n,'.lean'))==h,n
 verify_bindings();assert P['baseline_manifest_sha256']==sha(ROOT/'source-manifest.json');assert json.loads((ROOT.parent/'wu-structural-compression-audit/validation.json').read_text())['status']=='pass';verify_production()
 assert len(P['order'])==4151 and len(P['affected'])==389 and len(P['unchanged'])==3762
 assert P['precision']['canonical_fields_sha256']=='e797b939f8cbb0a48f5c2b0e75853807de778b560a3a5d1fc75d3ef1eda0071f'
 if not args.execute:print('PLAN_INPUTS_VERIFIED_NOT_EXECUTED');return
 helper=Path('/tmp/wu-hf4-safe-probes/dag-v2');sys.path.insert(0,str(helper));import owned_process
 spec=importlib.util.spec_from_file_location('safe',helper/'run.py');safe=importlib.util.module_from_spec(spec);spec.loader.exec_module(safe);safe.no_live_lean()
 with Path('/tmp/wu-lean-exclusive.lock').open('a')as lock:
  fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);safe.no_live_lean();verify_bindings();verify_production();assert shutil.disk_usage(B).free>2_000_000_000
  run=B/('run-'+str(time.time_ns()));run.mkdir();save(run/'plan.json',P);sources=run/'sources';lib=run/'lib';logs=run/'logs';sources.mkdir();lib.mkdir();logs.mkdir();save(run/'ownership.json',dict(runner_pid=os.getpid(),run=str(run)))
  for n,h in P['candidate_sources'].items():
   src=B/'overlay'/rel(n,'.lean')if n in P['overlay']else ROOT/'src'/rel(n,'.lean');assert sha(src)==h,n;dest=sources/rel(n,'.lean');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dest);assert sha(dest)==h,n
  env=os.environ.copy()
  for k in ['LEAN_PATH','LEAN_SYSROOT','LEAN_SRC_PATH']:env.pop(k,None)
  env['LEAN_SYSROOT']=P['sysroot'];env['LEAN_PATH']=':'.join([str(lib),*P['package_paths']]);env['TMPDIR']=str(run/'tmp');(run/'tmp').mkdir()
  for p in [Path(P['lean']),Path(P['sysroot'])/'lib/lean/Init.olean']:bindings[str(p)]=sha(p)
  verified={};contexts={};bundles={};base={};affected=set(P['affected']);frozen=Path(P['immutable_baseline_library']);frozen_bindings={}
  for n in P['order']:
   if n in affected:continue
   rp=ROOT/'build/receipts'/rel(n,'.json');r=json.loads(rp.read_text());deps={d:verified[d]for d in P['graph'][n]};dcs={d:contexts[d]for d in deps};obj=ROOT/'build/lib'/rel(n,'.olean')
   assert r['exit_code']==0 and not r.get('direct_check_only')and r['source_sha256']==P['candidate_sources'][n]and r['object_sha256']==sha(obj)
   assert r['dependencies']==deps and r['dependency_contexts']==dcs and r['context_sha256']==context(r['source_sha256'],r['object_sha256'],dcs),n
   assert r['command'][0]==P['lean'] and sha(ROOT/r['log'])==r['log_sha256'],n
   pb=bundle(ROOT/'build/lib',n);fb=bundle(frozen,n);assert pb==fb,n
   for suffix,h in fb.items():
    src=frozen/rel(n,suffix);dest=lib/rel(n,suffix);dest.parent.mkdir(parents=True,exist_ok=True);assert not dest.exists();os.link(src,dest);assert sha(dest)==h;frozen_bindings[str(src)]=h
   verified[n]=r['object_sha256'];contexts[n]=r['context_sha256'];bundles[n]=fb;base[n]=dict(receipt_path=str(rp),receipt_sha256=sha(rp),source_sha256=r['source_sha256'],object_sha256=r['object_sha256'],context_sha256=r['context_sha256'],dependencies=deps,dependency_contexts=dcs,artifact_bundle_sha256=fb)
  save(run/'verified-base-receipts.json',base);save(run/'immutable-object-bindings.json',frozen_bindings);results=[];tracker=owned_process.TrackedSubprocess(run=run);previous={s:signal.getsignal(s)for s in [signal.SIGINT,signal.SIGTERM]}
  for s in previous:signal.signal(s,owned_process.interrupted)
  try:
   for n in P['affected']:
    verify_bindings();source=sources/rel(n,'.lean');assert sha(source)==P['candidate_sources'][n];deps={d:verified[d]for d in P['graph'][n]};dcs={d:contexts[d]for d in deps}
    for d in deps:assert bundle(lib,d)==bundles[d],d
    obj=lib/rel(n,'.olean');assert not obj.exists(),n;obj.parent.mkdir(parents=True,exist_ok=True);log=logs/(n+'.log');resource=logs/(n+'.resources');cmd=[P['lean'],'-j1','-DwarningAsError=true','-R',str(sources),'-o',str(obj)]
    if P['policies'][n]:cmd.append(P['policies'][n])
    cmd.append(str(source));execution=['/usr/bin/time','-v','-o',str(resource),*cmd];save(run/'STATUS.json',dict(status='running',current=n,completed=len(results),planned=len(P['affected']),verified_unchanged=len(base),started_unix=time.time()))
    save(log.with_suffix('.invocation.json'),dict(command=cmd,execution_command=execution,environment={k:env[k]for k in ['LEAN_PATH','LEAN_SYSROOT','TMPDIR']},source_sha256=P['candidate_sources'][n],dependencies=deps,dependency_contexts=dcs));start=time.monotonic()
    with log.open('w')as out:
     p=tracker.Popen(execution,cwd=sources,env=env,stdout=out,stderr=tracker.STDOUT,start_new_session=True);save(run/'own-process.json',dict(pid=p.pid,start_ticks=tracker.start_ticks,run=str(run),module=n));rc=p.wait(timeout=1800)
    tracker.cleanup();verify_bindings();assert sha(source)==P['candidate_sources'][n]
    for d in deps:assert bundle(lib,d)==bundles[d],d
    ob=sha(obj)if obj.exists()else None;row=dict(module=n,exit_code=rc,seconds=time.monotonic()-start,source_sha256=sha(source),object_sha256=ob,dependencies=deps,dependency_contexts=dcs,context_sha256=context(sha(source),ob,dcs)if ob else None,command=cmd,execution_command=execution,log=str(log),log_sha256=sha(log),resource_log=str(resource),resource_sha256=sha(resource),artifact_bundle_sha256=bundle(lib,n));results.append(row);save(run/'receipts'/rel(n,'.json'),row);save(run/'results.json',results);print(n,rc,round(row['seconds'],2),flush=True)
    if rc:save(run/'STATUS.json',dict(status='failed_not_adopted',failed=n,compiled=len(results),plan_sha256=sha(planfile)));raise SystemExit(rc)
    verified[n]=ob;contexts[n]=row['context_sha256'];bundles[n]=row['artifact_bundle_sha256']
   verify_bindings();verify_production()
   for n,h in P['candidate_sources'].items():assert sha(sources/rel(n,'.lean'))==h,n
   for n in P['order']:assert bundle(lib,n)==bundles[n],n
   for p,h in frozen_bindings.items():assert sha(Path(p))==h,p
   save(run/'STATUS.json',dict(status='FULL_SOURCE_4151_COMPILED_NOT_KERNEL_INTERFACE_OR_ADOPTION_ACCEPTANCE',fresh_compilations=len(results),verified_unchanged=len(base),plan_sha256=sha(planfile)));print('FULL_SOURCE_PASS '+str(run),flush=True)
  finally:
   tracker.cleanup()
   for s,h in previous.items():signal.signal(s,h)
if __name__=='__main__':main()
