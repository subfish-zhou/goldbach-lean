#!/usr/bin/env python3
"""Rebuild recovered proof sources using only this tree and pinned Lake packages.

No old proof-object directories are used. History variants are never imported.
Every success binds source, dependency receipts, command, log and output hash.
"""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,sys,time
ROOT=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--root',default='Wu2008Research');ap.add_argument('--all',action='store_true');ap.add_argument('--limit',type=int);ap.add_argument('--timeout',type=int,default=600);args=ap.parse_args()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
manifest={x['module']:x for x in json.loads((ROOT/'source-manifest.json').read_text())}
for n,row in manifest.items():
 f=ROOT/'src'/Path(*n.split('.')).with_suffix('.lean')
 if sha(f)!=row['source_sha256']:raise RuntimeError('source changed: '+n)
order=[];seen=set();busy=set()
def visit(n):
 if n not in manifest:return
 if n in seen:return
 if n in busy:raise RuntimeError('cycle '+n)
 busy.add(n)
 for dep in manifest[n]['imports']:visit(dep)
 busy.remove(n);seen.add(n);order.append(n)
for n in (manifest if args.all else [args.root]):visit(n)
if args.root not in manifest:raise RuntimeError('unknown root')
B=ROOT/'build';B.mkdir(exist_ok=True);(B/'lib').mkdir(exist_ok=True)
# `lake env` resolves only pinned package configuration; discard any inherited LEAN_PATH.
env=os.environ.copy();env.pop('LEAN_PATH',None)
p=subprocess.run(['lake','env','printenv','LEAN_PATH'],cwd=ROOT,env=env,text=True,capture_output=True)
if p.returncode:raise RuntimeError(p.stdout+p.stderr)
package_paths=[]
for entry in p.stdout.strip().split(':'):
 q=Path(entry)
 if not q.is_absolute():q=ROOT/q
 if '/packages/' in str(q.resolve()):package_paths.append(str(q.resolve()))
if not package_paths:raise RuntimeError('no package library roots')
prefix=subprocess.check_output(['lake','env','lean','--print-prefix'],cwd=ROOT,env=env,text=True).strip()
lean=Path(prefix)/'bin/lean';env['LEAN_PATH']=str(B/'lib')+':'+':'.join(package_paths);env['TMPDIR']=str(B/'tmp');(B/'tmp').mkdir(exist_ok=True)
save(B/'PLAN.json',{'root':args.root,'all':args.all,'modules':order,'toolchain':(ROOT/'lean-toolchain').read_text().strip(),'package_paths':package_paths,'old_proof_objects_used':False})
receipts={};count=0
for n in order:
 row=manifest[n];rel=Path(*n.split('.'));source=(ROOT/'src'/rel).with_suffix('.lean');obj=(B/'lib'/rel).with_suffix('.olean');receipt=(B/'receipts'/rel).with_suffix('.json')
 deps={k:receipts[k]['object_sha256'] for k in row['imports'] if k in receipts}
 if receipt.exists() and obj.exists():
  r=json.loads(receipt.read_text())
  if r.get('exit_code')==0 and r['source_sha256']==sha(source) and r['dependencies']==deps and r['object_sha256']==sha(obj):receipts[n]=r;continue
 if args.limit is not None and count>=args.limit:
  save(B/'STATUS.json',{'status':'batch_limit','verified':len(receipts),'planned':len(order),'next':n});print('BATCH_LIMIT',len(receipts),len(order),flush=True);sys.exit(0)
 obj.parent.mkdir(parents=True,exist_ok=True);log=B/'logs'/f'{n}-{time.time_ns()}.log';log.parent.mkdir(exist_ok=True)
 cmd=[str(lean),'-j2','-DwarningAsError=true','-R',str(ROOT/'src'),'-o',str(obj)]
 if n.startswith(('W','R2')):cmd+=['-DautoImplicit=false']
 cmd.append(str(source));start=time.time()
 with log.open('w') as f:
  try:rc=subprocess.run(cmd,cwd=ROOT/'src',env=env,stdout=f,stderr=subprocess.STDOUT,timeout=args.timeout).returncode
  except subprocess.TimeoutExpired:rc=124
 r={'module':n,'exit_code':rc,'source_sha256':sha(source),'object_sha256':sha(obj) if obj.exists() else None,'dependencies':deps,'log':str(log.relative_to(ROOT)),'log_sha256':sha(log),'command':cmd,'seconds':time.time()-start}
 save(log.with_suffix('.json'),r)
 save(receipt,r);count+=1
 print(n,rc,round(r['seconds'],2),flush=True)
 if rc:
  save(B/'STATUS.json',{'status':'failed','module':n,'exit_code':rc,'verified':len(receipts),'planned':len(order),'log':str(log.relative_to(ROOT))});sys.exit(rc)
 receipts[n]=r;save(B/'STATUS.json',{'status':'running','verified':len(receipts),'planned':len(order),'last':n})
save(B/'STATUS.json',{'status':'passed','root':args.root,'verified':len(receipts),'planned':len(order),'old_proof_objects_used':False});print('BUILD_PASS',len(receipts),flush=True)
