#!/usr/bin/env python3
"""Rebuild recovered proof sources using only this tree and pinned Lake packages.

No old proof-object directories are used. History variants are never imported.
Every success binds source, dependency receipts, command, log and output hash.
"""
from pathlib import Path
import argparse,hashlib,heapq,json,os,subprocess,sys,time
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
ROOT=Path(__file__).resolve().parent
ap=argparse.ArgumentParser()
ap.add_argument('--root',default='Wu2008Research')
ap.add_argument('--all',action='store_true')
ap.add_argument('--first',action='append',default=[],metavar='MODULE',
                help='Prioritize a module within the selected closure; repeatable. The full scope is retained.')
ap.add_argument('--limit',type=int)
ap.add_argument('--timeout',type=int,default=600)
ap.add_argument('--jobs',type=int,default=1,help='Maximum independent module compilations in flight.')
ap.add_argument('--lean-threads',type=int,default=2,help='Lean worker threads per module.')
args=ap.parse_args()
if args.jobs < 1 or args.lean_threads < 1:ap.error('jobs and lean-threads must be positive')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
manifest_path=ROOT/'source-manifest.json'
manifest_bytes=manifest_path.read_bytes()
manifest_sha256=hashlib.sha256(manifest_bytes).hexdigest()
manifest={x['module']:x for x in json.loads(manifest_bytes)}
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
roots=list(manifest) if args.all else [args.root]
for n in roots:visit(n)
if args.root not in manifest:raise RuntimeError('unknown root')
if args.first:
 selected=set(order)
 for n in args.first:
  if n not in selected:raise RuntimeError('priority module outside selected closure: '+n)
 # Reorder only: retain every original target and visit prerequisites first.
 order=[];seen=set();busy=set()
 for n in [*args.first,*roots]:visit(n)
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
save(B/'PLAN.json',{'root':args.root,'all':args.all,'first':args.first,'jobs':args.jobs,'lean_threads':args.lean_threads,'modules':order,'toolchain':(ROOT/'lean-toolchain').read_text().strip(),'package_paths':package_paths,'old_proof_objects_used':False})
receipts={};count=0

def input_change(n=None, deps=None):
 # A changed manifest may describe a different import graph. Never bind a
 # newly compiled object to the graph captured by an earlier invocation.
 if sha(manifest_path)!=manifest_sha256:return 'source manifest changed during build'
 if n is not None:
  source=ROOT/'src'/Path(*n.split('.')).with_suffix('.lean')
  if sha(source)!=manifest[n]['source_sha256']:return 'source changed during build: '+n
 for dep,expected in (deps or {}).items():
  obj=(B/'lib'/Path(*dep.split('.'))).with_suffix('.olean')
  if not obj.exists() or sha(obj)!=expected:return 'dependency object changed during build: '+dep
 return None

def stop_changed(reason):
 save(B/'STATUS.json',{'status':'inputs_changed','reason':reason,
  'verified':len(receipts),'planned':len(order)})
 print('INPUTS_CHANGED',reason,flush=True)
 sys.exit(125)

def module_paths(n):
 rel=Path(*n.split('.'))
 return ((ROOT/'src'/rel).with_suffix('.lean'),
         (B/'lib'/rel).with_suffix('.olean'),
         (B/'receipts'/rel).with_suffix('.json'))

def compile_module(n,deps):
 # Workers write only their own objects, logs and receipts. The coordinator
 # alone releases dependents and updates the overall build status.
 row=manifest[n];source,obj,receipt=module_paths(n)
 obj.parent.mkdir(parents=True,exist_ok=True)
 log=B/'logs'/f'{n}-{time.time_ns()}.log';log.parent.mkdir(exist_ok=True)
 cmd=[str(lean),f'-j{args.lean_threads}','-DwarningAsError=true','-R',str(ROOT/'src'),'-o',str(obj)]
 if n.startswith(('W','R2')):cmd+=['-DautoImplicit=false']
 cmd.append(str(source));start=time.time()
 with log.open('w') as f:
  try:rc=subprocess.run(cmd,cwd=ROOT/'src',env=env,stdout=f,stderr=subprocess.STDOUT,timeout=args.timeout).returncode
  except subprocess.TimeoutExpired:rc=124
 changed=input_change(n,deps)
 if changed:rc=125
 r={'module':n,'exit_code':rc,'source_sha256':row['source_sha256'],'object_sha256':sha(obj) if obj.exists() else None,'dependencies':deps,'log':str(log.relative_to(ROOT)),'log_sha256':sha(log),'command':cmd,'seconds':time.time()-start}
 if changed:r['input_change']=changed
 save(log.with_suffix('.json'),r);save(receipt,r)
 return r

# Dependencies, not mere topological positions, determine readiness. The heap
# retains --first order among ready modules; jobs=1 keeps the serial order.
positions={n:i for i,n in enumerate(order)}
remaining={n:set(d for d in manifest[n]['imports'] if d in positions) for n in order}
consumers={n:[] for n in order}
for n,deps in remaining.items():
 for dep in deps:consumers[dep].append(n)
ready=[(positions[n],n) for n in order if not remaining[n]]
heapq.heapify(ready)

def accept(n,r):
 receipts[n]=r
 for child in consumers[n]:
  remaining[child].remove(n)
  if not remaining[child]:heapq.heappush(ready,(positions[child],child))

running={};limited=[];failure=None
with ThreadPoolExecutor(max_workers=args.jobs) as pool:
 while ready or running:
  while ready and len(running)<args.jobs and failure is None:
   _,n=heapq.heappop(ready)
   source,obj,receipt=module_paths(n)
   deps={k:receipts[k]['object_sha256'] for k in manifest[n]['imports'] if k in positions}
   changed=input_change(n,deps)
   if changed:
    failure={'module':n,'exit_code':125,'input_change':changed};break
   if receipt.exists() and obj.exists():
    r=json.loads(receipt.read_text())
    if r.get('exit_code')==0 and r['source_sha256']==sha(source) and r['dependencies']==deps and r['object_sha256']==sha(obj):
     accept(n,r);continue
   if args.limit is not None and count>=args.limit:
    limited.append(n);continue
   running[pool.submit(compile_module,n,deps)]=n;count+=1
  if not running:break
  done,_=wait(running,return_when=FIRST_COMPLETED)
  for future in sorted(done,key=lambda f:positions[running[f]]):
   n=running.pop(future)
   try:r=future.result()
   except Exception as e:
    r={'module':n,'exit_code':1,'error':str(e),'seconds':0}
   print(n,r['exit_code'],round(r['seconds'],2),flush=True)
   if r['exit_code']:
    if failure is None or r['exit_code']==125:failure=r
   else:accept(n,r)
  if failure is None:
   save(B/'STATUS.json',{'status':'running','verified':len(receipts),'planned':len(order),'in_flight':len(running)})
 # On failure, already running independent jobs finish and keep their receipts;
 # no failed module's dependents are scheduled.
if failure:
 if failure['exit_code']==125:stop_changed(failure['input_change'])
 save(B/'STATUS.json',{'status':'failed','module':failure['module'],'exit_code':failure['exit_code'],
  'verified':len(receipts),'planned':len(order),'log':failure.get('log'),'error':failure.get('error')})
 sys.exit(failure['exit_code'])
if limited:
 save(B/'STATUS.json',{'status':'batch_limit','verified':len(receipts),'planned':len(order),'next':min(limited,key=positions.get)})
 print('BATCH_LIMIT',len(receipts),len(order),flush=True);sys.exit(0)
assert len(receipts)==len(order),'scheduler left unverified modules'
# Recheck all sources: an earlier module may have changed after its turn.
changed=input_change()
if changed:stop_changed(changed)
for n,row in manifest.items():
 source=ROOT/'src'/Path(*n.split('.')).with_suffix('.lean')
 if sha(source)!=row['source_sha256']:stop_changed('source changed during build: '+n)
for n,r in receipts.items():
 obj=(B/'lib'/Path(*n.split('.'))).with_suffix('.olean')
 if not obj.exists() or sha(obj)!=r['object_sha256']:
  stop_changed('output object changed during build: '+n)
save(B/'STATUS.json',{'status':'passed','root':args.root,'verified':len(receipts),'planned':len(order),'old_proof_objects_used':False});print('BUILD_PASS',len(receipts),flush=True)
