"""Exact previously tested rollback engine with an explicit target allowlist."""
from pathlib import Path
import json,hashlib,os,shutil
ROOT=None
ALLOWED=frozenset()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def save(p,x):
 p.parent.mkdir(parents=True,exist_ok=True);tmp=p.with_name(p.name+'.writing');tmp.write_text(json.dumps(x,indent=2)+'\n');os.replace(tmp,p)
def valid_target(name):
 p=Path(name);require(isinstance(name,str)and not p.is_absolute()and '..'not in p.parts and name in ALLOWED,'target outside explicit transaction allowlist');target=ROOT/p;require(not target.is_dir(),'target is directory');require(not any(q.is_symlink()for q in[target,*target.parents]if q==ROOT or q.is_relative_to(ROOT)),'symlink target/parent');return target
def restore(txn):
 journal=json.loads((txn/'journal.json').read_text());require(journal['phase']in ['mutating','rollback_needed'],'transaction not recoverable')
 require(len({i['target']for i in journal['items']})==len(journal['items']),'duplicate journal targets')
 # Verify every backup before first restore, including retired objects and metadata.
 for item in journal['items']:
  target=valid_target(item['target']);require(not target.is_symlink(),'symlink restore target')
  if item['old_sha256']is not None:require(sha(txn/'backup'/item['target'])==item['old_sha256'],'backup changed '+item['target'])
 for item in reversed(journal['items']):
  target=valid_target(item['target'])
  if item['old_sha256']is None:
   if target.exists():target.unlink()
  else:
   target.parent.mkdir(parents=True,exist_ok=True);tmp=target.with_name(target.name+'.rollback');shutil.copyfile(txn/'backup'/item['target'],tmp);os.replace(tmp,target)
 for item in journal['items']:
  target=valid_target(item['target']);require((sha(target)if target.exists()else None)==item['old_sha256'],'rollback incomplete')
 journal['phase']='rolled_back';save(txn/'journal.json',journal)

def commit_items(txn,journal,verify_install):
 journal['phase']='mutating';save(txn/'journal.json',journal)
 try:
  save(ROOT/'build/STATUS.json',dict(status='adopting_in_progress',transaction=str(txn)))
  for index,item in enumerate(journal['items']):
   target=valid_target(item['target']);target.parent.mkdir(parents=True,exist_ok=True)
   if item['new_sha256']is None:
    if target.exists():target.unlink()
   else:os.replace(txn/'stage'/item['target'],target)
   journal['completed']=index+1
   if index%100==0:save(txn/'journal.json',journal)
  for item in journal['items']:
   target=valid_target(item['target']);require((sha(target)if target.exists()else None)==item['new_sha256'],'installed digest mismatch')
  verify_install()
 except BaseException as exc:
  journal.update(phase='rollback_needed',error_type=type(exc).__name__,error=str(exc));save(txn/'journal.json',journal);restore(txn);raise
 journal['phase']='committed_pending_production_verification';save(txn/'journal.json',journal)
