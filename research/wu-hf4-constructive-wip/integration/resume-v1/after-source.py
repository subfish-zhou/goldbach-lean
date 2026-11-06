"""Observe the exact resumed worker; replace this observer with validation only on success."""
from pathlib import Path
import hashlib,json,os,sys,time
B=Path(__file__).resolve().parent;pin=json.loads((B/'after-source-pins.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();R=Path(pin['run']);report=B/'after-source-status.json'
def write(d):report.write_text(json.dumps(d,indent=2)+'\n')
def alive():
 p=Path('/proc')/str(pin['worker_pid'])/'stat'
 try:
  tail=p.read_text().rsplit(')',1)[1].split();return tail[19]==pin['worker_start_ticks']and tail[0]!='Z'
 except FileNotFoundError:return False
assert sha(B/'validate.py')==pin['validator_sha256'];assert sha(B/'run.py')==pin['runner_sha256'];assert sha(B/'plan.json')==pin['plan_sha256'];my=Path('/proc')/str(os.getpid())/'stat';my_start=my.read_text().rsplit(')',1)[1].split()[19]
while alive():
 s=json.loads((R/'STATUS.json').read_text());write(dict(status='WAITING_FOR_EXACT_LIVE_SOURCE_WORKER',controller_pid=os.getpid(),controller_start_ticks=my_start,source_status=s,observed_unix=time.time(),**pin));time.sleep(10)
s=json.loads((R/'STATUS.json').read_text());rows=json.loads((R/'results.json').read_text());assert s['status']=='FULL_SOURCE_4151_COMPILED_NOT_KERNEL_INTERFACE_OR_ADOPTION_ACCEPTANCE',s;assert len(rows)==389 and all(type(r['exit_code'])is int and r['exit_code']==0 for r in rows);assert sum('resumed_proof_origin'in r for r in rows)==53;assert sha(B/'validate.py')==pin['validator_sha256'];cmd=[sys.executable,str(B/'validate.py'),'--run',str(R),'--execute'];write(dict(status='EXACT_SOURCE_WORKER_TERMINAL_SUCCESS_EXEC_VALIDATION',command=cmd,controller_pid=os.getpid(),controller_start_ticks=my_start,source_proofs=389,original_prefix=53,new_compilations=336,**pin));print('SOURCE_COMPLETED_EXEC_VALIDATION',flush=True)
# No Python observer parent remains to masquerade as a second proof worker.
os.execv(sys.executable,cmd)
