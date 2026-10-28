#!/usr/bin/env python3
"""Real-byte negative controls; only temporary copied candidate files mutate."""
import argparse, copy, importlib.util, json, tempfile
from pathlib import Path
HERE=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('audit',HERE/'audit.py');a=importlib.util.module_from_spec(s);s.loader.exec_module(a)
def main():
 p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,required=True);p.add_argument('--candidate-root',type=Path,required=True);p.add_argument('--output',type=Path);args=p.parse_args()
 original=json.loads((HERE/'manifest.json').read_text()); results=[]
 with tempfile.TemporaryDirectory() as td:
  root=Path(td)
  for row in original['files']:
   dst=root/row['file'];dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes((args.candidate_root/row['file']).read_bytes())
  first=root/original['files'][0]['file']; good=first.read_bytes()
  for case in ['baseline_identity','baseline_blob_sha','interval_offset','fragment_sha','survivor_changed_rehashed','candidate_bytes']:
   m=copy.deepcopy(original);r=m['files'][0]
   first.write_bytes(good)
   if case=='baseline_identity': m['baseline_commit']='0'*40
   elif case=='baseline_blob_sha':r['before_sha256']='0'*64
   elif case=='interval_offset':r['deletions'][0]['start']+=1
   elif case=='fragment_sha':r['deletions'][0]['fragment_sha256']='0'*64
   else:
    first.write_bytes(good+b'\n-- negative survivor mutation\n')
    if case=='survivor_changed_rehashed':r['after_sha256']=a.sha(first.read_bytes())
   try:a.audit(args.repo,root,m)
   except ValueError as e:results.append(dict(case=case,status='rejected',reason=str(e)))
   else:raise RuntimeError('negative control accepted: '+case)
 report=dict(status='PASS',lean_run=False,negative_controls=results)
 text=json.dumps(report,indent=2)+'\n'
 if args.output:args.output.write_text(text)
 print(text,end='')
if __name__=='__main__':main()
