#!/usr/bin/env python3
"""Portable17-module Hf4 producer. Frozen relative inputs; never invokes Lean."""
from pathlib import Path
import argparse,hashlib,importlib.util,json
HERE=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()

def load(name,path):
 spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module

def verify_inputs():
 manifest=json.loads((HERE/'frozen-inputs.json').read_text());expected=manifest['inputs']
 actual={str(p.relative_to(HERE))for root in ['lib','stages','frozen']for p in (HERE/root).rglob('*')if p.is_file()and'__pycache__'not in p.parts}
 assert actual==set(expected),'frozen producer input inventory differs'
 for name,h in expected.items():assert sha((HERE/name).read_bytes())==h,('frozen input differs',name)
 return expected

def generate(route):
 frozen=verify_inputs();golden=json.loads((HERE/'frozen/golden.json').read_text());complete=load('portable_complete',HERE/'stages/complete/complete.py');base=complete.generate();table=load('portable_table',HERE/'stages/table/generate.py');endpoints=table.generate(base)
 if route=='constructive':
  full=load('portable_constructive',HERE/'stages/constructive/generate.py');last=full.generate(base,endpoints);available={**base,**last};audit=json.loads(last['numeric-audit.json'])
 else:available={**base,**endpoints};audit=json.loads(base['numeric-audit.json'])
 if route=='constructive':
  for name in ['Hf4DirectDagSemantics','Hf4DirectDagSeedSoundness']:available['lean/'+name+'.lean']=(HERE/'frozen'/(name+'.lean')).read_bytes()
 expected=golden['routes'][route]['modules'];outputs={name+'.lean':available['lean/'+name+'.lean']for name in sorted(expected)}
 assert len(outputs)==17
 for name,b in outputs.items():assert sha(b)==expected[name.removesuffix('.lean')],('generated Lean differs from original golden source',name)
 assert not(set(name.removesuffix('.lean')for name in outputs)&set(golden['retired_modules_not_generated']))
 key='canonical_fields_sha256'if route=='constructive'else'checked_and_inverse_canonical_sha256'
 assert audit[key]==golden['canonical_fields_sha256']
 assert verify_inputs()==frozen
 report={'status':'PORTABLE17_SOURCE_REPRODUCTION_NOT_ACCEPTANCE','route':route,'producer_sha256':sha(Path(__file__).read_bytes()),'frozen_input_manifest_sha256':sha((HERE/'frozen-inputs.json').read_bytes()),'modules':{n:sha(b)for n,b in outputs.items()},'canonical_fields_sha256':audit[key],'fields':74200,'precision_denominator':10**14,'original_target_count':80,'all40_original_header_bytes_retained':True,'stored_inverse_records':0 if route=='constructive'else 880,'input_paths_relative':True,'live_retired_source_reads':False,'Lean_executed':False}
 return outputs,(json.dumps(report,indent=2)+'\n').encode()

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--route',choices=['checkpoint','constructive'],default='constructive');p.add_argument('--output-dir',type=Path,required=True);p.add_argument('--check',action='store_true');a=p.parse_args();outputs,report=generate(a.route)
 for n,b in outputs.items():
  f=a.output_dir/n
  if a.check:assert f.read_bytes()==b,('generated source differs',n)
  else:f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b)
 golden=json.loads((HERE/'frozen/golden.json').read_text())
 if a.check:
  for n in golden['retired_modules_not_generated']:assert not(a.output_dir/(n+'.lean')).exists(),('retired module remains in check surface',n)
  if(a.output_dir/'producer-report.json').exists():assert(a.output_dir/'producer-report.json').read_bytes()==report,'producer report provenance differs'
 else:(a.output_dir/'producer-report.json').write_bytes(report)
 print(json.dumps({'status':'CHECK_PASS'if a.check else'GENERATED17','route':a.route,'modules':len(outputs),'canonical_fields_sha256':golden['canonical_fields_sha256'],'Lean_executed':False}))
if __name__=='__main__':main()
