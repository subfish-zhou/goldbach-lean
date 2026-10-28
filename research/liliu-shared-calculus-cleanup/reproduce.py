#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,subprocess,sys,datetime
import argparse
parser=argparse.ArgumentParser(description='Rebuild and independently check the main proof snapshot, optionally revalidate a stable Wu tree.')
parser.add_argument('--output',type=Path,required=True)
parser.add_argument('--include-wu',action='store_true',help='Also check the separate Wu tree; requires a stable, rebuilt Wu source snapshot.')
args=parser.parse_args()
ROOT=Path(__file__).resolve().parents[2];OUT=args.output.resolve();OUT.mkdir(parents=True,exist_ok=False)
files=list(ROOT.glob('*.lean'))
for name in ['Goldbach','MathlibNt','AnalyticNumberTheory','PrimeNumberTheoremAnd']:files.extend((ROOT/name).rglob('*.lean'))
files += [ROOT/p for p in ['lean-toolchain','lakefile.toml','lake-manifest.json','scripts/check.py','scripts/source_size.py','scripts/test_build_docs.py']]
inputs={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)}
(OUT/'inputs.json').write_text(json.dumps(inputs,indent=2)+'\n')
contract='research/liliu-shared-lemma-cleanup/StrengthenedStatements.lean'
auxiliary_inputs={contract:hashlib.sha256((ROOT/contract).read_bytes()).hexdigest()}
env=os.environ.copy();env.pop('LEAN_PATH',None);env.pop('LEAN_SRC_PATH',None);env['LEAN_NUM_THREADS']='4'
result={'phase':'Li-Liu shared calculus and author-weight proofs','status':'running','started_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_modules':sum(p.suffix=='.lean' for p in files),'checks':{},'auxiliary_input_sha256':auxiliary_inputs}
def save():(OUT/'result.json').write_text(json.dumps(result,indent=2)+'\n')
def verify_inputs():
 for relative,digest in (inputs|auxiliary_inputs).items():assert hashlib.sha256((ROOT/relative).read_bytes()).hexdigest()==digest,relative
 current={str(p.relative_to(ROOT)) for area in ['Goldbach','MathlibNt','AnalyticNumberTheory','PrimeNumberTheoremAnd'] for p in (ROOT/area).rglob('*.lean')}|{str(p.relative_to(ROOT)) for p in ROOT.glob('*.lean')}
 assert current=={p for p in inputs if p.endswith('.lean')},'source inventory changed'
def run(name,cmd,log,cwd=ROOT):
 print('START',name,flush=True);save()
 with (OUT/log).open('w') as output:code=subprocess.run(cmd,cwd=cwd,env=env,stdout=output,stderr=subprocess.STDOUT).returncode
 result['checks'][name]={'exit_code':code,'log':log};verify_inputs();save()
 if code:
  result['status']='failed';save();print('FAIL',name,code,flush=True);sys.exit(code)
 print('PASS',name,flush=True)
save()
run('full_source_build',['lake','--rehash','--wfail','build'],'full-build.log')
run('public_literal_and_axiom_checks',['python3','scripts/check.py'],'public-checks.log')
run('strengthened_internal_statement_contracts',['lake','env','lean','-DwarningAsError=true',contract],'strengthened-statements.log')
for name in ['Goldbach.Theorem','Goldbach.Checks','Goldbach.OnePlusOneNine','Goldbach.OnePlusOneNineChecks','Goldbach.All']:
 run('kernel_replay_'+name,['lake','env','leanchecker','--verbose',name],'kernel-'+name+'.log')
run('script_tests',['python3','-m','unittest','discover','-s','scripts','-p','test_*.py'],'script-tests.log')
if args.include_wu:
 run('current_wu_source_receipts',['python3','verify_sources.py'],'wu-source-hashes.log',ROOT/'research/wu2008')
 run('wu_literal_and_receipt_validation',['python3','check_classical.py'],'wu-literal-receipts.log',ROOT/'research/wu2008')
verify_inputs();result['status']='pass';result['finished_at_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();result['input_manifest_sha256']=hashlib.sha256((OUT/'inputs.json').read_bytes()).hexdigest();save();print('ALL_VALIDATION_PASS',flush=True)
