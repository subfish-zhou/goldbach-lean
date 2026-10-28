#!/usr/bin/env python3
"""Independently freeze an accepted archive and audit exact light-layer moves.

One-time capture: --capture /path/to/accepted/baseline.tar
Repeat audit: no arguments (uses compact frozen proof records, not /tmp).
No Lean invocation or source mutation is performed.
"""
from pathlib import Path
import argparse,ast,hashlib,json,re,tarfile
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]; SRC=ROOT/'research/wu2008/src'; DIAG=ROOT/'research/wu2008/diagnostics'
FAMILIES={'BPay':42,'CPay':10,'DPay':10,'outerPay':42}
SIMPLE=['WR2ClassicalCumulativeTable','WR2ClassicalCumulativePayment','WR2ClassicalCumulativeDivision','WR2IntegerLogHorner','WR2ClassicalCIntegerData','WR2ClassicalCPayments','WR2ClassicalSixthIntegerData','WR2ClassicalEighthRawIntegerData','WR2ClassicalFourthAllOuterPoint']
SPECIAL=['WR2ClassicalFourthConditions','WR2ExactRationalLog']
GENERATORS={'classical_c_eighth_certificates.py':['c_payments','eighth_payments'],'classical_sixth_certificates.py':['point_data','integer_values'],'classical_fourth_certificates.py':['table_data','natural_sources']}
OLD_BLOCKS=[f'WR2ClassicalFourthBlock{f}{i:03d}.lean' for f,n in FAMILIES.items() for i in range(n)]
BATCHES=[f'WR2ClassicalFourth{f}Batch{i:03d}.lean' for f,n in FAMILIES.items() for i in range((n+7)//8)]
ALL=[f'WR2ClassicalFourthAll{f}.lean' for f in FAMILIES]
CHANGED={n+'.lean' for n in SIMPLE+SPECIAL}|set(ALL)
NEW=set(BATCHES)|{'WR2ExactRationalLogData.lean','WR2ClassicalFourthIntegerConditions.lean'}
def sha(t):return hashlib.sha256(t.encode()).hexdigest()
def noimports(t):return re.sub(r'^import [^\n]+\n','',t,flags=re.M)
def function_asts(t,names):
 tree=ast.parse(t);return {n:sha(ast.dump(next(x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name==n))) for n in names}
def capture(archive):
 with tarfile.open(archive) as tar:
  sources={m.name.removeprefix('src/'):tar.extractfile(m).read().decode() for m in tar.getmembers() if m.isfile() and m.name.startswith('src/') and m.name.endswith('.lean')}
  generators={n:tar.extractfile('diagnostics/'+n).read().decode() for n in GENERATORS}
 data={'archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'source_hashes':{n:sha(t) for n,t in sources.items()},'records':{n:sources[n] for n in sorted(CHANGED|set(OLD_BLOCKS))},'producer_AST_sha256':{n:function_asts(t,GENERATORS[n]) for n,t in generators.items()}}
 (HERE/'baseline-preservation.json').write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n')
def audit(current=None):
 baseline=json.loads((HERE/'baseline-preservation.json').read_text());old=baseline['records']
 new=current if current is not None else {str(p.relative_to(SRC)):p.read_text() for p in SRC.rglob('*.lean')}
 assert set(new)==(set(baseline['source_hashes'])-set(OLD_BLOCKS))|NEW,'source inventory'
 for n,h in baseline['source_hashes'].items():
  if n not in CHANGED and n not in OLD_BLOCKS:assert sha(new[n])==h,('unapproved source change',n)
 for n in SIMPLE:
  name=n+'.lean';assert noimports(new[name])==noimports(old[name]),('body changed',name)
 payments=[]
 for f,count in FAMILIES.items():
  allname=f'WR2ClassicalFourthAll{f}.lean'; body=noimports(old[allname]);assert noimports(new[allname])==body,('aggregate body',f)
  assert body.count(f'#print axioms WuPaper.ClassicalFourthConditions.all_{f}')==1
  expectedimports='import Mathlib.Tactic.FinCases\n'+''.join(f'import WR2ClassicalFourth{f}Batch{j:03d}\n' for j in range((count+7)//8))
  assert new[allname]==expectedimports+body,('aggregate import coverage',f)
  for first in range(0,count,8):
   chunks=[];imports=[]
   for i in range(first,min(first+8,count)):
    text=old[f'WR2ClassicalFourthBlock{f}{i:03d}.lean'];start=text.index('set_option maxRecDepth');end=text.index('end WuPaper.ClassicalFourthConditions')
    chunks.append(text[start:end]);name=f'{f}_block_{i:03d}'
    assert len(re.findall(r'\b'+name+r'\b',body))==1,('aggregate theorem reference',name)
    for line in text.splitlines(keepends=True):
     if line.startswith('import '):
      line=line.replace('WR2ClassicalFourthConditions','WR2ClassicalFourthIntegerConditions')
      if line not in imports:imports.append(line)
    payments.append(name)
   expected=''.join(imports)+'namespace WuPaper.ClassicalFourthConditions\n\n'+''.join(chunks)+'end WuPaper.ClassicalFourthConditions\n'
   assert new[f'WR2ClassicalFourth{f}Batch{first//8:03d}.lean']==expected,('proof/statement/budget/QName',f,first)
 # Entire contiguous Nat declaration region is moved, not regenerated.
 text=old['WR2ClassicalFourthConditions.lean'];a=text.index('def BPay');b=text.index('theorem B_payment');nat=text[a:b]
 assert noimports(new['WR2ClassicalFourthConditions.lean'])==noimports(text[:a]+text[b:]),'real bridge changed'
 assert noimports(new['WR2ClassicalFourthIntegerConditions.lean'])=='\nnamespace WuPaper.ClassicalFourthConditions\nopen ClassicalFourthData\n\n'+nat+'end WuPaper.ClassicalFourthConditions\n','Nat declaration move'
 # The rational definitions and casts retain their namespace and exact bodies.
 text=old['WR2ExactRationalLog.lean'];a=text.index('def logLo');b=text.index('@[simp] theorem cast_logLo');c=text.index('/-- The same midpoint');d=text.index('end WuPaper.ExactRational',c)
 defs=text[a:b]+text[c:d]
 assert noimports(new['WR2ExactRationalLog.lean'])==noimports(text[:a]+text[b:c]+text[d:]),'rational Real bridge changed'
 target=new['WR2ExactRationalLogData.lean'];assert target[target.index('def logLo'):target.index('end WuPaper.ExactRational')]==defs,'rational definitions changed'
 assert 'namespace WuPaper.ExactRational\nopen Finset\n' in target,'rational QName'
 for n,names in GENERATORS.items():assert function_asts((DIAG/n).read_text(),names)==baseline['producer_AST_sha256'][n],('numeric producer changed',n)
 return {'status':'PASS','baseline_archive_sha256':baseline['archive_sha256'],'baseline_modules':len(baseline['source_hashes']),'current_modules':len(new),'exact_independent_proofs_statements_and_scoped_budgets':len(payments),'aggregate_axiom_prints':4,'direct_aggregate_references':len(payments),'moved_Nat_declarations':6,'moved_rational_definitions':3,'imports_only_body_checks':len(SIMPLE),'unchanged_numeric_producer_functions':sum(map(len,GENERATORS.values())),'all_other_source_hashes_preserved':True,'current_changed_and_new_hashes':{n:sha(new[n]) for n in sorted(CHANGED|NEW)},'Lean_run':False}
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--capture',type=Path);args=p.parse_args()
 if args.capture:capture(args.capture)
 result=audit();(HERE/'preservation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='current_changed_and_new_hashes'},indent=2))
if __name__=='__main__':main()
