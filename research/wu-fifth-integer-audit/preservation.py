#!/usr/bin/env python3
"""Portable source/contract and interpreted-Nat audit; never invokes Lean.

--capture freezes the accepted baseline archive. Default audits actual sources.
--overlay DIR may be repeated for pre-adoption checks (records candidate status).
"""
from pathlib import Path
import argparse,ast,hashlib,json,re,subprocess,tarfile
from lean_nat import definition,evaluator
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];SRC=ROOT/'research/wu2008/src'
BRANCHES=['initial','middle','terminal'];PREFIX='WR2ClassicalFifth'
DELETED={f'{PREFIX}{b.title()}GridBlock{i:03d}.lean' for b in BRANCHES for i in range(16)}
CHANGED={PREFIX+b.title()+kind+'.lean' for b in BRANCHES for kind in ['Root','Payments']}|{PREFIX+'TableCheck.lean'}
NEW={PREFIX+n+'.lean' for n in ['IntegerData','IntegerPolynomial','IntegerDomains','IntegerSoundness','PolynomialData','PaymentData','InitialSums','MiddleSums','TerminalSums']}
RECORDS=CHANGED|{PREFIX+'Certificate.lean','WR2IntegerLogHorner.lean'}
BASELINE_GIT='c4e1b8d00dda9661140f95e0f03f0d5a08d636c2'
sha=lambda t:hashlib.sha256(t.encode()).hexdigest()
def noimports(t):return re.sub(r'^import [^\n]+\n','',t,flags=re.M)
def declaration(t,name,kind='theorem'):
 rows=re.findall(r'^'+kind+' '+name+r'\b.*?(?= :=)',t,re.M|re.S);assert len(rows)==1,('declaration',name);return rows[0]
def capture(path):
 with tarfile.open(path) as tar:
  sources={m.name.removeprefix('src/'):tar.extractfile(m).read().decode() for m in tar.getmembers() if m.isfile() and m.name.startswith('src/') and m.name.endswith('.lean')}
  generator=tar.extractfile('diagnostics/classical_fifth_certificates.py').read().decode()
 for b in BRANCHES:
  name=PREFIX+b.title()+'Payments.lean';fixed=subprocess.check_output(['git','show',BASELINE_GIT+':research/wu2008/src/'+name],cwd=ROOT,text=True)
  assert fixed==sources[name],('archive differs from fixed Git payments',b)
 asts={n:sha(ast.dump(next(v for v in ast.parse(generator).body if isinstance(v,ast.FunctionDef) and v.name==n))) for n in ['point_data','correction_coefficients']}
 data={'archive_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'fixed_payment_git':BASELINE_GIT,'source_hashes':{n:sha(t) for n,t in sources.items()},'records':{n:sources[n] for n in sorted(RECORDS)},'numeric_producer_AST':asts}
 (HERE/'frozen-records.json').write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n')
def original_values(text,branch):
 blocks=re.findall(r'^def '+branch+r'Block(\d+) : ℕ → ℕ\n(.*?)(?=\ndef )',text,re.M|re.S);assert len(blocks)==64
 values=[]
 for expected,(label,body) in enumerate(blocks):
  assert int(label)==expected
  rows=re.findall(r'^  \| (\d+) => (\d+)$',body,re.M)
  assert len(rows)==16 and [int(i) for i,v in rows]==list(range(16)) and body.count('  | _ => 0')==1
  values.extend(int(v) for i,v in rows)
 dispatch=re.search(r'def '+branch+r'Numerator.*?\n(.*?)\ndef '+branch+'Payment',text,re.S).group(1)
 mapping=re.findall(r'\| (\d+) => '+branch+r'Block(\d+) \(i%16\)',dispatch)
 assert mapping==[(str(i),f'{i:03d}') for i in range(64)] and '| _ => 0' in dispatch
 assert 'match i/16 with' in dispatch
 assert len(values)==1024;return values

def audit(sources=None,check_generator=True):
 baseline=json.loads((HERE/'frozen-records.json').read_text());old=baseline['records']
 current=sources if sources is not None else {str(p.relative_to(SRC)):p.read_text() for p in SRC.rglob('*.lean')}
 assert set(current)==(set(baseline['source_hashes'])-DELETED)|NEW,'exact source inventory'
 for n,h in baseline['source_hashes'].items():
  if n not in CHANGED and n not in DELETED:assert sha(current[n])==h,('outside candidate cohort changed',n)
 for b in BRANCHES:
  n=PREFIX+b.title()+'Payments.lean';a=old[n];z=current[n]
  assert declaration(a,b+'Numerator','def')==declaration(current[PREFIX+'PaymentData.lean'],b+'Numerator','def'),('Numerator interface',b)
  assert re.search(r'^def '+b+r'Payment .*$',a,re.M).group()==re.search(r'^def '+b+r'Payment .*$',z,re.M).group(),('Payment body',b)
  for suffix in ['sum','total']:assert declaration(a,b+'_'+suffix)==declaration(z,b+'_'+suffix),('public sum/total',b,suffix)
  assert a[a.index('theorem '+b+'_total'):]==z[z.index('theorem '+b+'_total'):],('total proof',b)
  n=PREFIX+b.title()+'Root.lean';assert declaration(old[n],'all_'+b+'_paid')==declaration(current[n],'all_'+b+'_paid'),('Root statement',b)
  assert 'namespace WuPaper.ClassicalFifthRational\n' in current[n]
 table=old[PREFIX+'TableCheck.lean'];cp=re.search(r'^def cPoly .*\n',table,re.M).group()
 assert noimports(current[PREFIX+'TableCheck.lean'])==noimports(table.replace(cp+'\n','',1)),'TableCheck other bodies'
 moved=current[PREFIX+'PolynomialData.lean'];assert cp in moved and 'namespace WuPaper.ClassicalFifthTableCheck\n' in moved,'cPoly body/QName'
 for b in BRANCHES:
  pd=current[PREFIX+'PaymentData.lean']
  assert definition(pd,b+'Numerator')==f'FifthIntegerPayment.paymentNumerator .{b} i','Numerator alias'
  assert definition(pd,b+'PaymentBlockSum')==f'∑ j ∈ range 64, {b}Numerator (64*b+j)','block alias'
 payment=evaluator(current);branches={}
 for b in BRANCHES:
  values=original_values(old[PREFIX+b.title()+'Payments.lean'],b)
  actual=[payment(b,i) for i in range(1024)];assert actual==values,('Nat interpreter payment mismatch',b)
  for i in [1024,1025,2048,10**9]:assert payment(b,i)==0,('outside support',b,i)
  total=int(re.search(r'theorem '+b+r'_sum .*? = (\d+) :=',old[PREFIX+b.title()+'Payments.lean']).group(1));assert sum(values)==total
  sums=current[PREFIX+b.title()+'Sums.lean'];rows=re.findall(b+r'PaymentBlockSum (\d+) = (\d+)',sums)
  assert len(rows)==16 and [int(i) for i,v in rows]==list(range(16)),'16 contiguous blocks'
  assert len(re.findall(r'^theorem '+b+r'_sum_block_\d{3}',sums,re.M))==16,'independent theorem count'
  for i,v in rows:assert int(v)==sum(actual[int(i)*64:(int(i)+1)*64]),('sum mismatch',b,i)
  branches[b]={'payments':1024,'block_sums':[int(v) for i,v in rows],'total':total,'exact_all_values_match':True}
 if check_generator:
  generator=(ROOT/'research/wu2008/diagnostics/classical_fifth_certificates.py').read_text()
  for name,h in baseline['numeric_producer_AST'].items():assert sha(ast.dump(next(v for v in ast.parse(generator).body if isinstance(v,ast.FunctionDef) and v.name==name)))==h,('numeric producer',name)
 return {'status':'PASS','baseline_archive_sha256':baseline['archive_sha256'],'modules_before':len(baseline['source_hashes']),'modules_after':len(current),'unchanged_outside_old_candidate_cohort':len(baseline['source_hashes'])-len(CHANGED|DELETED),'fixed_Git_payment_equality':3072,'interpreted_actual_Lean_Nat_payments':3072,'independent_64point_sums':48,'public_Payment_definitions':3,'Numerator_signatures':3,'sum_total_declarations':6,'Root_all_paid_declarations':3,'unchanged_Certificate':True,'cPoly_body_and_QName_preserved':True,'TableCheck_other_body_preserved':True,'outside_support_zero_guard_exact':True,'branches':branches,'candidate_source_hashes':{n:sha(current[n]) for n in sorted(CHANGED|NEW)},'interpreter_sha256':sha((HERE/'lean_nat.py').read_text()),'Lean_run':False}
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--capture',type=Path);p.add_argument('--overlay',type=Path,action='append',default=[]);a=p.parse_args()
 if a.capture:capture(a.capture)
 sources=None
 if a.overlay:
  sources={str(p.relative_to(SRC)):p.read_text() for p in SRC.rglob('*.lean') if p.name not in DELETED}
  for directory in a.overlay:
   sources.update({p.name:p.read_text() for p in directory.glob('*.lean')})
 result=audit(sources)
 if a.overlay:result['status']='CANDIDATE_ONLY_PASS_NOT_FORMAL_ACCEPTANCE'
 (HERE/('candidate-preservation.json' if a.overlay else 'preservation.json')).write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k not in ['branches','candidate_source_hashes']},indent=2))
if __name__=='__main__':main()
