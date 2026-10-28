from pathlib import Path
import json,re,hashlib,argparse
parser=argparse.ArgumentParser(description='Compare pre/post compiled declaration censuses produced by research/chen-audit/TypeCensus.lean.');parser.add_argument('census_directory',type=Path);args=parser.parse_args()
base=args.census_directory;repo=Path(__file__).resolve().parents[2];out=repo/'research/wu18938-audit'
def index(d):return {p:i for i,p in enumerate(json.loads((base/d/'type-modules.json').read_text()))}
a=index('baseline');b=index('current');plan=json.loads((out/'generated-change-plan.json').read_text());generated=set(plan['before'])|set(plan['after'])
def expected_internal(mod,name):
 if (mod=='WR2XiSourceRefinedTarget' and name.startswith('WuPaper.R2Xi.SourceContinuousCount.one8938_of_coefficient')) or (mod=='WR2ClassicalCertificate' and name.startswith('WuPaper.ClassicalSlots.one8938')):return True
 if mod=='WR2ClassicalEighthRawCertificate' and (name=='WuPaper.ClassicalEighth.payment.eq_1' or re.fullmatch(r'WuPaper\.ClassicalEighth\.raw_upper\._simp_1_\d+',name)):return True
 if mod not in generated:return False
 if re.search(r'(?:_block_\d+|_grid_block_\d+)',name):return True
 return bool(re.fullmatch(r'WR2Classical(?:FourthAll(?:BPay|CPay|DPay|Log|OuterPoint|outerPay)|Fifth(?:Initial|Middle|Terminal)Root|Sixth(?:Lower|Upper)Root|CCertificate|EighthRawCertificate)',mod) and re.search(r'\.all_[^.]+\._proof_\d+_\d+$',name))
result={'method':'Compare declaration kind and canonical expression type hash from Lean ModuleData; binder names and metadata erased. Public declarations exclude _private names. Duplicate part records are deduplicated; all kind/type variants (including exported axiom stubs and their private theorem bodies) are compared. Types of internal finite proof blocks intentionally change with compilation partition size.','unchanged_public_declarations':0,'unchanged_public_in_non_generated_modules':0,'compared_retained_modules':0,'changed_public_types':[],'removed_public_in_retained_modules':[],'added_public_in_retained_modules':[],'unexpected':[]}
for p in sorted(a.keys()&b.keys()):
 def decl(d,i):
  rs=json.loads((base/d/'types'/f'{i}.json').read_text())['declarations'];r={}
  for x in rs:
   if x['name'].startswith('_private.'):continue
   v=(x['kind'],x['typeHash']);r.setdefault(x['name'],set()).add(v)
  return {name:tuple(sorted(variants)) for name,variants in r.items()}
 aa=decl('baseline',a[p]);bb=decl('current',b[p]);mod=p[4:-5].replace('/','.');result['compared_retained_modules']+=1
 for name in aa.keys()&bb.keys():
  if aa[name]==bb[name]:
   result['unchanged_public_declarations']+=1
   if mod not in generated:result['unchanged_public_in_non_generated_modules']+=1
  else:
   row={'module':mod,'name':name,'before':aa[name],'after':bb[name]};result['changed_public_types'].append(row)
   if not expected_internal(mod,name):result['unexpected'].append(row)
 for key,names in [('removed_public_in_retained_modules',aa.keys()-bb.keys()),('added_public_in_retained_modules',bb.keys()-aa.keys())]:
  for name in sorted(names):
   row={'module':mod,'name':name};result[key].append(row)
   if not expected_internal(mod,name):result['unexpected'].append(row)
result['changed_finite_block_types']=sum(bool(re.search(r'(?:_block_\d+|_grid_block_\d+)',r['name'])) for r in result['changed_public_types'])
result['changed_coverage_auxiliary_types']=sum('._proof_' in r['name'] and '.all_' in r['name'] for r in result['changed_public_types'])
result['changed_simplifier_auxiliary_types']=sum('._simp_' in r['name'] for r in result['changed_public_types'])
# Lean emits this equation theorem where it is first requested; the new soundness
# helper requests it before the certificate. Check its type across that move.
def signature(stage,module,name):
 mods=json.loads((base/stage/'type-modules.json').read_text());rs=json.loads((base/stage/'types'/f'{mods.index(module)}.json').read_text())['declarations']
 return sorted({(r['kind'],r['typeHash']) for r in rs if r['name']==name})
moved='WuPaper.ClassicalEighth.payment.eq_1'
ms=signature('baseline','src/WR2ClassicalEighthRawCertificate.lean',moved)
assert ms and ms==signature('current','src/WR2ClassicalEighthTableCheck.lean',moved)
result['relocated_unchanged_declarations']=[{'name':moved,'before_module':'WR2ClassicalEighthRawCertificate','after_module':'WR2ClassicalEighthTableCheck','signature':ms}]
result['new_modules']=sorted(b.keys()-a.keys());result['removed_modules_count']=len(a.keys()-b.keys());result['status']='pass' if not result['unexpected'] else 'fail'
(out/'type-comparison.json').write_text(json.dumps(result,indent=2)+'\n');print({k:(len(v) if isinstance(v,list) else v) for k,v in result.items()});assert not result['unexpected'],result['unexpected'][:5]
