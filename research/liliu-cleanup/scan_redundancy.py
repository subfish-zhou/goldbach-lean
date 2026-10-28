#!/usr/bin/env python3
from pathlib import Path
import collections,hashlib,json,re
import argparse
parser=argparse.ArgumentParser(description='Read-only conservative Li-Liu declaration pruning scan. No production sources are changed.')
parser.add_argument('--census',type=Path,required=True)
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args()
ROOT=Path(__file__).resolve().parents[2];OUT=args.output.resolve();CENSUS=args.census.resolve();OUT.mkdir(parents=True,exist_ok=False)
for rel,digest in json.loads((CENSUS/'source-inputs.json').read_text()).items():
 assert hashlib.sha256((ROOT/rel).read_bytes()).hexdigest()==digest, 'Census source mismatch: '+rel
D=json.loads((CENSUS/'declarations.json').read_text());OWN={n:set(v) for n,v in json.loads((CENSUS/'owners.json').read_text()).items()};GRAPH=json.loads((CENSUS/'imports.json').read_text());SOURCE={m:ROOT/Path(*m.split('.')).with_suffix('.lean') for m in GRAPH}
def closure(g,roots):
 seen=set();todo=list(roots)
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n);todo.extend(g.get(n,[]))
 return seen
CHEN=closure(GRAPH,['Goldbach.Theorem']);LI={m for m in GRAPH if 'LiLiu' in m and m not in CHEN}
GUARD='MathlibNt.SieveTheory.LiLiuGoldbachFinalCoefficientsReachability'
SKIP={GUARD}
NS='MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.'
VIRTUAL={NS+'goldbach_onePlusOneNine_nat_unconditional':{NS+'goldbach_D19_gt_paper_0004','MathlibNt.SieveTheory.LiLiuOnePlusOneNine.D19_pos_iff','MathlibNt.SieveTheory.SingularSeries.liuSingularSeries_pos'},NS+'goldbach_onePlusOneNine_unconditional':{NS+'goldbach_onePlusOneNine_nat_unconditional','MathlibNt.SieveTheory.LiLiuOnePlusOneNine.oneNine_power_iff_source_exponent'}}
REF={n:set(d['type']+d['value']+d['recursorRHS']) for n,d in D.items()};SRC=collections.defaultdict(set);GLOBAL=collections.defaultdict(set);ILEAN={};unknown_owners=collections.Counter()
for m in GRAPH:
 p=ROOT/'.lake/build/lib/lean'/Path(*m.split('.')).with_suffix('.ilean');r=json.loads(p.read_text());ILEAN[m]=r
 if m in SKIP:continue
 for key,data in r['references'].items():
  k=json.loads(key)
  if 'c' not in k:continue
  dep=k['c']['n']
  for u in data['usages']:
   parent=u[4] if len(u)>4 else None
   if parent in D:SRC[parent].add(dep)
   else:GLOBAL[m].add(dep)
for n,deps in VIRTUAL.items():REF[n]=set(D[n]['type'])|deps;SRC[n]=set(deps)
EDGES={n:deps|SRC[n] for n,deps in REF.items()}
roots={n for n,ms in OWN.items() if any(m not in LI for m in ms)}
roots.update(x['declaration'] for x in json.loads((ROOT/'blueprint/nodes.json').read_text()))
roots.update(VIRTUAL);roots.update([NS+'goldbachWeight_authorG11_numericLedger',NS+'goldbachG67IntegralConstant_lower_certified','G12AnalyticCertificate.actual_le_target',NS+'G9Analytic.actual_le_target'])
if (OUT/'additional-roots.json').exists():roots.update(json.loads((OUT/'additional-roots.json').read_text()))
while True:
 needed=closure(EDGES,roots);usedmods={m for n in needed for m in OWN.get(n,[])}|{GUARD}
 newroots={n for m in usedmods if m not in SKIP for n in GLOBAL[m]} | {n for m in usedmods for n in ILEAN[m]['decls'] if '__macroRules__' in n}
 if newroots<=roots:break
 roots.update(newroots)
prefixes={'.'.join(n.split('.')[:i]) for n in needed for i in range(1,len(n.split('.'))+1)}
plan={};deleted=[];removed=[]
for m in sorted(LI-SKIP):
 text=SOURCE[m].read_text();lines=text.splitlines(keepends=True);groups=[]
 for n,rg in ILEAN[m]['decls'].items():
  a,b=rg[0],rg[2]
  if rg[1]!=0:continue
  while a>0 and (re.search(r'^\s*(?:set_option|omit|include)\b.*\bin\s*$',lines[a-1]) or re.search(r'^\s*open\b.*\bin\s*$',lines[a-1])):a-=1
  groups.append([a,b,{n}])
 groups.sort(key=lambda g:(g[0],g[1]));merged=[]
 for a,b,ns in groups:
  if merged and a<=merged[-1][1]:merged[-1][1]=max(b,merged[-1][1]);merged[-1][2]|=ns
  else:merged.append([a,b,ns])
 cuts=[];kept=[]
 for a,b,ns in merged:
  # Type/constructor references keep their enclosing declaration as well.
  live=any(n in needed or n in prefixes or n not in D for n in ns)
  if live:kept.extend(ns)
  else:cuts.append((a,b));removed.append({'module':m,'names':sorted(ns),'start_line':a+1,'end_line':b+1})
 module_live=bool(kept) or any(n in needed for n in ILEAN[m]['decls'])
 # Unnamed commands in diagnostic modules do not contribute production proofs.
 if not module_live and m not in usedmods:deleted.append(m);plan[m]=None
 else:
  erase={i for a,b in cuts for i in range(a,b+1)}
  updated=''.join(line for i,line in enumerate(lines) if i not in erase)
  # Diagnostics attached to private or removed declarations have no remaining role.
  updated=re.sub(r'^\s*#(?:check|print)\b[^\n]*(?:\n|$)','',updated,flags=re.M)
  updated=re.sub(r'\n{4,}','\n\n\n',updated)
  if updated!=text:plan[m]=updated
(OUT/'ilean-inputs.json').write_text(json.dumps({m:hashlib.sha256((ROOT/'.lake/build/lib/lean'/Path(*m.split('.')).with_suffix('.ilean')).read_bytes()).hexdigest() for m in GRAPH},indent=2)+'\n')
(OUT/'prune-plan.json').write_text(json.dumps({'deleted_modules':deleted,'removed_declarations':removed,'changed_modules':sorted(plan),'protected_roots':sorted(roots),'source_and_compiled_reached_names':len(needed),'needed_modules':sorted(usedmods)},indent=2)+'\n')
(OUT/'planned-sources.json').write_text(json.dumps(plan))
print('Candidate Li-Liu modules:',len(LI),'planned deletions:',len(deleted),'pruned declaration blocks:',len(removed),'changed modules:',len(plan),'conservative reached names:',len(needed))
for m in ['MathlibNt.SieveTheory.LiLiuGoldbachS4IntegralScalar','MathlibNt.SieveTheory.LiLiuGoldbachB10IntegralScalar','MathlibNt.SieveTheory.LiLiuGoldbachG11UniformScalar','MathlibNt.SieveTheory.LiLiuGoldbachG11MainMassBuchstab']:
 print(m,'DELETE' if m in deleted else 'keep/prune')
