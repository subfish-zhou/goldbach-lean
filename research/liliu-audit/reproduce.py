#!/usr/bin/env python3
"""Inspect the existing main-library objects for Li-Liu simplification candidates.

Run after a matching complete main build. The output directory must be new.
The tool reads production sources and objects without modifying or rebuilding them.
Candidate areas are not proven deletions; other consumers and elaboration still
need checking before any cleanup.
"""
from pathlib import Path
import argparse,hashlib,json,importlib.util,re,collections,subprocess,os
root=Path(__file__).resolve().parents[2]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args();out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
spec=importlib.util.spec_from_file_location('exporter',root/'scripts/build_project_structure.py');exporter=importlib.util.module_from_spec(spec);spec.loader.exec_module(exporter)
spec=importlib.util.spec_from_file_location('checks',root/'scripts/check.py');checks=importlib.util.module_from_spec(spec);spec.loader.exec_module(checks)
sources={str(p.relative_to(root).with_suffix('')).replace('/','.'):p for p in checks.source_files()}
mods=sorted(sources);(out/'modules.json').write_text(json.dumps(mods))
source_inputs={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources.values()}
for relative in ['lean-toolchain','lakefile.toml','lake-manifest.json','scripts/check.py','scripts/build_project_structure.py','research/chen-audit/TypeCensus.lean']:
 source_inputs[relative]=hashlib.sha256((root/relative).read_bytes()).hexdigest()
(out/'source-inputs.json').write_text(json.dumps(source_inputs,indent=2)+'\n')
(out/'types').mkdir();manifest=[];objects={}
for i,m in enumerate(mods):
 obj=root/'.lake/build/lib/lean'/Path(*m.split('.')).with_suffix('.olean');assert obj.is_file(),f'Build the main tree first: {m}'
 manifest.append(f"{sources[m]}\t{obj}\t{out}/types/{i}.json")
 for p in [obj,Path(str(obj)+'.private'),Path(str(obj)+'.server'),obj.with_suffix('.ir.sig'),obj.with_suffix('.ir')]:
  if p.exists():objects[str(p.relative_to(root))]=hashlib.sha256(p.read_bytes()).hexdigest()
(out/'object-inputs.json').write_text(json.dumps(objects,indent=2)+'\n')
(out/'manifest.tsv').write_text('\n'.join(manifest)+'\n')
env=os.environ.copy();env.pop('LEAN_PATH',None);env.pop('LEAN_SRC_PATH',None)
with (out/'extraction.log').open('w') as log:
 subprocess.run(['lake','env','lean','--run','research/chen-audit/TypeCensus.lean',str(out/'manifest.tsv')],cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
decls={};owners=collections.defaultdict(set);graph={};stats={};variants={}
for i,m in enumerate(mods):
 raw=json.loads((out/'types'/f'{i}.json').read_text());source=root/Path(*m.split('.')).with_suffix('.lean');text=source.read_text();graph[m]=[n for n in raw['sourceImports'] if n in mods];stats[m]={'code_lines':checks.count_code_lines(text),'physical_lines':len(text.splitlines()),'sha256':hashlib.sha256(source.read_bytes()).hexdigest()}
 for d in exporter.normalize_declarations(raw):
  n=d['name'];old=decls.get(n)
  if old is not None and old!=d:
   assert n.endswith('.eq_def'),n
   assert {k:v for k,v in old.items() if k!='value'}=={k:v for k,v in d.items() if k!='value'},n
   variants[n]=variants.get(n,0)+1;d=dict(d,value=sorted(set(old['value'])|set(d['value'])))
  decls[n]=d;owners[n].add(m)
refs={n:set(d['type']+d['value']+d['recursorRHS']) for n,d in decls.items()}
def closure(g,roots):
 seen=set();pending=list(roots)
 while pending:
  n=pending.pop()
  if n in seen:continue
  seen.add(n);pending.extend(g.get(n,[]))
 return seen
def providers(names):return {m for n in names for m in owners.get(n,[])}
def summary(ms):return {'modules':len(ms),'code_lines':sum(stats[m]['code_lines'] for m in ms),'physical_lines':sum(stats[m]['physical_lines'] for m in ms)}
roots={'existence':['Goldbach.one_plus_one_nine','Goldbach.one_plus_one_nine_real'],'count':['Goldbach.one_plus_one_nine_count','Goldbach.one_plus_one_nine_lower_bound'],'chen':['Goldbach.chen_theorem','Goldbach.representation_lower_bound']}
def scope_census(ms):
 ds={};os=collections.defaultdict(set)
 for i,m in enumerate(mods):
  if m not in ms:continue
  for d in exporter.normalize_declarations(json.loads((out/'types'/f'{i}.json').read_text())):
   n=d['name'];old=ds.get(n)
   if old is not None and old!=d:
    assert n.endswith('.eq_def'),n
    assert {k:v for k,v in old.items() if k!='value'}=={k:v for k,v in d.items() if k!='value'},n
    d=dict(d,value=sorted(set(old['value'])|set(d['value'])))
   ds[n]=d;os[n].add(m)
 return ds,os
imps=closure(graph,['Goldbach.OnePlusOneNine']);liDecls,liOwners=scope_census(imps)
liRefs={n:set(d['type']+d['value']+d['recursorRHS']) for n,d in liDecls.items()}
reached={k:closure(liRefs,v) for k,v in roots.items() if k!='chen'}
chenImps=closure(graph,['Goldbach.Theorem']);chenDecls,chenOwners=scope_census(chenImps)
chenRefs={n:set(d['type']+d['value']+d['recursorRHS']) for n,d in chenDecls.items()}
reached['chen']=closure(chenRefs,roots['chen'])
allLi=reached['existence']|reached['count'];isLi=lambda m:'LiLiu' in m
ownersGlobal=owners;owners=liOwners

publicRoots=['Goldbach','Goldbach.All','Goldbach.Checks','Goldbach.OnePlusOneNineChecks','Goldbach.Blueprint','MathlibNt','AnalyticNumberTheory'];supported=closure(graph,publicRoots)
countProviders=providers(reached['count']);existProviders=providers(reached['existence']);bothProviders=providers(allLi)
result={'source_modules':len(mods),'local_declarations':len(decls),'paper':'https://arxiv.org/html/2606.05224v1','import_closure':summary(imps),'reference_closures':{k:summary(providers(v)) for k,v in reached.items() if k!='chen'},'existence_only_provider_modules':summary(existProviders-countProviders),'no_reached_declarations':summary(imps-bothProviders),'unresolved_liliu_references':sorted(n for n in allLi if n not in liDecls and n.startswith(('MathlibNt.','Goldbach.','AnalyticNumberTheory.','PrimeNumberTheoremAnd.'))),'library_only_liliu':summary({m for m in set(mods)-supported if isLi(m)}),'generated_equation_variants':variants,'candidate_modules':{label:[dict(module=m,**stats[m]) for m in sorted(ms,key=lambda m:(-stats[m]['code_lines'],m))] for label,ms in [('existence_only',existProviders-countProviders),('no_reached_declarations',imps-bothProviders),('library_only_liliu',{m for m in set(mods)-supported if isLi(m)})]},'module_statistics':stats}
result.update(base_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),source_state='Working tree identified by source-inputs.json; base_head is not an assertion that the measured sources are committed.',method='Compiled type/value/recursor references, with independent declaration censuses restricted to each theorem import closure. External declarations are leaves. Conflicting generated eq_def proof variants union their recorded references conservatively. Module counts are candidate areas, not deletable-line estimates.',source_input_manifest_sha256=hashlib.sha256((out/'source-inputs.json').read_bytes()).hexdigest(),object_input_manifest_sha256=hashlib.sha256((out/'object-inputs.json').read_bytes()).hexdigest())
assert not result['unresolved_liliu_references'],result['unresolved_liliu_references']
for n,h in source_inputs.items():assert hashlib.sha256((root/n).read_bytes()).hexdigest()==h,n
for n,h in objects.items():assert hashlib.sha256((root/n).read_bytes()).hexdigest()==h,n
assert set(sources.values())==set(checks.source_files()),'Source inventory changed'
(out/'analysis.json').write_text(json.dumps(result,indent=2)+'\n');(out/'declarations.json').write_text(json.dumps(decls));(out/'owners.json').write_text(json.dumps({n:sorted(ms) for n,ms in ownersGlobal.items()}));(out/'references.json').write_text(json.dumps({n:sorted(ms) for n,ms in reached.items()}));(out/'imports.json').write_text(json.dumps(graph))
# Summarize disjoint review areas and incoming references from the full census.
chenImports=closure(graph,['Goldbach.Theorem'])
liUnreached={row['module'] for row in result['candidate_modules']['no_reached_declarations'] if isLi(row['module'])}
liExistence={row['module'] for row in result['candidate_modules']['existence_only'] if isLi(row['module'])}
libraryOnly={row['module'] for row in result['candidate_modules']['library_only_liliu']}
assert not liUnreached&liExistence and not libraryOnly&liUnreached and not libraryOnly&liExistence
pool=liUnreached|liExistence|libraryOnly
incoming=collections.defaultdict(set)
for n,d in decls.items():
 for dep in d['type']+d['value']+d['recursorRHS']:
  for target in ownersGlobal.get(dep,[]):
   for source in ownersGlobal[n]:
    if target!=source:incoming[target].add(source)
consumers={m:{'inside_candidate_pool':sorted(incoming[m]&pool),'outside_candidate_pool':sorted(incoming[m]-pool)} for m in sorted(pool)}
(out/'candidate-consumers.json').write_text(json.dumps(consumers,indent=2)+'\n')
classification=collections.defaultdict(set)
for m in libraryOnly:
 tag='audit_check_inspection_by_name' if any(n in m for n in ['AxiomCheck','Audit','Reachability','PublicStd','ProductionCheck']) else 'other_proof_or_alternative'
 classification[tag].add(m)
summaryReport={'scope':'Gross candidate areas before implementation, not achieved or guaranteed net savings. Line totals count whole modules.',
 'current_main':summary(set(mods)),'current_liliu':result['import_closure'],
 'shared_with_chen':summary(imps&chenImports),'liliu_outside_chen':summary(imps-chenImports),
 'gross_liliu_named_review_pool':summary(pool),
 'outside_supported_roots_classification':{tag:summary(ms) for tag,ms in sorted(classification.items())},
 'conversion_helpers_to_retain':[{'module':m,'code_lines':stats[m]['code_lines']} for m in ['MathlibNt.SieveTheory.LiLiuGoldbachOneNineLiteralExponent','MathlibNt.Analysis.RationalPower'] if m in stats],
 'protected_public_declarations':roots['existence']+roots['count']}
(out/'summary.json').write_text(json.dumps(summaryReport,indent=2)+'\n')
for k in ['source_modules','local_declarations','import_closure','reference_closures','existence_only_provider_modules','no_reached_declarations','library_only_liliu']:print(k,result[k])
