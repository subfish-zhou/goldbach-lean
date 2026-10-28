#!/usr/bin/env python3
"""Generate complete direct371 source drafts; never executes Lean or adoption."""
from pathlib import Path
from fractions import Fraction as F
import argparse,ast,copy,hashlib,importlib.util,json
HERE=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('base371',HERE/'generate.py');base=importlib.util.module_from_spec(sp);sp.loader.exec_module(base)
hf=base.hf;sha=lambda b:hashlib.sha256(b).hexdigest()

def semantic_text(nodes,shared,scales,plan):
 fragments=json.loads((HERE/'inputs/semantic-fragments.json').read_text())
 expected_get=fragments['expected_get'];suffix=fragments['run_suffix']
 suffix=suffix.replace('Program.', 'DirectProgram.').replace('381','371').replace('380','370')
 s='import Hf4CheckedDagSoundness\nimport Hf4DirectDagProgram\nimport Hf4DirectDag\nimport Mathlib.Tactic.FinCases\n\n/-! UNCOMPILED371-node bridge adapted from actual passed semantic01. -/\nset_option maxRecDepth 30000\n\nnamespace Hf4Quad.CheckedDag.DirectSemantics\nopen Hf4Quad.DirectDag\n\n'
 for name,js in [('original',range(371)),('seedFun',sorted(shared))]:
  s+=f'noncomputable def {name} (m h : ℚ) : ℕ → ℝ → ℝ\n'
  for j in js:s+=f'  | {j} => fun x => f{j} ((m:ℝ)+(h:ℝ)*x)\n'
  s+='  | _ => fun _ => 0\n\n'
 s+='noncomputable def expected (m h : ℚ) : ℕ → List (ℝ → ℝ)\n  | 0 => []\n  | n+1 => original m h n :: expected m h n\n\n'+expected_get
 for j,step in enumerate(plan):
  op,*args=step
  argstr=' '.join('('+hf.lean(F(v))+')'if op=='scale'and k==0 else str(v)for k,v in enumerate(args))
  st='Step.'+op+(' '+argstr if args else '')
  s+=f'private theorem step_{j:03} (m h : ℚ) :\n    nextFun (seedFun m h) m h ({st}) (expected m h {j}) = original m h {j} := by\n'
  if op in ['variable','shared']:s+='  rfl\n\n';continue
  get=lambda a:f'getFun (expected m h {j}) {a} x'
  if op=='neg':refs=args;rhs='-'+get(args[0])
  elif op in ['addExact','add','mul']:
   refs=args if op=='addExact'else args[1:];rhs=get(refs[0])+(' * 'if op=='mul'else' + ')+get(refs[1])
  elif op=='inv':refs=args[1:];rhs='('+get(refs[0])+')⁻¹'
  elif op=='scale':refs=args[1:];rhs=f'((({hf.lean(F(args[0]))}):ℚ):ℝ) * '+get(refs[0])
  s+=f'  change (fun x => {rhs}) = original m h {j}\n'
  s+='  rw ['+', '.join(f'expected_get m h {j} {a} (by decide)'for a in dict.fromkeys(refs))+']\n'
  if op=='scale':
   k,parent=scales[j];assert nodes[j][1]!=parent,'right coefficient needs explicit mul_comm'
   s+='  funext x\n'
   s+=f'  exact congrArg (fun c : ℝ => c * original m h {parent} x)\n    (by norm_num : ((({hf.lean(k)}):ℚ):ℝ) = ({hf.lean(k)}:ℝ))\n\n'
  else:s+='  rfl\n\n'
 s+='theorem plan_length : DirectProgram.plan.length = 371 := by rfl\n\ntheorem local_steps (m h : ℚ) (j : Fin 371) :\n    nextFun (seedFun m h) m h (DirectProgram.plan[j.val]?.getD Step.variable)\n      (expected m h j.val) = original m h j.val := by\n  fin_cases j\n'
 for j in range(371):s+=f'  · exact step_{j:03} m h\n'
 return s+'\n'+suffix+'end Hf4Quad.CheckedDag.DirectSemantics\n#print axioms Hf4Quad.CheckedDag.DirectSemantics.original_f370\n'

def seed_text(nodes,models,shared):
 s='import Hf4DirectDagSemantics\nimport Hf4QuadRationalModel\n\n/-! UNCOMPILED seed bridge; no original381 SharedCertificates import. -/\nnamespace Hf4Quad.CheckedDag.DirectSemantics\nopen RationalModel\n\n'
 def ancestors(j):
  op,*args=nodes[j]
  return [j]+([]if op in ['const','rad','var']else sum((ancestors(a)for a in args),[]))
 for j in sorted(shared):
  p,e=models[0][j];ds=', '.join(f'DirectDag.f{k}'for k in dict.fromkeys(ancestors(j)))
  s+=f'private theorem seed_valid_{j:03} (m h : ℚ) :\n    (DirectProgram.seeds {j}).Valid (seedFun m h {j}) := by\n'
  simp='DirectProgram.seeds, seedFun, '+ds+', Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero, Rat.cast_neg'
  if j==1:s+='  convert radical using 1 <;>\n    norm_num [Certificate.Valid, Certificate.cubic, DirectProgram.seeds, seedFun, DirectDag.f1]\n\n'
  elif e==0:s+=f'  simpa only [{simp}] using constant ({hf.lean(p[0])}:ℚ)\n\n'
  else:
   assert j==299 and p[0]==189*models[0][1][0][0]and e==189*models[0][1][1]
   s+='  convert radical.scale (189:ℚ) using 1 <;>\n    norm_num [Certificate.Valid, Certificate.cubic, RationalModel.scale, DirectProgram.seeds, seedFun, DirectDag.f299, DirectDag.f217, DirectDag.f1]\n\n'
 s+='theorem seed_sound (m h : ℚ) (k : ℕ) :\n    (DirectProgram.seeds k).Valid (seedFun m h k) := by\n'
 for j in sorted(shared):s+=f'  by_cases hk{j} : k = {j}\n  · subst k\n    exact seed_valid_{j:03} m h\n'
 s+='  simpa only [DirectProgram.seeds, seedFun, zero, Rat.cast_zero, '+', '.join('hk'+str(j)for j in sorted(shared))+'] using constant (0:ℚ)\n\nend Hf4Quad.CheckedDag.DirectSemantics\n#print axioms Hf4Quad.CheckedDag.DirectSemantics.seed_sound\n'
 return s

def original_soundness(inverse=False):
 ns='Hf4Quad.InverseDag.Direct'if inverse else'Hf4Quad.CheckedDag.DirectProof'
 imports='import Hf4DirectDagSeedSoundness\n'+('import Hf4InverseDagSoundness\n'if inverse else'')
 return imports+f'''
/-! UNCOMPILED original-kernel bridge. The interval premises are exactly the
old cell domain: h>=0 and m-h>=1; arithmetic precision/budgets are unchanged. -/
namespace {ns}
open Hf4Quad.CheckedDag
open Hf4Quad.CheckedDag.DirectSemantics
open Hf4Quad.RationalModel

theorem direct_model (literals : ℕ → Certificate) (m h : ℚ)
    (ok : checked DirectProgram.seeds literals m h DirectProgram.plan [] = true) :
    (getCert (run DirectProgram.seeds literals m h DirectProgram.plan []) 0).Valid
      (fun x => directKernel ((m:ℝ)+(h:ℝ)*x)) := by
  have good := run_sound DirectProgram.seeds literals (seedFun m h) m h
    (seed_sound m h) DirectProgram.plan [] [] nil_valid ok
  have last := good 0
  rw [original_f370] at last
  simpa only [DirectDag.direct_kernel_dag] using last

theorem original_compact_model (literals : ℕ → Certificate) (m h : ℚ)
    (hh : 0 ≤ (h:ℝ)) (hm : 1 ≤ (m:ℝ)-(h:ℝ))
    (ok : checked DirectProgram.seeds literals m h DirectProgram.plan [] = true) :
    (getCert (run DirectProgram.seeds literals m h DirectProgram.plan []) 0).Valid
      (fun x => compactKernel ((m:ℝ)+(h:ℝ)*x)) := by
  have good := direct_model literals m h ok
  intro x hx
  have hl := (abs_le.mp hx).1
  have hp : 0 ≤ (h:ℝ)*(x+1) := mul_nonneg hh (by linarith only [hl])
  have ht : 1 ≤ (m:ℝ)+(h:ℝ)*x := by nlinarith only [hm, hp]
  simpa only [compactKernel_eq_directKernel ht] using good x hx

end {ns}
#print axioms {ns}.original_compact_model
'''

def inverse_panel(models,plan,literals):
 s='import Hf4DirectDagProgram\nimport Hf4InverseDagData\n\n/-! UNCOMPILED371-node inverse-only Panel0;22 literal checkpoints. -/\nnamespace Hf4Quad.InverseDag.DirectPanel0\nopen CheckedDag\nopen CheckedDag.DirectProgram\n\ndef literals : ℕ → RationalModel.Certificate\n'
 for slot,j in enumerate(literals):
  if plan[j][0]=='inv':s+=f'  | {slot} => {base.record(models[0][j])}\n'
 return s+'''  | _ => zero

def midpoint : ℚ := 41/40
def halfwidth : ℚ := 1/40

def rangeCheck (start width : ℕ) : Bool :=
  checkRange plan seeds literals midpoint halfwidth start width

def finalCertificate : RationalModel.Certificate :=
  getCert (run seeds literals midpoint halfwidth plan []) 0

end Hf4Quad.InverseDag.DirectPanel0
'''

def inverse_checks():
 return base.checks_text(32).replace('Hf4DirectDagPanel0Data','Hf4DirectInversePanel0Data').replace('Hf4Quad.CheckedDag.DirectPanel0','Hf4Quad.InverseDag.DirectPanel0')

def inverse_model(models):
 fields=['a','b','c','d','error'];p,e=models[0][-1];vals=p+[e]
 s='import Hf4DirectInversePanel0Checks32\nimport Hf4InverseDagChunks\nimport Hf4DirectInverseOriginalSoundness\n\n/-! UNCOMPILED371-node model,12 bounded chunks and5 separate field decisions. -/\nnamespace Hf4Quad.InverseDag.DirectPanel0\nopen CheckedDag\nopen CheckedDag.DirectProgram\n\ntheorem all_checked : checked seeds literals midpoint halfwidth plan [] = true := by\n  have h0 : checked seeds literals midpoint halfwidth (plan.take 0) [] = true := rfl\n'
 prev=0
 for k,start in enumerate(range(0,371,32)):
  width=min(32,371-start);end=start+width
  s+=f'  have h{end} := checked_prefix_extend plan seeds literals midpoint halfwidth {start} {width}\n    h{prev} checked32_{k:02}\n';prev=end
 s+='  apply checked_from_complete_prefix\n  simpa only [DirectSemantics.plan_length] using h371\n\n'
 for field,val in zip(fields,vals):s+=f'set_option maxHeartbeats 4000000 in\nset_option maxRecDepth 30000 in\ntheorem final_{field}_eq : finalCertificate.{field} = ({hf.lean(val)}:ℚ) := by\n  decide +kernel\n\n'
 s+='''theorem reconstructed_model : finalCertificate.Valid
    (fun x => compactKernel ((41/40:ℝ)+(1/40:ℝ)*x)) := by
  have hh := Direct.original_compact_model literals midpoint halfwidth
    (by norm_num [halfwidth]) (by norm_num [midpoint, halfwidth]) all_checked
  simpa only [finalCertificate, midpoint, halfwidth, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using hh

end Hf4Quad.InverseDag.DirectPanel0

namespace Hf4Quad.DirectPanel0
open RationalModel

'''
 s+=f'def c370 : Certificate := {base.record(models[0][-1])}\n\n'
 s+='theorem reconstructed_c370_eq : InverseDag.DirectPanel0.finalCertificate = c370 := by\n'
 for f in fields:s+=f'  have h_{f} := InverseDag.DirectPanel0.final_{f}_eq\n'
 s+='  cases hrecord : InverseDag.DirectPanel0.finalCertificate with\n  | mk a b c d error =>\n'
 s+='    rw [hrecord] at '+' '.join('h_'+f for f in fields)+'\n'
 for f,v in zip(fields,vals):s+=f'    change {f} = ({hf.lean(v)}:ℚ) at h_{f}\n'
 s+='    simp only [c370,'+','.join('h_'+f for f in fields)+']\n\n'
 s+='''theorem compact_model : c370.Valid (fun x => compactKernel ((41/40)+(1/40)*x)) := by
  rw [← reconstructed_c370_eq]
  exact InverseDag.DirectPanel0.reconstructed_model

end Hf4Quad.DirectPanel0
#print axioms Hf4Quad.DirectPanel0.compact_model
'''
 return s

def endpoint_text():
 return '''import Hf4DirectInversePanel0Model
import Hf4QuadCompactIntegral

/-! UNCOMPILED unchanged original Panel0 bounds, separate provisional namespace. -/
noncomputable section
namespace Hf4Quad.DirectPanel0
open RationalModel

theorem mass_bounds : ((17511388157/6000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass 1 (21/20) ∧
    SigmaActualBlockSeparable.endpointCellMass 1 (21/20) ≤ (21990320141/6000000000000000) := by
  have hh := endpoint_compact_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(41/40)-(1/40)) (by norm_num : ((41/40):ℝ)+(1/40)≤3) compact_model
  norm_num [Certificate.cubic,c370] at hh
  constructor <;> linarith only [hh.1,hh.2]

end Hf4Quad.DirectPanel0
#print axioms Hf4Quad.DirectPanel0.mass_bounds
'''

def audit_plan(nodes,models,shared,plan,literals):
 seeds={j:tuple(models[0][j][0]+[models[0][j][1]])for j in shared}
 payloads=[{slot:tuple(m[j][0]+[m[j][1]])for slot,j in enumerate(literals)}for m in models]
 arity={'variable':0,'shared':1,'neg':1,'addExact':2,'scale':2,'add':3,'mul':3,'inv':2}
 def run(pp,dd,ss,inverse):
  checks=0;flat=[]
  for i,data in enumerate(dd):
   env=[]
   for j,step in enumerate(pp):
    kind,*args=step;assert kind in arity and len(args)==arity[kind]
    if kind in ['add','mul','inv']:refs=args[1:]
    elif kind=='scale':refs=args[1:]
    elif kind in ['neg','addExact']:refs=args
    else:refs=[]
    assert all(type(a)is int and 0<=a<len(env)for a in refs)
    if kind=='variable':v=(F(41+2*i,40),F(1,40),F(0),F(0),F(0))
    elif kind=='shared':assert args[0]in ss;v=ss[args[0]]
    elif kind=='neg':a=env[args[0]];v=tuple(-x for x in a[:4])+(a[4],)
    elif kind=='addExact':a,b=(env[x]for x in args);v=tuple(x+y for x,y in zip(a,b))
    elif kind=='scale':k=F(args[0]);a=env[args[1]];v=tuple(k*x for x in a[:4])+(abs(k)*a[4],)
    else:
     slot,*refs=args;a=env[refs[0]]
     if not inverse or kind=='inv':assert slot in data;v=data[slot]
     if kind in ['add','mul']:
      b=env[refs[1]]
      if inverse:
       if kind=='add':p=list(map(hf.floor,(x+y for x,y in zip(a[:4],b[:4]))));e=hf.ceil(a[4]+b[4]+sum(abs(a[k]+b[k]-p[k])for k in range(4)))
       else:p=list(map(hf.floor,hf.prod(a[:4],b[:4])[:4]));e=hf.ceil(a[4]*sum(map(abs,b[:4]))+b[4]*sum(map(abs,a[:4]))+a[4]*b[4]+hf.err(a[:4],b[:4],p))
       v=tuple(p)+(e,)
      if kind=='add':assert a[4]+b[4]+sum(abs(a[k]+b[k]-v[k])for k in range(4))<=v[4]
      else:assert a[4]*sum(map(abs,b[:4]))+b[4]*sum(map(abs,a[:4]))+a[4]*b[4]+hf.err(a[:4],b[:4],v[:4])<=v[4]
     else:
      low=abs(a[0])-sum(map(abs,a[1:4]))-a[4];assert low>0
      assert hf.err(a[:4],v[:4],[F(1),F(0),F(0),F(0)])+sum(map(abs,v[:4]))*a[4]<=low*v[4]
     checks+=1
    assert v==tuple(models[i][j][0]+[models[i][j][1]]),(i,j)
    env.insert(0,v);flat.extend([i,j,k,str(x)]for k,x in enumerate(v))
  return sha(json.dumps(flat,separators=(',',':')).encode()),checks
 checked=run(plan,payloads,seeds,False)
 sparse=[{slot:v for slot,v in p.items()if plan[literals[slot]][0]=='inv'}for p in payloads]
 inverse=run(plan,sparse,seeds,True);assert checked==inverse and checked[1]==5800
 negatives=[]
 for case in ['negative_ref','future_ref','unknown_step','missing_inverse','changed_inverse','changed_seed']:
  pp=copy.deepcopy(plan);dd=copy.deepcopy(sparse);ss=copy.deepcopy(seeds)
  ix=next(j for j,r in enumerate(pp)if r[0]=='inv');slot=pp[ix][1]
  if case=='negative_ref':pp[ix][-1]=-1
  elif case=='future_ref':pp[ix][-1]=ix
  elif case=='unknown_step':pp[0][0]='unknown'
  elif case=='missing_inverse':del dd[0][slot]
  elif case=='changed_inverse':dd[0][slot]=(dd[0][slot][0]+1,)+dd[0][slot][1:]
  else:ss[1]=(ss[1][0]+1,)+ss[1][1:]
  try:run(pp,dd,ss,True)
  except (AssertionError,ValueError,KeyError,TypeError):negatives.append(case)
  else:raise AssertionError('negative control accepted '+case)
 return {'status':'PYTHON_EXACT_RECONSTRUCTION_PASS_NOT_LEAN','checked_and_inverse_canonical_sha256':checked[0],'reconstructed_fields_each_route':74200,'all_arithmetic_conditions_checked_each_route':checked[1],'inverse_literals_all40':880,'negative_controls_rejected':negatives}

def generate():
 outputs=base.generate();base_manifest=outputs.pop('manifest.json');outputs['base-manifest.json']=base_manifest
 nodes=base.direct_nodes();models=[hf.evaluate(nodes,i)for i in range(40)];shared,derived,scales,plan,literals=base.layout(nodes,models)
 numeric=audit_plan(nodes,models,shared,plan,literals)
 outputs['numeric-audit.json']=(json.dumps(numeric,indent=2)+'\n').encode()
 new={'Hf4DirectDagSemantics':semantic_text(nodes,shared,scales,plan),'Hf4DirectDagSeedSoundness':seed_text(nodes,models,shared),'Hf4DirectDagOriginalSoundness':original_soundness(False),'Hf4DirectInverseOriginalSoundness':original_soundness(True),'Hf4DirectInversePanel0Data':inverse_panel(models,plan,literals),'Hf4DirectInversePanel0Checks32':inverse_checks(),'Hf4DirectInversePanel0Model':inverse_model(models),'Hf4DirectInversePanel0Endpoint':endpoint_text()}
 outputs.update({'lean/'+n+'.lean':s.encode()for n,s in new.items()})
 generic=['Hf4CheckedDagData','Hf4CheckedDagSoundness','Hf4InverseDagData','Hf4InverseDagSoundness','Hf4InverseDagChunks','Hf4ConstructionRounding','Hf4ConstructionConditions']
 for n in generic:outputs['lean/'+n+'.lean']=(HERE/'inputs'/str(n+'.lean')).read_bytes()
 # Use the project's actual counter, not a second line-count definition.
 path=HERE.parents[1]/'lib/source_counter.py';spec=importlib.util.spec_from_file_location('linecounter',path);counter=importlib.util.module_from_spec(spec);spec.loader.exec_module(counter)
 def effective(b):return sum(bool(line.strip())for line in counter.code_only(b.decode()).splitlines())
 counts={n:{'physical':len(b.splitlines()),'effective':effective(b),'bytes':len(b)}for n,b in outputs.items()if n.endswith('.lean')}
 manifest={'status':'COMPLETE_DIRECT371_SOURCE_DRAFT_UNCOMPILED_NOT_ACCEPTED','producer_sha256':sha(Path(__file__).read_bytes()),'base_producer_sha256':sha((HERE/'generate.py').read_bytes()),'base_manifest_sha256':sha(base_manifest),'precision_denominator':hf.D,'fields':74200,'canonical_fields_sha256':json.loads(base_manifest)['field_canonical_sha256'],'nodes':371,'shared':47,'inverse_literals_per_panel':22,'copied_generic_modules':generic,'input_sha256':{str(p.relative_to(HERE)):sha(p.read_bytes())for p in (HERE/'inputs').glob('*.lean')},'files':{n:sha(b)for n,b in outputs.items()},'source_counts':counts,'new_semantic_and_seed_effective':sum(counts['lean/'+n+'.lean']['effective']for n in ['Hf4DirectDagSemantics','Hf4DirectDagSeedSoundness']),'all_Lean_execution_pending':True,'domain_note':'direct_model arbitrary m,h; original_compact_model requires existing cell h>=0 and m-h>=1; no new accuracy/precision premise','no_old381_imports_in_new_modules':not any('import Hf4QuadCompactDag'in s or'import Hf4QuadSharedCertificates'in s or'import Hf4CheckedDagProgram'in s or'import Hf4CheckedDagSemantics'in s for s in new.values())}
 assert manifest['no_old381_imports_in_new_modules']
 assert numeric['checked_and_inverse_canonical_sha256']==manifest['canonical_fields_sha256']
 outputs['manifest.json']=(json.dumps(manifest,indent=2)+'\n').encode()
 return outputs

def main():
 p=argparse.ArgumentParser();p.add_argument('--out',type=Path,default=HERE);p.add_argument('--check',action='store_true');a=p.parse_args();outputs=generate()
 if a.check:assert {str(p.relative_to(a.out))for p in (a.out/'lean').glob('*.lean')}=={n for n in outputs if n.endswith('.lean')}
 for n,b in outputs.items():
  p=a.out/n
  if a.check:assert p.read_bytes()==b,('reproduction mismatch',n)
  else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 print(json.dumps({'status':'REPRODUCTION_PASS'if a.check else'COMPLETE_SOURCE_DRAFT_UNCOMPILED','files':len(outputs)}))
if __name__=='__main__':main()
