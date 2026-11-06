#!/usr/bin/env python3
"""Separate direct371 candidate. Python exact generation only; never runs Lean."""
from pathlib import Path
from fractions import Fraction as F
import argparse,hashlib,importlib.util,json,collections
HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]/'lib/legacy_hf4.py'
BASE_SHA='9c22e28b7566d7f686ec3d3da85c3f2d5fd4a669d965b5682e1c87c6c532ad7a'
ALGEBRA_SHA='5648745f7d4abea030b74c1be8ec1aab5cf9842e08ca514c5a819bfa3d435bb5'
sha=lambda b:hashlib.sha256(b).hexdigest()
assert sha(BASE.read_bytes())==BASE_SHA
spec=importlib.util.spec_from_file_location('hf',BASE);hf=importlib.util.module_from_spec(spec);spec.loader.exec_module(hf)

def direct_nodes():
 g=hf.Graph();t=g.make('var');r=g.make('rad')
 def lo(z):return 2*z*(525+z*(1050+z*(385+z*(-280+z*(-140+z**2*(12-2*z))))))/(105*(1+z)**2*(5-3*z**2))
 def up(z):return 2*z*(105+z*(105+z*(-70+z*(-70+z*(-14+z*(-14-6*z))))))/(105*(1-z)*(1+z)**2)
 def pair(k):
  if k==0:n=t-1;l=t+11;q=3*(t+3)
  elif k==1:n=t*(t-1);l=t**2+23*t+24;q=3*(t**2+7*t+8)
  elif k==2:
   N=(t**2+18*t+21)*(t+2)**2;D=90*(t+1)**2;n=N-D;l=N+3*D;q=3*N+D
  else:n=r*(t-1);a=10*(t+3);l=a-n;q=a+n
  fun=up if k==0 else lo
  return fun(n/l)+fun(n/q)
 joint=F(32,35)-F(184,105)*t-F(1144,945)*t**2-F(5261,540)*t**3+F(176,63)*t**4+F(1759,270)*t**5+F(2122,945)*t**6+F(299,1260)*t**7
 final=(-(2145*t**2+4418*t+2280)/(210*(t+1)**2))*pair(0)/t+(64*(10*t**4+18*t**3-t**2-6*t+3)/(945*t**4))*pair(1)/t+(250*(-5*t**2+21*t+26)/(189*(-t**2+6*t+6)))*pair(2)/t+(250*(-11*t**2+97*t+108)/(189*r*(-t**2+6*t+6)))*pair(3)/t+joint/(t**4*(t+1)*(t+3)**3)
 assert final.n==370 and len(g.nodes)==371
 return g.nodes

KERNEL='''import Hf4DirectCoordinates

/-! UNCOMPILED direct371 kernel bridge. The coordinate lemmas in its imported
module passed root's strict algebra02 trial; this bridge has not yet run. -/
noncomputable section
namespace Hf4Quad

def directUpper (t : ℝ) : ℝ :=
  upZ ((t-1)/(t+11))+upZ ((t-1)/(3*(t+3)))

def directNegative (t : ℝ) : ℝ :=
  lowZ (t*(t-1)/(t^2+23*t+24))+lowZ (t*(t-1)/(3*(t^2+7*t+8)))

def directQuadratic (t : ℝ) : ℝ :=
  let n := (t^2+18*t+21)*(t+2)^2
  let d := 90*(t+1)^2
  lowZ ((n-d)/(n+3*d))+lowZ ((n-d)/(3*n+d))

def directRadical (t : ℝ) : ℝ :=
  let n := TerminalE.radical*(t-1)
  let a := 10*(t+3)
  lowZ (n/(a-n))+lowZ (n/(a+n))

def directKernel (t : ℝ) : ℝ :=
  (-(2145*t^2+4418*t+2280)/(210*(t+1)^2))*directUpper t/t+
  (64*(10*t^4+18*t^3-t^2-6*t+3)/(945*t^4))*directNegative t/t+
  (250*(-5*t^2+21*t+26)/(189*(-t^2+6*t+6)))*directQuadratic t/t+
  (250*(-11*t^2+97*t+108)/(189*TerminalE.radical*(-t^2+6*t+6)))*directRadical t/t+
  SigmaRationalOuterFTC.jointNum t/SigmaRationalOuterFTC.jointDen t

theorem compactKernel_eq_directKernel {t : ℝ} (ht : 1 ≤ t) :
    compactKernel t = directKernel t := by
  have h0 := DirectCoordinates.zero_coordinates t
  have h1 := DirectCoordinates.negative_coordinates ht
  have hq := DirectCoordinates.quotient_coordinates
    (n := (t^2+18*t+21)*(t+2)^2) (DirectCoordinates.quadratic_den_ne ht)
  have hr := DirectCoordinates.conjugate_coordinates
    (a := 5*(t+3)) (b := TerminalE.radical*(t-1)) (DirectCoordinates.radical_den_ne ht)
  have ha : 2*(5*(t+3)) = (10:ℝ)*(t+3) := by ring
  simp only [ha] at hr
  simp only [compactKernel, directKernel, directUpper, directNegative,
    directQuadratic, directRadical, slCompact, suCompact,
    h0.1, h0.2, h1.1, h1.2, hq.1, hq.2,
    DirectCoordinates.radical_argument t, hr.1, hr.2]

end Hf4Quad
#print axioms Hf4Quad.compactKernel_eq_directKernel
'''

def dag_text(nodes):
 s='import Hf4DirectKernel\n\n/-! UNCOMPILED generated direct371 DAG, separate from original CompactDag. -/\nnoncomputable section\nnamespace Hf4Quad.DirectDag\n'
 for j,(op,*args) in enumerate(nodes):
  if op=='var':rhs='t'
  elif op=='rad':rhs='TerminalE.radical'
  elif op=='const':rhs=hf.lean(args[0])
  elif op=='neg':rhs=f'-f{args[0]} t'
  elif op=='inv':rhs=f'(f{args[0]} t)⁻¹'
  else:rhs=f'f{args[0]} t'+('+' if op=='add' else '*')+f'f{args[1]} t'
  s+=f'def f{j} ({"_" if op in ["rad","const"] else "t"} : ℝ) : ℝ := {rhs}\n'
 ds=','.join(f'f{j}' for j in reversed(range(len(nodes))))
 s+='\ntheorem direct_kernel_dag (t : ℝ) : directKernel t = f370 t := by\n'
 s+='  simp only [directKernel,directUpper,directNegative,directQuadratic,directRadical,lowZ,upZ,SigmaRationalOuterFTC.jointNum,SigmaRationalOuterFTC.jointDen,'+ds+',div_eq_mul_inv,sub_eq_add_neg,pow_succ,pow_zero,one_mul]\n\nend Hf4Quad.DirectDag\n'
 return s

def layout(nodes,models):
 shared=set();derived=set();scales={}
 for j,(op,*args) in enumerate(nodes):
  if op in ['rad','const'] or (op not in ['rad','const','var'] and all(a in shared for a in args)):shared.add(j)
  if op=='neg':derived.add(j)
  if op=='add' and all(models[i][j]==([x+y for x,y in zip(models[i][args[0]][0],models[i][args[1]][0])],models[i][args[0]][1]+models[i][args[1]][1]) for i in range(40)):derived.add(j)
  if op=='mul' and j not in shared:
   for scalar,parent in [args,args[::-1]]:
    if nodes[scalar][0]!='const':continue
    k=nodes[scalar][1]
    if k!=0 and all(models[i][j]==([k*x for x in models[i][parent][0]],abs(k)*models[i][parent][1]) for i in range(40)):scales[j]=(k,parent);break
 plan=[];literals=[]
 for j,(op,*args) in enumerate(nodes):
  offset=lambda a:j-1-a
  if j in shared:step=['shared',j]
  elif op=='var':step=['variable']
  elif j in scales:k,parent=scales[j];step=['scale',str(k),offset(parent)]
  elif j in derived:step=['neg',offset(args[0])] if op=='neg' else ['addExact',offset(args[0]),offset(args[1])]
  else:literals.append(j);step=[op,len(literals)-1,*map(offset,args)]
  plan.append(step)
 assert len(shared)==47 and len(literals)==145
 return shared,derived,scales,plan,literals

def record(model):
 p,e=model
 return '⟨'+','.join(hf.lean(x) for x in [*p,e])+'⟩'

def program_text(plan,seeds):
 s='import Hf4CheckedDagData\n\n/-! UNCOMPILED separate direct371 plan. All references use backward offsets. -/\nnamespace Hf4Quad.CheckedDag.DirectProgram\n\ndef plan : List Step := [\n'
 for step in plan:s+='  .'+step[0]+(' '+' '.join('('+hf.lean(F(x))+')' if step[0]=='scale' and k==0 else str(x) for k,x in enumerate(step[1:])) if len(step)>1 else '')+',\n'
 s=s[:-2]+'\n]\n\ndef seeds : ℕ → RationalModel.Certificate\n'
 for j,m in sorted(seeds.items()):s+=f'  | {j} => {record(m)}\n'
 return s+'  | _ => zero\n\nend Hf4Quad.CheckedDag.DirectProgram\n'

def panel_text(models,literals):
 s='import Hf4DirectDagProgram\n\n/-! UNCOMPILED new direct371 certificates, fixed original D=10^14. -/\nnamespace Hf4Quad.CheckedDag.DirectPanel0\nopen DirectProgram\n\ndef literals : ℕ → RationalModel.Certificate\n'
 for slot,j in enumerate(literals):s+=f'  | {slot} => {record(models[0][j])}\n'
 return s+'''  | _ => zero

def midpoint : ℚ := 41/40
def halfwidth : ℚ := 1/40

def rangeCheck (start width : ℕ) : Bool :=
  checkRange plan seeds literals midpoint halfwidth start width

def finalCertificate : RationalModel.Certificate :=
  getCert (run seeds literals midpoint halfwidth plan []) 0

end Hf4Quad.CheckedDag.DirectPanel0
'''

def checks_text(width):
 s='import Hf4DirectDagPanel0Data\n\n/-! UNCOMPILED new direct371 arithmetic checks. -/\nnamespace Hf4Quad.CheckedDag.DirectPanel0\n'
 for k,start in enumerate(range(0,371,width)):
  s+=f'\nset_option maxHeartbeats 4000000 in\nset_option maxRecDepth 30000 in\ntheorem checked{width}_{k:02} : rangeCheck {start} {min(width,371-start)} = true := by\n  decide +kernel\n'
 return s+'\nend Hf4Quad.CheckedDag.DirectPanel0\n'

def generate():
 algebra=(HERE/'inputs/Hf4DirectCoordinates.lean').read_bytes();assert sha(algebra)==ALGEBRA_SHA
 nodes=direct_nodes();models=[hf.evaluate(nodes,i) for i in range(40)];shared,derived,scales,plan,literals=layout(nodes,models)
 bounds=[]
 for i,model in enumerate(models):
  p,e=model[-1];lo,up=(p[0]+p[2]/3-e)/20,(p[0]+p[2]/3+e)/20;tl,tu=map(F,hf.TARGETS[i]);assert tl<=lo<=up<=tu
  bounds.append({'panel':i,'original_target':hf.TARGETS[i],'new_lower':str(lo),'new_upper':str(up),'final_record':[str(x) for x in p+[e]]})
 flat=[[i,j,k,str(x)]for i,m in enumerate(models)for j,(p,e) in enumerate(m)for k,x in enumerate(p+[e])]
 outputs={'lean/Hf4DirectCoordinates.lean':algebra,'lean/Hf4DirectKernel.lean':KERNEL.encode(),'lean/Hf4DirectDag.lean':dag_text(nodes).encode(),'lean/Hf4DirectDagProgram.lean':program_text(plan,{j:models[0][j]for j in shared}).encode(),'lean/Hf4DirectDagPanel0Data.lean':panel_text(models,literals).encode(),'lean/Hf4DirectDagPanel0Checks32.lean':checks_text(32).encode()}
 data={'common-plan.json':plan,'all40-payloads.json':[[[str(x)for x in models[i][j][0]+[models[i][j][1]]]for j in literals]for i in range(40)],'all40-bounds.json':bounds,'exact-fields.json':flat}
 outputs.update({n:(json.dumps(v,indent=2)+'\n').encode()for n,v in data.items()})
 manifest={'status':'GENERATED_NEW_MATH_BRIDGE_UNCOMPILED_NOT_ACCEPTED','producer_sha256':sha(Path(__file__).read_bytes()),'base_generator_sha256':BASE_SHA,'strictly_compiled_coordinate_source_sha256':ALGEBRA_SHA,'precision_denominator':hf.D,'nodes':371,'panels':40,'fields':len(flat),'field_canonical_sha256':sha(json.dumps(flat,separators=(',',':')).encode()),'shared':len(shared),'nonshared_exact':len(derived-shared),'scales':len(scales),'rounded_records_per_panel':len(literals),'rounded_op_counts':dict(collections.Counter(nodes[j][0]for j in literals)),'all40_original_targets_pass':True,'new_rational_records_differ_from_original':True,'files':{n:sha(b)for n,b in outputs.items()},'pending':['strict compactKernel→directKernel bridge compilation','strict directKernel→f370 DAG compilation','new371 semantic/seed soundness','all40 arithmetic and unchanged endpoint statements','full downstream/kernel/axiom/generator acceptance']}
 outputs['manifest.json']=(json.dumps(manifest,indent=2)+'\n').encode()
 return outputs

def main():
 p=argparse.ArgumentParser();p.add_argument('--out',type=Path,default=HERE);p.add_argument('--check',action='store_true');a=p.parse_args();outputs=generate()
 for n,b in outputs.items():
  target=a.out/n
  if a.check:assert target.read_bytes()==b,('producer mismatch',n)
  else:target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(b)
 print(json.dumps({'status':'REPRODUCTION_PASS'if a.check else'GENERATED_UNCOMPILED','files':len(outputs),'out':str(a.out)}))
if __name__=='__main__':main()
