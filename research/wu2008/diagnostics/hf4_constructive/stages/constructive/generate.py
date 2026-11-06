#!/usr/bin/env python3
"""Fully constructive direct371 source alternative; never runs Lean/adoption."""
from pathlib import Path
from fractions import Fraction as F
import argparse,copy,hashlib,importlib.util,json,re
HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'complete'
BASE_SHA='2c796866096a67b8d39546e4cbe54e2216edbd3f9506376bb176d222a9cef7bf'
TABLE=HERE.parent/'table'
TABLE_SHA='cab0794742247c604066913cf3df23898a4f97a21acc1dac1b695a2a41d9cb58'
sha=lambda b:hashlib.sha256(b).hexdigest()
def load_bound(root,digest):
 b=(root/'manifest.json').read_bytes();assert sha(b)==digest;return json.loads(b)
def read(root,j,n):
 b=root[n];assert sha(b)==j['files'][n],n;return b.decode()
def change_ns(s):return s.replace('Hf4Quad.InverseDag','Hf4Quad.ConstructiveDag').replace('InverseDag.DirectTable','ConstructiveDag.DirectTable')

def data_text(source):
 s=change_ns(source).replace('seeds literals','seeds').replace('(literals : ℕ → Certificate) ','').replace('checkStep literals','checkStep')
 old='| .inv k _ => literals k';assert old in s;s=s.replace(old,'| .inv _ a => Construction.constructInv (getCert cs a)')
 old='| .inv k a => decide (invCondition (getCert cs a) (literals k))';assert old in s;s=s.replace(old,'| .inv _ a => decide (0 < lower (getCert cs a))')
 s=re.sub(r'/\-!.*?\-/', '/-! UNCOMPILED full constructor: add, mul and inv all compute their original\nD=10^14 rounded records. Only positive-lower inverse guards are checked.\nNo literal-certificate function, payload parameter or inverse records. -/',s,count=1,flags=re.S)
 s=s.replace('/-- Independent chunk verification reconstructs the prefix but does not recheck\nits arithmetic conditions. No single closed decision spans all381 nodes. -/', '/-- Optional bounded-range interface retained for resource fallback. -/')
 assert 'literals'not in s
 return s

def sound_text(source):
 s=change_ns(source).replace('import Hf4InverseDagData','import Hf4ConstructiveDagData').replace('seeds literals','seeds').replace('checkStep literals','checkStep')
 old='| inv k a => exact (env a).inv (of_decide_eq_true ok)';assert old in s
 s=s.replace(old,'| inv k a => exact (env a).inv (Construction.inv_condition _ (of_decide_eq_true ok))')
 s=re.sub(r'/\-!.*?\-/', '/-! UNCOMPILED full-constructor soundness. The old positive lower bound\nis the only checked inverse premise; inv_condition proves the full enclosure. -/',s,count=1,flags=re.S)
 assert 'literals'not in s
 return s

def original_text(source):
 s=change_ns(source).replace('Hf4InverseDagSoundness','Hf4ConstructiveDagSoundness')
 s=s.replace('(literals : ℕ → Certificate) ','').replace('DirectProgram.seeds literals','DirectProgram.seeds').replace('direct_model literals m h','direct_model m h')
 assert 'literals'not in s
 return s

def table_data(source):
 s=change_ns(source).replace('Hf4InverseDagData','Hf4ConstructiveDagData')
 a=s.index('def literals');b=s.index('def lowerTarget');s=s[:a]+s[b:]
 assert s.count('(literals i)')==2;s=s.replace(' (literals i)','')
 s=s.replace('original40 cells/targets,22 inverse checkpoints per cell','original40 cells/targets, no inverse payloads')
 assert 'literals'not in s
 return s

def table_sound(source):
 s=change_ns(source).replace('Hf4DirectTableData','Hf4ConstructiveTableData').replace('Hf4DirectInverseOriginalSoundness','Hf4ConstructiveOriginalSoundness')
 assert s.count('Direct.original_compact_model (literals i)')==1
 s=s.replace('Direct.original_compact_model (literals i)','Direct.original_compact_model')
 return s

def reconstruction():
 spec=importlib.util.spec_from_file_location('original371',BASE/'generate.py');base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
 hf=base.hf;nodes=base.direct_nodes();models=[hf.evaluate(nodes,i)for i in range(40)];shared,derived,scales,plan,literals=base.layout(nodes,models)
 seeds={j:tuple(models[0][j][0]+[models[0][j][1]])for j in shared}
 payloads=[{plan[j][1]:tuple(m[j][0]+[m[j][1]])for j in range(371)if plan[j][0]=='inv'}for m in models]
 def nrm(p):return sum(map(abs,p[:4]))
 def lower(p):return abs(p[0])-sum(map(abs,p[1:4]))-p[4]
 def construct_inv(a):
  L=lower(a);assert L>0
  # Exactly Lean invCoefficients: all z0..z3 remain unrounded until the record.
  z0=1/a[0];z1=-(a[1]*z0)/a[0];z2=-(a[1]*z1+a[2]*z0)/a[0];z3=-(a[1]*z2+a[2]*z1+a[3]*z0)/a[0]
  p=list(map(hf.floor,[z0,z1,z2,z3]));e=hf.ceil((hf.err(a[:4],p,[F(1),F(0),F(0),F(0)])+sum(map(abs,p))*a[4])/L)
  return tuple(p)+(e,)
 def run(pp,dd,full):
  flat=[];guards=0;conditions=0;endpoints=[]
  for i,data in enumerate(dd):
   env=[]
   for j,step in enumerate(pp):
    kind,*args=step
    arities={'variable':0,'shared':1,'neg':1,'addExact':2,'scale':2,'mul':3,'add':3,'inv':2};assert kind in arities and len(args)==arities[kind]
    refs=args[1:]if kind in ['scale','add','mul','inv']else args if kind in ['neg','addExact']else[]
    assert all(type(a)is int and 0<=a<len(env)for a in refs)
    if kind=='variable':v=(F(41+2*i,40),F(1,40),F(0),F(0),F(0))
    elif kind=='shared':v=seeds[args[0]]
    elif kind=='neg':a=env[args[0]];v=tuple(-x for x in a[:4])+(a[4],)
    elif kind=='addExact':a,b=(env[x]for x in args);v=tuple(x+y for x,y in zip(a,b))
    elif kind=='scale':k=F(args[0]);a=env[args[1]];v=tuple(k*x for x in a[:4])+(abs(k)*a[4],)
    else:
     slot,*refs=args;a=env[refs[0]]
     if kind=='inv':
      assert lower(a)>0;guards+=1;v=construct_inv(a)if full else data[slot]
      assert hf.err(a[:4],v[:4],[F(1),F(0),F(0),F(0)])+nrm(v)*a[4]<=lower(a)*v[4]
     else:
      b=env[refs[1]]
      if kind=='add':p=list(map(hf.floor,(x+y for x,y in zip(a[:4],b[:4]))));e=hf.ceil(a[4]+b[4]+sum(abs(a[k]+b[k]-p[k])for k in range(4)));v=tuple(p)+(e,)
      else:p=list(map(hf.floor,hf.prod(a[:4],b[:4])[:4]));e=hf.ceil(a[4]*nrm(b)+b[4]*nrm(a)+a[4]*b[4]+hf.err(a[:4],b[:4],p));v=tuple(p)+(e,)
      if kind=='add':assert a[4]+b[4]+sum(abs(a[k]+b[k]-v[k])for k in range(4))<=v[4]
      else:assert a[4]*nrm(b)+b[4]*nrm(a)+a[4]*b[4]+hf.err(a[:4],b[:4],v[:4])<=v[4]
     conditions+=1
    assert v==tuple(models[i][j][0]+[models[i][j][1]]),(i,j)
    env.insert(0,v);flat.extend([i,j,k,str(x)]for k,x in enumerate(v))
   v=env[0];lo,up=(v[0]+v[2]/3-v[4])/20,(v[0]+v[2]/3+v[4])/20;L,U=map(F,hf.TARGETS[i]);assert L<=lo<=up<=U
   endpoints.append({'panel':i,'lower':str(lo),'upper':str(up),'original_targets':hf.TARGETS[i]})
  return sha(json.dumps(flat,separators=(',',':')).encode()),guards,conditions,endpoints
 checkpoint=run(plan,payloads,False);full=run(plan,[{}for _ in range(40)],True);assert full==checkpoint
 assert full[:3]==('e797b939f8cbb0a48f5c2b0e75853807de778b560a3a5d1fc75d3ef1eda0071f',880,5800)
 controls=[]
 for label,p in [('zero_lower',(F(0),)*5),('negative_lower',(F(1),F(2),F(0),F(0),F(0)))]:
  try:construct_inv(p)
  except AssertionError:controls.append(label)
  else:raise AssertionError('nonpositive guard accepted')
 for label in ['future_ref','negative_ref','unknown_operation','changed_checkpoint']:
  pp=copy.deepcopy(plan);dd=copy.deepcopy(payloads);ix=next(j for j,r in enumerate(pp)if r[0]=='inv')
  if label=='future_ref':pp[ix][-1]=ix
  elif label=='negative_ref':pp[ix][-1]=-1
  elif label=='unknown_operation':pp[0][0]='unknown'
  else:slot=pp[ix][1];dd[0][slot]=(dd[0][slot][0]+1,)+dd[0][slot][1:]
  try:run(pp,dd,label!='changed_checkpoint')
  except (AssertionError,KeyError,TypeError,ValueError):controls.append(label)
  else:raise AssertionError('negative control accepted '+label)
 return {'status':'EXACT_PYTHON_FULL_CONSTRUCTOR_AND_CHECKPOINT_PASS_NOT_LEAN','canonical_fields_sha256':full[0],'fields_each_route':74200,'inverse_positive_guards':full[1],'all_original_conditions_independently_verified':full[2],'stored_inverse_records_full_constructor':0,'stored_inverse_records_checkpoint_control':880,'rounding_D':hf.D,'all40_original_target_enclosures_retained':True,'negative_controls_rejected':controls,'all40_enclosures':full[3]}

def generate(base_outputs,table_outputs):
 BASE_SHA=sha(base_outputs['manifest.json']);TABLE_SHA=sha(table_outputs['manifest.json'])
 bj=json.loads(base_outputs['manifest.json']);tj=json.loads(table_outputs['manifest.json'])
 sources={
  'Hf4ConstructiveDagData.lean':data_text(read(base_outputs,bj,'lean/Hf4InverseDagData.lean')),
  'Hf4ConstructiveDagSoundness.lean':sound_text(read(base_outputs,bj,'lean/Hf4InverseDagSoundness.lean')),
  'Hf4ConstructiveOriginalSoundness.lean':original_text(read(base_outputs,bj,'lean/Hf4DirectInverseOriginalSoundness.lean')),
  'Hf4ConstructiveTableData.lean':table_data(read(table_outputs,tj,'lean/Hf4DirectTableData.lean')),
  'Hf4ConstructiveTableSoundness.lean':table_sound(read(table_outputs,tj,'lean/Hf4DirectTableSoundness.lean')),
  'Hf4ConstructiveTableChecks.lean':change_ns(read(table_outputs,tj,'lean/Hf4DirectTableChecks.lean')).replace('Hf4DirectTableData','Hf4ConstructiveTableData'),
  'Hf4ConstructiveTablePublic.lean':change_ns(read(table_outputs,tj,'lean/Hf4DirectTablePublic.lean')).replace('Hf4DirectTableChecks','Hf4ConstructiveTableChecks').replace('Hf4DirectTableSoundness','Hf4ConstructiveTableSoundness')}
 outputs={'lean/'+n:s.encode()for n,s in sources.items()}
 whole=change_ns(read(table_outputs,tj,'variants/whole/lean/Hf4DirectTableChecks.lean')).replace('Hf4DirectTableData','Hf4ConstructiveTableData')
 outputs['variants/whole/lean/Hf4ConstructiveTableChecks.lean']=whole.encode()
 for n in tj['original_source_sha256']:outputs['compatibility-facades/'+n]=b'import Hf4ConstructiveTablePublic\n'
 report=reconstruction();outputs['numeric-audit.json']=(json.dumps(report,indent=2)+'\n').encode()
 cp=HERE.parents[1]/'lib/source_counter.py';sp=importlib.util.spec_from_file_location('counter',cp);counter=importlib.util.module_from_spec(sp);sp.loader.exec_module(counter)
 counts={n:{'effective':sum(bool(l.strip())for l in counter.code_only(b.decode()).splitlines()),'physical':len(b.splitlines()),'bytes':len(b)}for n,b in outputs.items()if n.endswith('.lean')}
 manifest={'status':'FULL_CONSTRUCTOR_SOURCE_CANDIDATE_UNCOMPILED_NOT_ACCEPTED','producer_sha256':sha(Path(__file__).read_bytes()),'base_manifest_sha256':BASE_SHA,'table_manifest_sha256':TABLE_SHA,'input_source_sha256':{'complete/'+n:bj['files'][n]for n in ['lean/Hf4InverseDagData.lean','lean/Hf4InverseDagSoundness.lean','lean/Hf4DirectInverseOriginalSoundness.lean']},'input_table_sha256':{'table/'+n:h for n,h in tj['files'].items()if n.endswith('.lean')},'files':{n:sha(b)for n,b in outputs.items()},'source_counts':counts,'canonical_fields_sha256':report['canonical_fields_sha256'],'fields':74200,'positive_lower_checks_all40':880,'stored_inverse_records':0,'stored_inverse_payload_fields':0,'original_targets':80,'precision_denominator':10**14,'unchanged_dependencies':['Hf4DirectDagProgram','Hf4DirectDagSeedSoundness','Hf4CheckedDagSoundness','Hf4ConstructionConditions'],'condition_formula':'next.inv = Construction.constructInv; checkStep.inv = decide (0<lower p); soundness applies Construction.inv_condition','retained_controls':'checked-literal371, inverse-only371,2x2matrix and880-record endpoint table all untouched','no_Lean_execution':True,'resource_status':'UNMEASURED; full constructive expression may cost more than checkpoint route; no performance or savings acceptance claimed'}
 assert sha(base_outputs['manifest.json'])==BASE_SHA and sha(table_outputs['manifest.json'])==TABLE_SHA
 outputs['manifest.json']=(json.dumps(manifest,indent=2)+'\n').encode()
 return outputs

