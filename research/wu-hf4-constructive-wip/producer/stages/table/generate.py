#!/usr/bin/env python3
"""Separate all40 direct endpoint table source draft; no Lean or adoption."""
from pathlib import Path
from fractions import Fraction as F
import argparse,hashlib,importlib.util,json,re
HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'complete'
BASE_SHA='f3efec41d79cdaa2fbb886a0fa12c6dd403f8170e8259ee163abfa63cae65107'
FROZEN=HERE.parents[1]/'frozen'
sha=lambda b:hashlib.sha256(b).hexdigest()

SOUNDNESS='''import Hf4DirectTableData
import Hf4DirectInverseOriginalSoundness
import Hf4QuadCompactIntegral

/-! UNCOMPILED generic enclosure transfer: no final-record equality is needed. -/
noncomputable section
namespace Hf4Quad.InverseDag.DirectTable
open CheckedDag RationalModel

/-- Transfer two rational mass enclosures through the existing cubic integral
lemma. Only p.a,p.c,p.error matter; no named final-certificate field facts. -/
theorem endpoint_certificate_bounds {m h L U : ℚ} {p : Certificate}
    (hh : 0 < (h:ℝ)) (ha : 1 ≤ (m:ℝ)-(h:ℝ)) (hb : (m:ℝ)+(h:ℝ) ≤ 3)
    (hm : p.Valid (fun x => compactKernel ((m:ℝ)+(h:ℝ)*x)))
    (hL : L ≤ 2*h*(p.a+p.c/3-p.error))
    (hU : 2*h*(p.a+p.c/3+p.error) ≤ U) :
    (L:ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass ((m:ℝ)-(h:ℝ)) ((m:ℝ)+(h:ℝ)) ∧
    SigmaActualBlockSeparable.endpointCellMass ((m:ℝ)-(h:ℝ)) ((m:ℝ)+(h:ℝ)) ≤ (U:ℝ) := by
  have hh0 := endpoint_compact_model hh ha hb hm
  have hL' : (L:ℝ) ≤ 2*(h:ℝ)*((p.a:ℝ)+(p.c:ℝ)/3-(p.error:ℝ)) := by
    exact_mod_cast hL
  have hU' : 2*(h:ℝ)*((p.a:ℝ)+(p.c:ℝ)/3+(p.error:ℝ)) ≤ (U:ℝ) := by
    exact_mod_cast hU
  exact ⟨hL'.trans hh0.1, hh0.2.trans hU'⟩

theorem cell_domain (i : Fin 40) :
    0 < (halfwidth:ℝ) ∧ 1 ≤ (midpoint i:ℝ)-(halfwidth:ℝ) ∧
    (midpoint i:ℝ)+(halfwidth:ℝ) ≤ 3 := by
  have hiN : i.val ≤ 39 := by omega
  have hi : (i.val:ℚ) ≤ 39 := by exact_mod_cast hiN
  have hi0 : (0:ℚ) ≤ (i.val:ℚ) := Nat.cast_nonneg _
  have ha : (1:ℚ) ≤ midpoint i-halfwidth := by
    dsimp only [midpoint, halfwidth]
    linarith only [hi0]
  have hb : midpoint i+halfwidth ≤ (3:ℚ) := by
    dsimp only [midpoint, halfwidth]
    linarith only [hi]
  refine ⟨by norm_num [halfwidth], ?_, ?_⟩
  · exact_mod_cast ha
  · exact_mod_cast hb

theorem mass_factor (z : ℚ) : 2*halfwidth*z = z/20 := by
  unfold halfwidth
  ring

theorem mass_bounds (i : Fin 40) (ok : panelCheck i = true) :
    (lowerTarget i:ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass
      ((midpoint i:ℝ)-(halfwidth:ℝ)) ((midpoint i:ℝ)+(halfwidth:ℝ)) ∧
    SigmaActualBlockSeparable.endpointCellMass
      ((midpoint i:ℝ)-(halfwidth:ℝ)) ((midpoint i:ℝ)+(halfwidth:ℝ)) ≤ (upperTarget i:ℝ) := by
  have hs : arithmeticCheck i = true ∧ enclosureCheck i = true :=
    Bool.and_eq_true_iff.mp ok
  have he : lowerTarget i ≤ ((finalCertificate i).a+(finalCertificate i).c/3-(finalCertificate i).error)/20 ∧
      ((finalCertificate i).a+(finalCertificate i).c/3+(finalCertificate i).error)/20 ≤ upperTarget i :=
    of_decide_eq_true hs.2
  obtain ⟨hh, ha, hb⟩ := cell_domain i
  have hm : (finalCertificate i).Valid
      (fun x => compactKernel ((midpoint i:ℝ)+(halfwidth:ℝ)*x)) :=
    Direct.original_compact_model (literals i) (midpoint i) halfwidth hh.le ha hs.1
  apply endpoint_certificate_bounds hh ha hb hm
  · simpa only [mass_factor] using he.1
  · simpa only [mass_factor] using he.2

end Hf4Quad.InverseDag.DirectTable
#print axioms Hf4Quad.InverseDag.DirectTable.mass_bounds
'''

def checks_text(whole=False):
 s='import Hf4DirectTableData\n'+(''if whole else'import Mathlib.Tactic.FinCases\n')+'import Mathlib.Data.Fintype.Fin\n\n/-! UNCOMPILED arithmetic/enclosure decision experiment. -/\nset_option maxRecDepth 30000\nset_option maxHeartbeats 4000000\n\nnamespace Hf4Quad.InverseDag.DirectTable\n'
 if whole:s+='\ntheorem all_panels : ∀ i : Fin 40, panelCheck i = true := by\n  decide +kernel\n'
 else:
  for i in range(40):s+=f'\ntheorem panel_{i:02} : panelCheck ⟨{i}, by decide⟩ = true := by\n  decide +kernel\n'
  s+='\ntheorem all_panels (i : Fin 40) : panelCheck i = true := by\n  fin_cases i\n'
  for i in range(40):s+=f'  · exact panel_{i:02}\n'
 return s+'\nend Hf4Quad.InverseDag.DirectTable\n'

def generate(base_outputs):
 mb=base_outputs['manifest.json'];BASE_SHA=sha(mb);binding=json.loads(mb)
 read=lambda n:base_outputs[n]
 for n in ['common-plan.json','all40-payloads.json','all40-bounds.json','numeric-audit.json']:
  assert sha(read(n))==binding['files'][n],n
 plan=json.loads(read('common-plan.json'));payloads=json.loads(read('all40-payloads.json'));bounds=json.loads(read('all40-bounds.json'))
 inverse_slots=[row[1]for row in plan if row[0]=='inv'];assert len(inverse_slots)==22 and len(set(inverse_slots))==22
 source_files=['Hf4QuadPanel0.lean']+[f'Hf4QuadBatch{i}.lean'for i in range(13)]
 headers={int(k):v for k,v in json.loads((FROZEN/'original-headers.json').read_text()).items()}
 origin=json.loads((FROZEN/'header-origin.json').read_text());assert sha((FROZEN/'original-headers.json').read_bytes())==origin['header_json_sha256']
 assert set(headers)==set(range(40))
 q=lambda x:'('+str(F(x).numerator)+'/'+str(F(x).denominator)+')'if F(x).denominator!=1 else str(F(x).numerator)
 s='import Hf4DirectDagProgram\nimport Hf4InverseDagData\n\n/-! UNCOMPILED original40 cells/targets,22 inverse checkpoints per cell. -/\nnamespace Hf4Quad.InverseDag.DirectTable\nopen CheckedDag\nopen CheckedDag.DirectProgram\n\ndef literals (i : Fin 40) : ℕ → RationalModel.Certificate :=\n  match i.val with\n'
 for i,p in enumerate(payloads):
  s+=f'  | {i} => fun\n'
  for slot in inverse_slots:s+=f'    | {slot} => ⟨'+','.join(q(v)for v in p[slot])+'⟩\n'
  s+='    | _ => zero\n'
 s+='  | _ => fun _ => zero\n\n'
 for target,pos in [('lowerTarget',0),('upperTarget',1)]:
  s+=f'def {target} (i : Fin 40) : ℚ :=\n  match i.val with\n'
  for i,b in enumerate(bounds):s+=f'  | {i} => {q(b["original_target"][pos])}\n'
  s+='  | _ => 0\n\n'
 s+='''def midpoint (i : Fin 40) : ℚ := (41+2*(i.val:ℚ))/40
def halfwidth : ℚ := 1/40

def finalCertificate (i : Fin 40) : RationalModel.Certificate :=
  getCert (run seeds (literals i) (midpoint i) halfwidth plan []) 0

def arithmeticCheck (i : Fin 40) : Bool :=
  checked seeds (literals i) (midpoint i) halfwidth plan []

def enclosureCheck (i : Fin 40) : Bool :=
  let p := finalCertificate i
  decide (lowerTarget i ≤ (p.a+p.c/3-p.error)/20 ∧
    (p.a+p.c/3+p.error)/20 ≤ upperTarget i)

def panelCheck (i : Fin 40) : Bool := arithmeticCheck i && enclosureCheck i

end Hf4Quad.InverseDag.DirectTable
'''
 public='import Hf4DirectTableChecks\nimport Hf4DirectTableSoundness\n\n/-! UNCOMPILED40 compatibility wrappers with EXACT original written headers. -/\nnoncomputable section\n'
 for i in range(40):
  public+=f'\nnamespace Hf4Quad.Panel{i}\n\n'+headers[i]['header']+' := by\n'
  public+=f'  have hh := InverseDag.DirectTable.mass_bounds ⟨{i}, by decide⟩\n    (InverseDag.DirectTable.all_panels ⟨{i}, by decide⟩)\n'
  public+='  norm_num [InverseDag.DirectTable.lowerTarget, InverseDag.DirectTable.upperTarget,\n    InverseDag.DirectTable.midpoint, InverseDag.DirectTable.halfwidth] at hh\n  exact hh\n'
  public+=f'\nend Hf4Quad.Panel{i}\n'
 # Independent check of the rational endpoint formulas and all source headers.
 for i,b in enumerate(bounds):
  a,c,e=(F(b['final_record'][k])for k in [0,2,4]);lo,up=(a+c/3-e)/20,(a+c/3+e)/20;L,U=map(F,b['original_target']);assert L<=lo<=up<=U
  assert q(L).replace('(','').replace(')','')in headers[i]['header'];assert q(U).replace('(','').replace(')','')in headers[i]['header']
  assert F(41+2*i,40)-F(1,40)==1+F(i,20)
  assert F(41+2*i,40)+F(1,40)==1+F(i+1,20)
 outputs={'lean/Hf4DirectTableData.lean':s.encode(),'lean/Hf4DirectTableSoundness.lean':SOUNDNESS.encode(),'lean/Hf4DirectTableChecks.lean':checks_text().encode(),'lean/Hf4DirectTablePublic.lean':public.encode(),'variants/whole/lean/Hf4DirectTableChecks.lean':checks_text(True).encode()}
 facades={n:'import Hf4DirectTablePublic\n'for n in source_files}
 outputs.update({'compatibility-facades/'+n:s.encode()for n,s in facades.items()})
 outputs['original-headers.json']=(json.dumps(headers,indent=2)+'\n').encode()
 counterpath=HERE.parents[1]/'lib/source_counter.py';sp=importlib.util.spec_from_file_location('counter',counterpath);counter=importlib.util.module_from_spec(sp);sp.loader.exec_module(counter)
 def count(b):return {'effective':sum(bool(l.strip())for l in counter.code_only(b.decode()).splitlines()),'physical':len(b.splitlines()),'bytes':len(b)}
 counts={n:count(b)for n,b in outputs.items()if n.endswith('.lean')}
 manifest={'status':'GENERIC40_ENDPOINT_TABLE_UNCOMPILED_NOT_ACCEPTED','producer_sha256':sha(Path(__file__).read_bytes()),'base_manifest_sha256':BASE_SHA,'base_inputs_sha256':{n:binding['files'][n]for n in ['common-plan.json','all40-payloads.json','all40-bounds.json','numeric-audit.json']},'original_source_sha256':origin['preV5_original_source_sha256'],'files':{n:sha(b)for n,b in outputs.items()},'source_counts':counts,'canonical_fields_sha256':binding['canonical_fields_sha256'],'stored_inverse_records':880,'stored_inverse_fields':4400,'stored_original_targets':80,'all40_original_header_bytes_retained':True,'all40_rational_mass_enclosures_rechecked':True,'precision_denominator':10**14,'avoids_generating_for40panel_replication':['40 final-certificate literal copies','200 separate final-field equality facts','40 certificate cases/reconstruction proofs','40 separate analytic reconstructed_model proofs'],'comparison_basis':'Source draft obligations only; no current-project deletion or accepted savings claimed','retained_fallbacks':'Original complete371 and separate2x2 model-variants untouched; table full-check/whole-table resource behavior unmeasured','pending':['Lean generic Rat-to-Real enclosure proof','Lean forallFin40 domain proof','actual perpanel numeric resources/kernel checks','alternative wholeFin40 check resource benchmark','all40 exact external theorem type/kernel checks','full downstream/generator acceptance'],'no_Lean_execution':True}
 assert sha(base_outputs['manifest.json'])==BASE_SHA
 outputs['manifest.json']=(json.dumps(manifest,indent=2)+'\n').encode()
 return outputs

