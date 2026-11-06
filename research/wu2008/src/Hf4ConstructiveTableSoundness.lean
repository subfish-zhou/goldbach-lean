import Hf4ConstructiveTableData
import Hf4ConstructiveOriginalSoundness
import Hf4QuadCompactIntegral

/-! UNCOMPILED generic enclosure transfer: no final-record equality is needed. -/
noncomputable section
namespace Hf4Quad.ConstructiveDag.DirectTable
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
    Direct.original_compact_model (midpoint i) halfwidth hh.le ha hs.1
  apply endpoint_certificate_bounds hh ha hb hm
  · simpa only [mass_factor] using he.1
  · simpa only [mass_factor] using he.2

end Hf4Quad.ConstructiveDag.DirectTable
#print axioms Hf4Quad.ConstructiveDag.DirectTable.mass_bounds
