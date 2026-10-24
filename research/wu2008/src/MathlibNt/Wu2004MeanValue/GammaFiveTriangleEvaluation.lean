import MathlibNt.Wu2004MeanValue.GammaFiveTriangleLog
import Mathlib.Tactic.Tauto

/-! Exact logarithmic evaluation of both literal Gamma₅ triangle integrals. -/
namespace Wu2004MeanValue.GammaFiveLossBudget
open Real Set MeasureTheory
open scoped Classical Interval

/-- The transported section integral evaluates to the full or legal logarithmic kernel. -/
theorem triangle_masked_log {S B : ℝ} (hS : 0 < S) (hB : B < 1/2)
    (legal : Bool) (H : ℝ → ℝ) (v : ℝ) :
    (∫ t : ℝ, triangleMasked S B legal H v t) =
      H v * (1/(v*(1-v/S))) *
        (if legal then legalSectionLog S B v else fullSectionLog S B v) := by
  let L := max (1/S) (max (1-v/S-B) (1-v/S-1/2))
  let U := if legal then min B (min (1-v/S-1/S) (min ((1-v/S)/2) (v/S)))
    else min B (min (1-v/S-1/S) ((1-v/S)/2))
  have hsec (t : ℝ) : triangleSection S B legal v t ↔ L ≤ t ∧ t ≤ U := by
    rw [triangle_section_endpoints hB.le]
    cases legal <;> dsimp [L,U] <;> simp only [le_min_iff, Bool.false_eq_true,
      false_implies, and_true, true_implies]
    tauto
  have hL : 0 < L := (one_div_pos.mpr hS).trans_le (le_max_left _ _)
  have hU : U < 1-v/S := by
    have hb : U ≤ 1-v/S-1/S := by
      cases legal <;> exact (min_le_right _ _).trans (min_le_left _ _)
    have ha := one_div_pos.mpr hS
    linarith
  calc
    _ = H v * ∫ t : ℝ, if L ≤ t ∧ t ≤ U then 1/(v*t*(1-v/S-t)) else 0 := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      dsimp only
      simp only [triangleMasked, hsec]
      split_ifs <;> simp [div_eq_mul_inv]
    _ = H v * ((1/(v*(1-v/S)))*sectionLog (1-v/S) L U) := by
      rw [masked_section_integral hL hU]
    _ = _ := by
      rw [← mul_assoc]
      cases legal <;> rfl

/-- The original full or legal nested integral equals its logarithmic feedback integral. -/
theorem triangle_literal_log {S B : ℝ} (hS : 0 < S) (hB : B < 1/2)
    (hAB : 1/S ≤ B) (hleft : 1 ≤ S*(1-2*B)) (hright : S ≤ 5)
    (legal : Bool) {H : ℝ → ℝ} (hm : Measurable H) (hb : ∀ v, |H v| ≤ 1) :
    (∫ t in (1/S)..B, ∫ u in t..B,
      if legal = true → 2*u ≤ 1 ∧ u+2*t ≤ 1 then
        H (S*(1-t-u))/(t*u*(1-t-u)) else 0) =
      ∫ v in (1 : ℝ)..3, H v * (1/(v*(1-v/S))) *
        (if legal then legalSectionLog S B v else fullSectionLog S B v) := by
  rw [triangle_literal_transport hS hB hAB hleft hright legal hm hb]
  apply intervalIntegral.integral_congr
  intro v _
  exact triangle_masked_log hS hB legal H v

/-- Integrability of the explicit logarithmic feedback integrand follows from Fubini. -/
theorem triangle_log_integrable {S B : ℝ} (hS : 0 < S) (hB : B < 1/2)
    (legal : Bool) {H : ℝ → ℝ} (hm : Measurable H) (hb : ∀ v, |H v| ≤ 1) :
    Integrable (fun v => H v * (1/(v*(1-v/S))) *
      (if legal then legalSectionLog S B v else fullSectionLog S B v)) := by
  apply (triangle_masked_integrable hS hB legal hm hb).integral_prod_left.congr
  exact Filter.Eventually.of_forall (fun v => triangle_masked_log hS hB legal H v)

end Wu2004MeanValue.GammaFiveLossBudget
