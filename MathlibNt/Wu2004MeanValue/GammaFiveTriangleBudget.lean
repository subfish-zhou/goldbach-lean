import MathlibNt.Wu2004MeanValue.GammaFiveTriangleEvaluation
import MathlibNt.Wu2004MeanValue.GammaFiveSectionBudget

/-!
# Four-row loss bounds for the literal Gamma₅ triangles

The bounds here concern the original nested triangular integrals, including
both legal insertion gates. The normalization by five is explicit. To use
these in a count inequality, its improvement function and parameter row must
still be identified with the corresponding objects here.
-/

namespace Wu2004MeanValue.GammaFiveLossBudget
open Real Set MeasureTheory
open scoped Classical Interval

/-- Full (`false`) or legal (`true`) triangular gain with a given weight. -/
noncomputable def triangleGain (S B : ℝ) (legal : Bool) (H : ℝ → ℝ) : ℝ :=
  ∫ t in (1/S)..B, ∫ u in t..B,
    if legal = true → 2*u ≤ 1 ∧ u+2*t ≤ 1 then
      H (S*(1-t-u))/(t*u*(1-t-u)) else 0

/-- Only values on the actual triangle's ratio range affect the gain.
This permits replacing a clipped improvement function by the original one. -/
theorem triangleGain_congr_on {S B : ℝ} (hS : 0 < S) (hAB : 1/S ≤ B)
    (legal : Bool) {H K : ℝ → ℝ}
    (hHK : ∀ v ∈ Icc (S*(1-2*B)) (S-2), H v = K v) :
    triangleGain S B legal H = triangleGain S B legal K := by
  unfold triangleGain
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le hAB]
  intro t ht
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le ht.2]
  intro u hu
  have htS : 1 ≤ t*S := (div_le_iff₀ hS).mp ht.1
  have huS : 1 ≤ u*S := (div_le_iff₀ hS).mp (ht.1.trans hu.1)
  have htop := mul_nonneg hS.le (show 0 ≤ 2*B-t-u by linarith [hu.1,hu.2])
  have hv : S*(1-t-u) ∈ Icc (S*(1-2*B)) (S-2) :=
    ⟨by nlinarith,by nlinarith⟩
  dsimp only
  rw [hHK _ hv]

/-- Each original row pays the difference of the literal full and legal gains.
The weight is only assumed measurable and bounded between zero and one. -/
theorem original_row_triangle_gain_budget (i : Fin 4) (H : ℝ → ℝ)
    (hm : Measurable H) (hH : ∀ v, 0 ≤ H v ∧ H v ≤ 1) :
    triangleGain (rowParameters i).1 (rowParameters i).2 false H -
      triangleGain (rowParameters i).1 (rowParameters i).2 true H < 5*rowDebit i/2 := by
  have hp : 0 < (rowParameters i).1 ∧ (rowParameters i).2 < 1/2 ∧
      1/(rowParameters i).1 ≤ (rowParameters i).2 ∧
      1 ≤ (rowParameters i).1*(1-2*(rowParameters i).2) ∧ (rowParameters i).1 ≤ 5 := by
    fin_cases i <;> norm_num [rowParameters]
  have hb : ∀ v, |H v| ≤ 1 := fun v => by
    rw [abs_of_nonneg (hH v).1]
    exact (hH v).2
  have hfull := triangle_literal_log hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2 false hm hb
  have hlegal := triangle_literal_log hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2 true hm hb
  change triangleGain _ _ false H = _ at hfull
  change triangleGain _ _ true H = _ at hlegal
  rw [hfull,hlegal]
  have hi := (triangle_log_integrable hp.1 hp.2.1 true hm hb).intervalIntegrable
    (a := (1 : ℝ)) (b := 3)
  exact original_row_full_sub_legal_budget i H hm (fun v _ => hH v) hi

/-- The one-fifth normalization gives exactly the four improved row debits. -/
theorem original_row_normalized_triangle_loss (i : Fin 4) (H : ℝ → ℝ)
    (hm : Measurable H) (hH : ∀ v, 0 ≤ H v ∧ H v ≤ 1) :
    (triangleGain (rowParameters i).1 (rowParameters i).2 false H -
      triangleGain (rowParameters i).1 (rowParameters i).2 true H)/5 < rowDebit i/2 := by
  have h := original_row_triangle_gain_budget i H hm hH
  linarith

end Wu2004MeanValue.GammaFiveLossBudget
