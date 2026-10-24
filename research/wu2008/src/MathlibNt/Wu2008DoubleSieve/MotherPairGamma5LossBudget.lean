import MathlibNt.Wu2008DoubleSieve.MotherPairGainData
import MathlibNt.Wu2008DoubleSieve.Gamma5AllRowsLossBudget

/-! The four actual mother-pair Γ₅ gains, with explicit full-minus-legal debits. -/
namespace Wu2008DoubleSieve.MotherPair
open Real Set MeasureTheory SecondFunctionalParameters
open Wu2004MeanValue.GammaFiveLossBudget
open scoped Classical Interval

/-- The full Γ₅ triangle for the same parameter object as the mother count. -/
noncomputable def gamma5FullGain (p : SecondFunctionalParameters) (δ : ℝ) : ℝ :=
  ∫ t in (1/p.S)..(1/p.kappa2), ∫ u in t..(1/p.kappa2),
    wuImprovementLimit true δ (p.S*(1-t-u))/(t*u*(1-t-u))

theorem gamma5_full_gain_eq_triangle (p : SecondFunctionalParameters) (δ : ℝ) :
    gamma5FullGain p δ = triangleGain p.S (1/p.kappa2) false (wuImprovementLimit true δ) := by
  simp only [gamma5FullGain, triangleGain, Bool.false_eq_true, false_implies, if_true]

/-- The clipped inner endpoint in the original mother integral is exactly t
on its outer interval; the two insertion gates remain unchanged. -/
theorem gamma5_legal_gain_eq_triangle (p : SecondFunctionalParameters) (δ : ℝ)
    (hAB : 1/p.S ≤ 1/p.kappa2) :
    gainIntegral p .gammaFive δ =
      triangleGain p.S (1/p.kappa2) true (wuImprovementLimit true δ) := by
  unfold gainIntegral triangleGain
  simp only [upperP, lowerQ, upperQ]
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le hAB]
  intro t ht
  dsimp only
  rw [max_eq_right ht.1, min_eq_right ht.2]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  by_cases h : 2*u ≤ 1 ∧ u+2*t ≤ 1 <;> simp [gainLiteral, gamma5GainLegal, Hratio, h]

/-- Original row objects in the same order as the four scalar loss certificates. -/
noncomputable def gamma5OriginalRow : Fin 4 → SecondFunctionalParameters :=
  ![row1,row2,row3,row4]

theorem gamma5_original_row_parameters (i : Fin 4) :
    (gamma5OriginalRow i).S = (rowParameters i).1 ∧
      1/(gamma5OriginalRow i).kappa2 = (rowParameters i).2 := by
  fin_cases i <;> norm_num [gamma5OriginalRow, row1, row2, row3, row4, rowParameters]

/-- Paid full-gain replacement for the exact legal gain used in the mother count. -/
theorem gamma5_original_row_full_sub_legal_lt (i : Fin 4) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    gamma5FullGain (gamma5OriginalRow i) δ -
      gainIntegral (gamma5OriginalRow i) .gammaFive δ < 5*rowDebit i/2 := by
  have hp := gamma5_original_row_parameters i
  have hAB : 1/(gamma5OriginalRow i).S ≤ 1/(gamma5OriginalRow i).kappa2 := by
    rw [hp.1,hp.2]
    fin_cases i <;> norm_num [rowParameters]
  rw [gamma5_full_gain_eq_triangle, gamma5_legal_gain_eq_triangle _ _ hAB, hp.1,hp.2]
  exact gamma5_original_row_loss_lt i hδ hδhi

end Wu2008DoubleSieve.MotherPair
