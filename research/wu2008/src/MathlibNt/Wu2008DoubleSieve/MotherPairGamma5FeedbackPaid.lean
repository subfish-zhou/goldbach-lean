import MathlibNt.Wu2008DoubleSieve.MotherPairGamma5LossBudget
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalCoupledMother

/-! Full Gamma5 gain, with its proved debit, in the actual four-row feedback. -/
namespace Wu2008DoubleSieve.SecondFunctionalCoupled
open MotherPair Wu2004MeanValue.GammaFiveLossBudget

/-- Replace only the legal Gamma5 gain by the full triangle and pay its row debit. -/
noncomputable def gamma5PaidCoefficient (r : Fin 4) (δ : ℝ) : ℝ :=
  coefficient (gamma5OriginalRow r) δ + gainIntegral (gamma5OriginalRow r) .gammaFive δ -
    gamma5FullGain (gamma5OriginalRow r) δ + 5*rowDebit r/2

theorem coefficient_le_gamma5PaidCoefficient (r : Fin 4) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    coefficient (gamma5OriginalRow r) δ ≤ gamma5PaidCoefficient r δ := by
  have h := gamma5_original_row_full_sub_legal_lt r hδ hδhi
  unfold gamma5PaidCoefficient
  linarith only [h]

/-- The final-depth improvement bound retains all other original H/J terms. -/
theorem gamma5_paid_actual_limit (r : Fin 4) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    wuUpperCoefficient (gamma5OriginalRow r).s - gamma5PaidCoefficient r δ / 5 ≤
      wuImprovementLimit true δ (gamma5OriginalRow r).s := by
  have hp : AnalyticParameters (gamma5OriginalRow r) := by
    fin_cases r
    · exact row1_fullH.toAnalyticParameters
    · exact row2_fullH.toAnalyticParameters
    · exact row3_fullH.toAnalyticParameters
    · exact row4_fullH.toAnalyticParameters
  have h := feedback_le_limit (gamma5OriginalRow r) hp hδ hδhi
  have hpaid := coefficient_le_gamma5PaidCoefficient r hδ (by linarith)
  unfold feedback at h
  linarith only [h, hpaid]

end Wu2008DoubleSieve.SecondFunctionalCoupled
