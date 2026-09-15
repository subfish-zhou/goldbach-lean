import MathlibNt.Wu2008DoubleSieve.FourSeventhsConsumer
import MathlibNt.Wu2008DoubleSieve.FourSeventhsElementaryCap
import MathlibNt.Wu2008DoubleSieve.ActualMatrixInverseConsumer

/-! The actual nonnegative inverse consumes the global elementary cap, with no cutoff. -/
namespace Wu2008DoubleSieve.SecondFunctionalFourSevenths
open MotherPair FourthRowPhiOmega2 SecondFunctionalPositive ActualMatrixInverse

noncomputable def elementaryAnalyticCost (p : SecondFunctionalParameters) (δ : ℝ) : ℝ :=
  4 * wuUpperCoefficient p.S + wuUpperCoefficient p.kappa1 +
    SecondFunctionalCoupledFeedback.classical p + (2/(1-2*δ)) *
      (omega3XIntegralEnvelope p.kappa3 p.kappa1 + elementaryCap p)

noncomputable def elementaryAnalyticSource (p : SecondFunctionalParameters) (δ : ℝ) : ℝ :=
  wuUpperCoefficient p.s +
    (4 * wuImprovementLimit true δ p.S + wuImprovementLimit true δ p.kappa1 +
      J δ p.s p.S + J δ p.kappa2 p.S + J δ p.kappa3 p.S - elementaryAnalyticCost p δ)/5

theorem analyticSource_eq_elementary (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (δ : ℝ) :
    analyticSource p δ = elementaryAnalyticSource p δ := by
  unfold analyticSource analyticCost elementaryAnalyticSource elementaryAnalyticCost
  rw [analyticCap_eq_elementary p hp hs]

/-- All original rows, their true tail, and the actual Q are supplied internally. -/
theorem actual_elementary_global_with_tail {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    Q.mulVec ((fun i => elementaryAnalyticSource (parameters i) δ) + literalTail δ) ≤
      actualVector δ := by
  apply solve_actual_rows
  have h := original_matrix_rows_with_tail hδ hδhi
  have he (i : Fin 4) := analyticSource_eq_elementary (parameters i)
    (original_mother i) (original_s_ge_two i) δ
  simpa only [he, add_assoc] using h

/-- No compact cutoff or factorial depth is needed for this global-envelope branch. -/
theorem actual_elementary_global {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    Q.mulVec (fun i => elementaryAnalyticSource (parameters i) δ) ≤ actualVector δ :=
  (Q_mulVec_mono (le_add_of_nonneg_right (literalTail_nonnegative hδ hδhi))).trans
    (actual_elementary_global_with_tail hδ hδhi)

end Wu2008DoubleSieve.SecondFunctionalFourSevenths
