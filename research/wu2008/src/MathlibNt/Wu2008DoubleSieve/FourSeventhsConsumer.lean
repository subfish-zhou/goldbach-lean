import MathlibNt.Wu2008DoubleSieve.FourSeventhsKernel

namespace Wu2008DoubleSieve.SecondFunctionalFourSevenths
open Real MotherPair FourthRowPhiOmega2 SecondFunctionalPositive

/-- The original cost with only its common-phi joint supremum replaced by the proved cap. -/
noncomputable def analyticCost (p : SecondFunctionalParameters) (δ : ℝ) : ℝ :=
  4 * wuUpperCoefficient p.S + wuUpperCoefficient p.kappa1 +
    SecondFunctionalCoupledFeedback.classical p + (2/(1-2*δ)) *
      (omega3XIntegralEnvelope p.kappa3 p.kappa1 + analyticCap p)

theorem original_cost_le (i : Fin 4) {δ : ℝ} (hδhi : δ ≤ 1/10) :
    SecondFunctionalCoupledFeedback.cost (parameters i) δ ≤ analyticCost (parameters i) δ := by
  have hpay := mul_le_mul_of_nonneg_left (original_jointSup_bound i)
    (show 0 ≤ 2/(1-2*δ) by apply div_nonneg (by norm_num); linarith)
  unfold SecondFunctionalCoupledFeedback.cost analyticCost
  linarith only [hpay]

/-- The proved cap reaches the actual H-limit consumer with the original full gain. -/
theorem original_actual_limit (i : Fin 4) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    wuUpperCoefficient (parameters i).s +
      (SecondFunctionalCoupledFeedback.gain (parameters i) δ - analyticCost (parameters i) δ)/5 ≤
      wuImprovementLimit true δ (parameters i).s := by
  have h := SecondFunctionalCoupledFeedback.actual_limit (parameters i) (parameters_analytic i) hδ hδhi
  have hc := original_cost_le i hδhi
  linarith only [h, hc]

/-- All point gains, all three J integrals, and the original classical term are retained. -/
noncomputable def analyticSource (p : SecondFunctionalParameters) (δ : ℝ) : ℝ :=
  wuUpperCoefficient p.s +
    (4 * wuImprovementLimit true δ p.S + wuImprovementLimit true δ p.kappa1 +
      J δ p.s p.S + J δ p.kappa2 p.S + J δ p.kappa3 p.S - analyticCost p δ)/5

theorem analyticSource_le_original (i : Fin 4) {δ : ℝ} (hδhi : δ ≤ 1/10) :
    analyticSource (parameters i) δ ≤ SecondFunctionalPositive.source (parameters i) δ := by
  have hc := original_cost_le i hδhi
  unfold analyticSource SecondFunctionalPositive.source
  linarith only [hc]

/-- The actual four-row inequality keeps its original nonnegative tail vector. -/
theorem original_matrix_rows_with_tail {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    matrix.mulVec (actualVector δ) + (fun i => analyticSource (parameters i) δ) +
      literalTail δ ≤ actualVector δ := by
  intro i
  have hr := matrix_rows_with_tail hδ hδhi i
  have hs := analyticSource_le_original i hδhi
  change matrix.mulVec (actualVector δ) i + analyticSource (parameters i) δ +
    literalTail δ i ≤ actualVector δ i
  change matrix.mulVec (actualVector δ) i + SecondFunctionalPositive.source (parameters i) δ +
    literalTail δ i ≤ actualVector δ i at hr
  linarith only [hr, hs]

end Wu2008DoubleSieve.SecondFunctionalFourSevenths
