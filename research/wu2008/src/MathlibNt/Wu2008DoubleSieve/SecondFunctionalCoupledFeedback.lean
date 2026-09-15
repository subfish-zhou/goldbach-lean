import MathlibNt.Wu2008DoubleSieve.SecondFunctionalCoupledRows
import MathlibNt.Wu2008DoubleSieve.MotherPairFeedbackMain

namespace Wu2008DoubleSieve.SecondFunctionalCoupledFeedback
open Real MeasureTheory MotherPair FourthRowPhiOmega2
open scoped Classical Interval

/-- The four legal feedback densities retain their original term multiplicities. -/
noncomputable def density (p : SecondFunctionalParameters) (v : ℝ) : ℝ :=
  feedbackLogKernel p .gammaFive v + feedbackLogKernel p .gammaSix v +
  feedbackLogKernel p .gammaSeven v + feedbackLogKernel p .gammaEight v

noncomputable def classical (p : SecondFunctionalParameters) : ℝ :=
  classicalIntegral p .gammaFive + classicalIntegral p .gammaSix +
  classicalIntegral p .gammaSeven + classicalIntegral p .gammaEight

theorem density_nonnegative (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (v : ℝ) : 0 ≤ density p v := by
  unfold density
  exact add_nonneg (add_nonneg (add_nonneg (feedback_log_nonnegative hp _ v)
    (feedback_log_nonnegative hp _ v)) (feedback_log_nonnegative hp _ v))
    (feedback_log_nonnegative hp _ v)

theorem four_gain_identity (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    fourIntegralUpper p δ = classical p -
      ∫ v in (1:ℝ)..3, wuImprovementLimit true δ v * density p v := by
  have h5 := feedback_log_actual_integrable hp Term.gammaFive hδ hδhi
  have h6 := feedback_log_actual_integrable hp Term.gammaSix hδ hδhi
  have h7 := feedback_log_actual_integrable hp Term.gammaSeven hδ hδhi
  have h8 := feedback_log_actual_integrable hp Term.gammaEight hδ hδhi
  unfold fourIntegralUpper classical density
  simp_rw [mul_add]
  rw [intervalIntegral.integral_add ((h5.add h6).add h7) h8,
    intervalIntegral.integral_add (h5.add h6) h7,
    intervalIntegral.integral_add h5 h6]
  rw [gainIntegral_feedbackLog hp .gammaFive hδ hδhi,
    gainIntegral_feedbackLog hp .gammaSix hδ hδhi,
    gainIntegral_feedbackLog hp .gammaSeven hδ hδhi,
    gainIntegral_feedbackLog hp .gammaEight hδ hδhi]
  ring

/-- Pure scalar cost; the phi-dependent terms were summed before their supremum. -/
noncomputable def cost (p : SecondFunctionalParameters) (δ : ℝ) : ℝ :=
  4 * wuUpperCoefficient p.S + wuUpperCoefficient p.kappa1 + classical p +
    (2/(1-2*δ)) *
      (omega3XIntegralEnvelope p.kappa3 p.kappa1 + SecondFunctionalCoupled.jointSup p)

/-- The actual H and J gains, not a supplied numerical lower bound. -/
noncomputable def gain (p : SecondFunctionalParameters) (δ : ℝ) : ℝ :=
  4 * wuImprovementLimit true δ p.S + wuImprovementLimit true δ p.kappa1 +
    J δ p.s p.S + J δ p.kappa2 p.S + J δ p.kappa3 p.S +
    ∫ v in (1:ℝ)..3, wuImprovementLimit true δ v * density p v

theorem coefficient_identity (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    SecondFunctionalCoupled.coefficient p δ = cost p δ - gain p δ := by
  unfold SecondFunctionalCoupled.coefficient cost gain
  rw [four_gain_identity p hp hδ hδhi]
  ring

/-- The actual original count now consumes both independent analytic producers. -/
theorem mother (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
          (cost p δ - gain p δ + ε) *
            boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  simpa only [coefficient_identity p hp hδ (show δ < 1/2 by linarith)] using
    SecondFunctionalCoupled.mother p hp k hk hδ hδhi hε

/-- General genuine feedback with one explicit legal density and no free envelope premise. -/
theorem actual_limit (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    wuUpperCoefficient p.s + (gain p δ - cost p δ)/5 ≤
      wuImprovementLimit true δ p.s := by
  have h := SecondFunctionalCoupled.feedback_le_limit p hp hδ hδhi
  unfold SecondFunctionalCoupled.feedback at h
  rw [coefficient_identity p hp hδ (by linarith)] at h
  linarith only [h]

end Wu2008DoubleSieve.SecondFunctionalCoupledFeedback
