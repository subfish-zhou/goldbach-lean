import MathlibNt.Wu2008DoubleSieve.FourthRowJoinedGated
import MathlibNt.Wu2008DoubleSieve.Gamma78GainMain
import MathlibNt.Wu2008DoubleSieve.Gamma678FeedbackSupport

/-! The accepted explicit kernels are consumed by the actual count upper bounds.
Gamma7/8 remain their actual label counts, not yet the mother's prefix counts. -/
namespace Wu2008DoubleSieve
open scoped Interval

 theorem gamma678FeedbackCount_gain6 {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    gamma6GainIntegral δ = ∫ v in (1 : ℝ)..3,
      wuImprovementLimit true δ v * Gamma678Feedback.K6 v := by
  convert Gamma678Feedback.actual6_eq hδ hδhi using 1
  norm_num [gamma6GainIntegral, gamma6GainLiteral, gamma5GainV, gamma5MassA,
      gamma5ClassicalS, gamma6BaseB, gamma6BaseC, gamma6BaseF,
      Gamma678Feedback.a, Gamma678Feedback.b, Gamma678Feedback.c,
      Gamma678Feedback.f, Gamma678Feedback.S]

 theorem gamma678FeedbackCount_gain7 {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    gamma78GainIntegral true δ = ∫ v in (1 : ℝ)..3,
      wuImprovementLimit true δ v * Gamma678Feedback.K7 v := by
  rw [gamma78Gain_G7_literal]
  exact Gamma678Feedback.actual7_eq hδ hδhi

 theorem gamma678FeedbackCount_gain8 {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    gamma78GainIntegral false δ = ∫ v in (1 : ℝ)..3,
      wuImprovementLimit true δ v * Gamma678Feedback.K8 v := by
  rw [gamma78Gain_G8_literal]
  exact Gamma678Feedback.actual8_eq hδ hδhi

 theorem gamma678FeedbackCount_gain_sum {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    gamma6GainIntegral δ + gamma78GainIntegral true δ + gamma78GainIntegral false δ =
      ∫ v in (1 : ℝ)..3, wuImprovementLimit true δ v *
        (Gamma678Feedback.K6 v + Gamma678Feedback.K7 v + Gamma678Feedback.K8 v) := by
  rw [gamma678FeedbackCount_gain6 hδ hδhi, gamma678FeedbackCount_gain7 hδ hδhi,
    gamma678FeedbackCount_gain8 hδ hδhi]
  simp_rw [mul_add]
  rw [intervalIntegral.integral_add
      ((Gamma678Feedback.actual6_rhs_integrable hδ hδhi).add
        (Gamma678Feedback.actual7_rhs_integrable hδ hδhi))
      (Gamma678Feedback.actual8_rhs_integrable hδ hδhi),
    intervalIntegral.integral_add (Gamma678Feedback.actual6_rhs_integrable hδ hδhi)
      (Gamma678Feedback.actual7_rhs_integrable hδ hδhi)]

/-- One complete kernel sum, one total error, and the unchanged actual three counts. -/
theorem gamma678FeedbackCount_joint_upper (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        fourthRowMotherGamma6 N δ (convolutionWuWindows N Δ V) +
          gamma78GainCount N (convolutionWuWindows N Δ V)
            (gamma78GainLabels true N δ (convolutionWuWindows N Δ V)) +
          gamma78GainCount N (convolutionWuWindows N Δ V)
            (gamma78GainLabels false N δ (convolutionWuWindows N Δ V)) ≤
          (gamma6BaseC6 + gamma78GainC true + gamma78GainC false -
            (∫ v in (1 : ℝ)..3, wuImprovementLimit true δ v *
              (Gamma678Feedback.K6 v + Gamma678Feedback.K7 v + Gamma678Feedback.K8 v)) + ε) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hδhalf : δ < 1 / 2 := by linarith
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨T6, hT6, h6⟩ := fourthRowJoinedGamma6_actual_upper k hk hδ hδhi hε2
  obtain ⟨T78, _, h78⟩ := gamma78Gain_joint_full_count_upper k hk hδ hδhi hε2
  refine ⟨max T6 T78, hT6.trans (le_max_left _ _), ?_⟩
  intro N hN he i Δ V hb
  have h6N := h6 N ((le_max_left T6 T78).trans hN) he i Δ V hb
  have h78N := h78 N ((le_max_right T6 T78).trans hN) he i Δ V hb
  rw [← gamma678FeedbackCount_gain_sum hδ hδhalf]
  nlinarith only [h6N, h78N]

end Wu2008DoubleSieve
