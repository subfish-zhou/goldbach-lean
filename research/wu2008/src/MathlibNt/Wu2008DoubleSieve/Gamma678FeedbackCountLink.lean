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


end Wu2008DoubleSieve
