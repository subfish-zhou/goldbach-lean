import MathlibNt.Wu2004MeanValue.GammaFiveLossBudgetTriangle
import MathlibNt.Wu2008DoubleSieve.Gamma5FeedbackMain

/-!
# A paid bound for the actual fourth-row Gamma₅ loss

The existing count estimate uses the legal gain. The missing full gain is
bounded here by 1/400 before the second functional's factor 1/5. This does
not remove the other inputs needed for the original Ξ₂ inequality.
-/

namespace Wu2008DoubleSieve
open Real Set MeasureTheory
open scoped Interval

/-- The scalar certificate uses exactly the existing fourth-row loss kernel. -/
theorem gamma5Feedback_loss_kernel_eq_budget :
    gamma5FeedbackLossKernel = Wu2004MeanValue.GammaFiveLossBudget.kernel := by
  funext v
  norm_num [gamma5FeedbackLossKernel, Wu2004MeanValue.GammaFiveLossBudget.kernel,
    gamma5FeedbackVm, gamma5FeedbackVc, gamma5FeedbackVe, gamma5FeedbackB,
    gamma5FeedbackR, gamma5FeedbackP, gamma5FeedbackW, gamma5FeedbackKappa,
    gamma5ClassicalS, gamma5ClassicalB]

/-- The actual improvement function pays a loss strictly below 1/2000,
including the original one-fifth factor. -/
theorem gamma5Feedback_actual_loss_lt {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    (∫ v in (1 : ℝ)..3,
      wuImprovementLimit true δ v * gamma5FeedbackLossKernel v) < 1/2000 := by
  have hbound (v : ℝ) (hv : v ∈ Icc (9373/7275 : ℝ) (103/75)) :
      0 ≤ wuImprovementLimit true δ v ∧ wuImprovementLimit true δ v ≤ 1 := by
    have hv' : v ∈ Icc (1 : ℝ) 3 := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    simpa only [gamma5Feedback_H_eq hv'] using gamma5Gain_H_bounds hδ hδhi v
  have hi := (gamma5Feedback_H_loss_integrable hδ hδhi).mono_set
    (show Set.uIcc (9373/7275 : ℝ) (103/75) ⊆ Set.uIcc (1 : ℝ) 3 by
      rw [uIcc_of_le (by norm_num : (9373/7275 : ℝ) ≤ 103/75),
        uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
      intro v hv
      exact ⟨by linarith [hv.1], by linarith [hv.2]⟩)
  rw [gamma5Feedback_loss_kernel_eq_budget] at hi ⊢
  exact Wu2004MeanValue.GammaFiveLossBudget.fourth_row_triangle_budget _ hbound hi

/-- The unscaled full gain can exceed the legal gain by less than 1/400. -/
theorem gamma5Feedback_full_gain_sub_legal_lt {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    gamma5FeedbackFullGain δ - gamma5GainIntegral δ < 1/400 := by
  have h := gamma5Feedback_actual_loss_lt hδ hδhi
  rw [← gamma5Feedback_loss_gain_eq hδ hδhi] at h
  linarith

/-- The actual full count, with the full-triangle gain and an explicit paid
1/400 debit. All original labels remain in the counted set. -/
theorem gamma5Feedback_full_count_upper_paid (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      gamma5ClassicalCount N δ (convolutionWuWindows N Δ V)
        (gamma5ClassicalLabels N δ (convolutionWuWindows N Δ V)) ≤
      (gamma5MassC5 - gamma5FeedbackFullGain δ + 1/400 + ε) *
        boxTheta N ((N : ℝ) ^ (1/2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT, hcount⟩ := gamma5Gain_full_count_upper k hk hδ hδhi hε
  refine ⟨T, hT, ?_⟩
  intro N hN he i Δ V hb
  have hdhalf : δ < 1/2 := by linarith
  have hΘ := gamma5Mass_theta_nonneg (show 2 ≤ N by omega) hδ hdhalf hb
  have hpaid := gamma5Feedback_full_gain_sub_legal_lt hδ hdhalf
  exact (hcount N hN he i Δ V hb).trans
    (mul_le_mul_of_nonneg_right (by linarith) hΘ)

end Wu2008DoubleSieve
