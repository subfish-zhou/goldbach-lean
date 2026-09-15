import MathlibNt.Wu2008DoubleSieve.Gamma5FeedbackTransport
import MathlibNt.Wu2008DoubleSieve.Gamma5FeedbackLoss

/-!
# Actual Hdelta kernel identities and the full Gamma5 count

FullGain is only an analytic integral, not a full-H actual-count estimate.
The actual producer uses the legal kernel, without the one-fifth factor.
-/

namespace Wu2008DoubleSieve

open Real Set MeasureTheory
open scoped Classical Topology Interval

noncomputable def gamma5FeedbackFullGain (δ : ℝ) : ℝ :=
  ∫ t in gamma5MassA..gamma5ClassicalB, ∫ u in t..gamma5ClassicalB,
    wuImprovementLimit true δ (gamma5GainV t u) / (t * u * (1 - t - u))

theorem gamma5Feedback_H_abs {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) (v : ℝ) :
    |gamma5GainH δ v| ≤ 1 := by
  rw [abs_of_nonneg (gamma5Gain_H_bounds hδ hδhi v).1]
  exact (gamma5Gain_H_bounds hδ hδhi v).2

theorem gamma5Feedback_H_eq {δ v : ℝ} (hv : v ∈ Icc (1 : ℝ) 3) :
    gamma5GainH δ v = wuImprovementLimit true δ v := by
  rw [gamma5GainH, gamma5Gain_clip_eq hv]

theorem gamma5Feedback_full_triangle (δ : ℝ) :
    gamma5FeedbackFullGain δ = gamma5FeedbackTriangleIntegral false (gamma5GainH δ) := by
  unfold gamma5FeedbackFullGain gamma5FeedbackTriangleIntegral
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le gamma5Mass_constants.2.1.le]
  intro t ht
  dsimp only
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le ht.2]
  intro u hu
  dsimp only
  have hv := gamma5Gain_triangle_bounds (v := (t, u)) ⟨ht.1, hu.1, hu.2⟩
  rw [gamma5Feedback_H_eq ⟨hv.2.2.1.le, hv.2.2.2.1.le⟩]
  simp only [Bool.false_eq_true, false_implies, if_true, gamma5MassKernel, mul_one_div]

theorem gamma5Feedback_legal_triangle (δ : ℝ) :
    gamma5GainIntegral δ = gamma5FeedbackTriangleIntegral true (gamma5GainH δ) := by
  unfold gamma5GainIntegral gamma5FeedbackTriangleIntegral
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le gamma5Mass_constants.2.1.le]
  intro t ht
  dsimp only
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le ht.2]
  intro u hu
  dsimp only
  have hv := gamma5Gain_triangle_bounds (v := (t, u)) ⟨ht.1, hu.1, hu.2⟩
  rw [gamma5Feedback_H_eq ⟨hv.2.2.1.le, hv.2.2.2.1.le⟩]
  simp only [gamma5GainLiteral, true_implies, gamma5MassKernel, mul_one_div]

theorem gamma5Feedback_H_kernel_integrable {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (legal : Bool) :
    IntervalIntegrable (fun v => wuImprovementLimit true δ v *
      (if legal then gamma5FeedbackLegalKernel v else gamma5FeedbackFullKernel v)) volume 1 3 := by
  have hi := gamma5Feedback_weighted_kernel_integrable legal
    (gamma5Gain_H_antitone hδ hδhi).measurable (gamma5Feedback_H_abs hδ hδhi)
  apply hi.intervalIntegrable.congr
  intro v hv
  dsimp only
  rw [gamma5Feedback_H_eq (by
    simpa only [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] using uIoc_subset_uIcc hv)]

/-- Exact transport of the actual legal Hdelta gain to its positive explicit kernel. -/
theorem gamma5Feedback_legal_gain_eq {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    gamma5GainIntegral δ =
      ∫ v in (1 : ℝ)..3, wuImprovementLimit true δ v * gamma5FeedbackLegalKernel v := by
  rw [gamma5Feedback_legal_triangle,
    gamma5Feedback_transport true (gamma5Gain_H_antitone hδ hδhi).measurable
      (gamma5Feedback_H_abs hδ hδhi)]
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
  intro v hv
  dsimp only
  rw [gamma5Feedback_H_eq hv]
  rfl

/-- Analytic full-triangle identity; this is not a full-H count bound. -/
theorem gamma5Feedback_full_gain_eq {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    gamma5FeedbackFullGain δ =
      ∫ v in (1 : ℝ)..3, wuImprovementLimit true δ v * gamma5FeedbackFullKernel v := by
  rw [gamma5Feedback_full_triangle,
    gamma5Feedback_transport false (gamma5Gain_H_antitone hδ hδhi).measurable
      (gamma5Feedback_H_abs hδ hδhi)]
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
  intro v hv
  dsimp only
  rw [gamma5Feedback_H_eq hv]
  rfl

theorem gamma5Feedback_H_loss_integrable {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    IntervalIntegrable (fun v => wuImprovementLimit true δ v * gamma5FeedbackLossKernel v)
      volume 1 3 := by
  have hf := gamma5Feedback_H_kernel_integrable hδ hδhi false
  have hl := gamma5Feedback_H_kernel_integrable hδ hδhi true
  simp only [Bool.false_eq_true, if_false, if_true] at hf hl
  have hi := (hf.sub hl).div_const 5
  apply hi.congr
  intro v _
  dsimp only
  rw [gamma5Feedback_kernel_identity v]
  ring

/-- The lost contribution contains exactly one factor of one fifth. -/
theorem gamma5Feedback_loss_gain_eq {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    (gamma5FeedbackFullGain δ - gamma5GainIntegral δ) / 5 =
      ∫ v in (1 : ℝ)..3, wuImprovementLimit true δ v * gamma5FeedbackLossKernel v := by
  rw [gamma5Feedback_full_gain_eq hδ hδhi, gamma5Feedback_legal_gain_eq hδ hδhi]
  have hf := gamma5Feedback_H_kernel_integrable hδ hδhi false
  have hl := gamma5Feedback_H_kernel_integrable hδ hδhi true
  simp only [Bool.false_eq_true, if_false, if_true] at hf hl
  rw [← intervalIntegral.integral_sub hf hl, ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro v _
  dsimp only
  rw [gamma5Feedback_kernel_identity v]
  ring

/-- Physically instantiated actual full count, retaining every original label. -/
theorem gamma5Feedback_full_count_upper (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      gamma5ClassicalCount N δ (convolutionWuWindows N Δ V)
        (gamma5ClassicalLabels N δ (convolutionWuWindows N Δ V)) ≤
      (gamma5MassC5 -
        (∫ v in (1 : ℝ)..3, wuImprovementLimit true δ v * gamma5FeedbackLegalKernel v) + ε) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  rw [← gamma5Feedback_legal_gain_eq hδ (by linarith)]
  exact gamma5Gain_full_count_upper k hk hδ hδhi hε

end Wu2008DoubleSieve
