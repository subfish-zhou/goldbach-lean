import MathlibNt.Wu2008DoubleSieve.Gamma5GainMain
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedKernel
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackTriangle

/-!
# Explicit full, legal, and one-fifth loss kernels for Gamma5
-/

namespace Wu2008DoubleSieve

open Real Set MeasureTheory
open scoped Classical Topology Interval

noncomputable def gamma5FeedbackKappa : ℝ := 291 / 100
noncomputable def gamma5FeedbackVm : ℝ := gamma5ClassicalS * (1 - 2 * gamma5ClassicalB)
noncomputable def gamma5FeedbackVc : ℝ := gamma5ClassicalS * (1 - gamma5ClassicalB) / 2
noncomputable def gamma5FeedbackVe : ℝ := gamma5ClassicalS / 3
noncomputable def gamma5FeedbackVf : ℝ := gamma5ClassicalS * (1 - gamma5MassA - gamma5ClassicalB)
noncomputable def gamma5FeedbackVp : ℝ := gamma5ClassicalS - 2
noncomputable def gamma5FeedbackW (v : ℝ) : ℝ := 1 - v / gamma5ClassicalS
noncomputable def gamma5FeedbackP (v : ℝ) : ℝ := 1 / (v * gamma5FeedbackW v)
noncomputable def gamma5FeedbackB (v : ℝ) : ℝ :=
  gamma5FeedbackP v *
    log (gamma5ClassicalS /
      (gamma5FeedbackKappa * gamma5ClassicalS - gamma5ClassicalS - gamma5FeedbackKappa * v))
noncomputable def gamma5FeedbackA (v : ℝ) : ℝ :=
  gamma5FeedbackP v * log (gamma5ClassicalS - 1 - v)
noncomputable def gamma5FeedbackR (v : ℝ) : ℝ :=
  gamma5FeedbackP v * log ((gamma5ClassicalS - 2 * v) / v)
noncomputable def gamma5FeedbackLegalMiddle (v : ℝ) : ℝ :=
  gamma5FeedbackP v * log (gamma5ClassicalB * v /
    ((1 - v / gamma5ClassicalS - gamma5ClassicalB) * (gamma5ClassicalS - 2 * v)))

noncomputable def gamma5FeedbackFullKernel (v : ℝ) : ℝ :=
  if gamma5FeedbackVm ≤ v ∧ v ≤ gamma5FeedbackVf then gamma5FeedbackB v
  else if gamma5FeedbackVf < v ∧ v ≤ gamma5FeedbackVp then gamma5FeedbackA v else 0

noncomputable def gamma5FeedbackLossKernel (v : ℝ) : ℝ :=
  if gamma5FeedbackVm ≤ v ∧ v ≤ gamma5FeedbackVc then gamma5FeedbackB v / 5
  else if gamma5FeedbackVc < v ∧ v < gamma5FeedbackVe then gamma5FeedbackR v / 5 else 0

noncomputable def gamma5FeedbackLegalKernel (v : ℝ) : ℝ :=
  if gamma5FeedbackVc < v ∧ v < gamma5FeedbackVe then gamma5FeedbackLegalMiddle v
  else if gamma5FeedbackVe ≤ v ∧ v ≤ gamma5FeedbackVf then gamma5FeedbackB v
  else if gamma5FeedbackVf < v ∧ v ≤ gamma5FeedbackVp then gamma5FeedbackA v else 0

theorem gamma5Feedback_breakpoints :
    gamma5FeedbackVm = 9373 / 7275 ∧ gamma5FeedbackVc = 19673 / 14550 ∧
    gamma5FeedbackVe = 103 / 75 ∧ gamma5FeedbackVf = 12398 / 7275 ∧
    gamma5FeedbackVp = 53 / 25 ∧
    1 < gamma5FeedbackVm ∧ gamma5FeedbackVm < gamma5FeedbackVc ∧
    gamma5FeedbackVc < gamma5FeedbackVe ∧ gamma5FeedbackVe < gamma5FeedbackVf ∧
    gamma5FeedbackVf < gamma5FeedbackVp ∧ gamma5FeedbackVp < 3 := by
  norm_num [gamma5FeedbackVm, gamma5FeedbackVc, gamma5FeedbackVe, gamma5FeedbackVf,
    gamma5FeedbackVp, gamma5ClassicalS, gamma5MassA, gamma5ClassicalB]

theorem gamma5Feedback_B_ratio (v : ℝ) :
    gamma5ClassicalS /
      (gamma5FeedbackKappa * gamma5ClassicalS - gamma5ClassicalS - gamma5FeedbackKappa * v) =
        gamma5ClassicalB / (gamma5FeedbackW v - gamma5ClassicalB) := by
  have heq : gamma5FeedbackKappa * gamma5ClassicalS - gamma5ClassicalS -
      gamma5FeedbackKappa * v =
      (gamma5ClassicalS / gamma5ClassicalB) * (gamma5FeedbackW v - gamma5ClassicalB) := by
    norm_num [gamma5ClassicalS, gamma5FeedbackKappa, gamma5ClassicalB, gamma5FeedbackW]
    ring
  rw [heq, div_mul_eq_div_div]
  norm_num [gamma5ClassicalS, gamma5ClassicalB]

theorem gamma5Feedback_joins :
    gamma5FeedbackB gamma5FeedbackVm = 0 ∧
    gamma5FeedbackB gamma5FeedbackVc =
      gamma5FeedbackP gamma5FeedbackVc * log (200 / 191) ∧
    gamma5FeedbackR gamma5FeedbackVc =
      gamma5FeedbackP gamma5FeedbackVc * log (200 / 191) ∧
    gamma5FeedbackR gamma5FeedbackVe = 0 ∧
    gamma5FeedbackLegalMiddle gamma5FeedbackVc = 0 ∧
    gamma5FeedbackLegalMiddle gamma5FeedbackVe = gamma5FeedbackB gamma5FeedbackVe ∧
    gamma5FeedbackB gamma5FeedbackVf = gamma5FeedbackA gamma5FeedbackVf ∧
    gamma5FeedbackA gamma5FeedbackVp = 0 := by
  norm_num [gamma5FeedbackB, gamma5FeedbackA, gamma5FeedbackR, gamma5FeedbackLegalMiddle,
    gamma5FeedbackVm, gamma5FeedbackVc, gamma5FeedbackVe, gamma5FeedbackVf, gamma5FeedbackVp,
    gamma5FeedbackKappa, gamma5ClassicalS, gamma5ClassicalB, gamma5MassA]

noncomputable def gamma5FeedbackDensity (v t : ℝ) : ℝ :=
  1 / (v * t * (gamma5FeedbackW v - t))

def gamma5FeedbackSlice (legal : Bool) (v t : ℝ) : Prop :=
  gamma5MassA ≤ t ∧ t ≤ gamma5FeedbackW v / 2 ∧ gamma5FeedbackW v - gamma5ClassicalB ≤ t ∧
    (legal = true → t ≤ v / gamma5ClassicalS)

noncomputable def gamma5FeedbackMasked (legal : Bool) (v t : ℝ) : ℝ :=
  if gamma5FeedbackSlice legal v t then gamma5FeedbackDensity v t else 0

theorem gamma5Feedback_slice_bounds {legal : Bool} {v t : ℝ}
    (h : gamma5FeedbackSlice legal v t) :
    v ∈ Icc gamma5FeedbackVm gamma5FeedbackVp ∧
    t ∈ Icc gamma5MassA gamma5ClassicalB ∧
    gamma5FeedbackW v - t ∈ Icc gamma5MassA gamma5ClassicalB := by
  rcases h with ⟨ha, ht, hb, _⟩
  norm_num [gamma5FeedbackW, gamma5ClassicalS, gamma5ClassicalB, gamma5MassA,
    gamma5FeedbackVm, gamma5FeedbackVp] at *
  exact ⟨⟨by linarith, by linarith⟩, ⟨ha, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem gamma5Feedback_density_integral {v A B : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) (hBw : B < gamma5FeedbackW v) :
    (∫ t in A..B, gamma5FeedbackDensity v t) =
      gamma5FeedbackP v * log (B * (gamma5FeedbackW v - A) /
        (A * (gamma5FeedbackW v - B))) := by
  have hw : gamma5FeedbackW v ≠ 0 := ne_of_gt (hA.trans_le hAB |>.trans hBw)
  have heq (t : ℝ) : gamma5FeedbackDensity v t =
      gamma5FeedbackP v * firstFeedbackWeightedKernel (gamma5FeedbackW v) t := by
    dsimp [gamma5FeedbackDensity, gamma5FeedbackP, firstFeedbackWeightedKernel]
    field_simp
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul, firstFeedbackWeightedKernel_integral hA hAB hBw]

theorem gamma5Feedback_mask_interval (f : ℝ → ℝ) {A B : ℝ} (hAB : A ≤ B) :
    (∫ t : ℝ, if A ≤ t ∧ t ≤ B then f t else 0) = ∫ t in A..B, f t := by
  have heq : (fun t => if A ≤ t ∧ t ≤ B then f t else 0) = (Icc A B).indicator f := by
    funext t
    by_cases h : A ≤ t ∧ t ≤ B
    · rw [if_pos h, indicator_of_mem (show t ∈ Icc A B from h)]
    · rw [if_neg h, indicator_of_notMem (show t ∉ Icc A B from h)]
  rw [heq]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hAB]

theorem gamma5Feedback_mask_zero (f : ℝ → ℝ) {A B : ℝ} (hBA : B ≤ A) :
    (∫ t : ℝ, if A ≤ t ∧ t ≤ B then f t else 0) = 0 := by
  rcases hBA.eq_or_lt with he | he
  · subst B
    rw [gamma5Feedback_mask_interval f le_rfl, intervalIntegral.integral_same]
  · have hh (t : ℝ) : ¬(A ≤ t ∧ t ≤ B) := by intro h; linarith [h.1, h.2]
    simp only [if_neg (hh _), integral_zero]

end Wu2008DoubleSieve
