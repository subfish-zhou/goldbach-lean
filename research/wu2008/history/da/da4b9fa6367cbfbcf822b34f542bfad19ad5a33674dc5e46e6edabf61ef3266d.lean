import MathlibNt.Wu2008DoubleSieve.Gamma5FeedbackBounds
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Masked affine transport with bounded measurable input

The factor 1/S from the substitution cancels S/v in the source density.
No continuity of the input function is assumed.
-/

namespace Wu2008DoubleSieve

open Real Set MeasureTheory
open scoped Classical Topology Interval

noncomputable def gamma5FeedbackSource (legal : Bool) (H : ℝ → ℝ) (t u : ℝ) : ℝ :=
  if gamma5GainTriangle (t, u) ∧ (legal = true → gamma5GainLegal t u)
  then H (gamma5GainV t u) * gamma5MassKernel t u else 0

noncomputable def gamma5FeedbackTriangleIntegral (legal : Bool) (H : ℝ → ℝ) : ℝ :=
  ∫ t in gamma5MassA..gamma5ClassicalB, ∫ u in t..gamma5ClassicalB,
    if legal = true → gamma5GainLegal t u then
      H (gamma5GainV t u) * gamma5MassKernel t u else 0

theorem gamma5Feedback_W_V (t u : ℝ) :
    gamma5FeedbackW (gamma5GainV t u) = t + u := by
  dsimp [gamma5FeedbackW, gamma5GainV]
  rw [mul_div_cancel_left₀ _ (by norm_num [gamma5ClassicalS])]
  ring

theorem gamma5Feedback_source_slice (legal : Bool) (t u : ℝ) :
    (gamma5GainTriangle (t, u) ∧ (legal = true → gamma5GainLegal t u)) ↔
      gamma5FeedbackSlice legal (gamma5GainV t u) t := by
  rw [gamma5FeedbackSlice, gamma5Feedback_W_V]
  have hr : gamma5GainV t u / gamma5ClassicalS = 1 - t - u := by
    dsimp [gamma5GainV]
    exact mul_div_cancel_left₀ _ (by norm_num [gamma5ClassicalS])
  rw [hr]
  have hb : 2 * gamma5ClassicalB < 1 := by norm_num [gamma5ClassicalB]
  constructor
  · rintro ⟨h, hl⟩
    exact ⟨h.1, by linarith [h.2.1], by linarith [h.2.2],
      fun he => by have hh := (hl he).2; linarith⟩
  · rintro ⟨ha, ht, hu, hl⟩
    refine ⟨⟨ha, by linarith, by linarith⟩, ?_⟩
    intro he
    exact ⟨by linarith, by have hh := hl he; linarith⟩

theorem gamma5Feedback_source_density (t u : ℝ) :
    gamma5MassKernel t u = gamma5ClassicalS * gamma5FeedbackDensity (gamma5GainV t u) t := by
  rw [gamma5FeedbackDensity, gamma5Feedback_W_V]
  have hS : gamma5ClassicalS ≠ 0 := by norm_num [gamma5ClassicalS]
  dsimp [gamma5MassKernel, gamma5GainV]
  rw [show t + u - t = u by ring]
  field_simp

theorem gamma5Feedback_source_eq (legal : Bool) (H : ℝ → ℝ) (t u : ℝ) :
    gamma5FeedbackSource legal H t u =
      gamma5ClassicalS * (H (gamma5GainV t u) * gamma5FeedbackMasked legal (gamma5GainV t u) t) := by
  unfold gamma5FeedbackSource gamma5FeedbackMasked
  rw [← gamma5Feedback_source_slice]
  split_ifs
  · rw [gamma5Feedback_source_density]
    ring
  · simp only [mul_zero]

theorem gamma5Feedback_inner_substitution (legal : Bool) (H : ℝ → ℝ) (t : ℝ) :
    (∫ u : ℝ, gamma5FeedbackSource legal H t u) =
      ∫ v : ℝ, H v * gamma5FeedbackMasked legal v t := by
  simp_rw [gamma5Feedback_source_eq]
  rw [integral_const_mul]
  change gamma5ClassicalS * (∫ u : ℝ,
    (fun y => H (gamma5ClassicalS * y) * gamma5FeedbackMasked legal (gamma5ClassicalS * y) t)
      ((1 - t) - u)) = _
  rw [integral_sub_left_eq_self
    (fun y : ℝ => H (gamma5ClassicalS * y) * gamma5FeedbackMasked legal (gamma5ClassicalS * y) t)
    volume (1 - t)]
  rw [Measure.integral_comp_mul_left (fun v => H v * gamma5FeedbackMasked legal v t)]
  rw [smul_eq_mul, abs_of_pos (inv_pos.mpr (by norm_num [gamma5ClassicalS]))]
  rw [← mul_assoc, mul_inv_cancel₀ (by norm_num [gamma5ClassicalS]), one_mul]

theorem gamma5Feedback_source_measurable (legal : Bool) {H : ℝ → ℝ} (hm : Measurable H) :
    Measurable (fun p : ℝ × ℝ => gamma5FeedbackSource legal H p.1 p.2) := by
  simp_rw [gamma5Feedback_source_eq]
  have hv : Measurable (fun p : ℝ × ℝ => gamma5GainV p.1 p.2) := by
    unfold gamma5GainV
    fun_prop
  exact measurable_const.mul ((hm.comp hv).mul
    ((gamma5Feedback_masked_measurable legal).comp (hv.prodMk measurable_fst)))

theorem gamma5Feedback_source_support (legal : Bool) (H : ℝ → ℝ) :
    Function.support (fun p : ℝ × ℝ => gamma5FeedbackSource legal H p.1 p.2) ⊆
      Icc gamma5MassA gamma5ClassicalB ×ˢ Icc gamma5MassA gamma5ClassicalB := by
  intro p hp
  have ht : gamma5GainTriangle p := by
    by_contra ht
    apply hp
    exact if_neg (fun h => ht h.1)
  exact ⟨(gamma5Gain_triangle_bounds ht).1, (gamma5Gain_triangle_bounds ht).2.1⟩

theorem gamma5Feedback_source_bound (legal : Bool) {H : ℝ → ℝ}
    (hb : ∀ v, |H v| ≤ 1) (t u : ℝ) :
    ‖gamma5FeedbackSource legal H t u‖ ≤ 400 := by
  by_cases h : gamma5GainTriangle (t, u) ∧ (legal = true → gamma5GainLegal t u)
  · have ht := gamma5Gain_triangle_bounds h.1
    have hk := gamma5Gain_smooth_bounds (t, u)
    rw [gamma5Gain_smooth_eq ht.1 ht.2.1] at hk
    rw [gamma5FeedbackSource, if_pos h, Real.norm_eq_abs, abs_mul, abs_of_nonneg hk.1]
    exact (mul_le_mul (hb _) hk.2 hk.1 (by norm_num)).trans_eq (by norm_num)
  · rw [gamma5FeedbackSource, if_neg h, norm_zero]
    norm_num

theorem gamma5Feedback_source_integrable (legal : Bool) {H : ℝ → ℝ}
    (hm : Measurable H) (hb : ∀ v, |H v| ≤ 1) :
    Integrable (fun p : ℝ × ℝ => gamma5FeedbackSource legal H p.1 p.2) := by
  apply (integrableOn_iff_integrable_of_support_subset (gamma5Feedback_source_support legal H)).mp
  apply Measure.integrableOn_of_bounded (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
    (gamma5Feedback_source_measurable legal hm).aestronglyMeasurable (M := 400)
  exact Filter.Eventually.of_forall (fun p => gamma5Feedback_source_bound legal hb p.1 p.2)

theorem gamma5Feedback_source_inner (legal : Bool) (H : ℝ → ℝ) {t : ℝ}
    (ht : t ∈ Icc gamma5MassA gamma5ClassicalB) :
    (∫ u : ℝ, gamma5FeedbackSource legal H t u) =
      ∫ u in t..gamma5ClassicalB,
        if legal = true → gamma5GainLegal t u then H (gamma5GainV t u) * gamma5MassKernel t u else 0 := by
  have hs : Function.support (gamma5FeedbackSource legal H t) ⊆ Icc t gamma5ClassicalB := by
    intro u hu
    by_contra hn
    exact hu (if_neg (fun h => hn ⟨h.1.2.1, h.1.2.2⟩))
  rw [truncatedSixthMass_integral_eq_interval ht.2 hs]
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le ht.2]
  intro u hu
  dsimp only
  have hh : gamma5GainTriangle (t, u) := ⟨ht.1, hu.1, hu.2⟩
  simp only [gamma5FeedbackSource, hh, true_and]

theorem gamma5Feedback_triangle_product (legal : Bool) {H : ℝ → ℝ}
    (hm : Measurable H) (hb : ∀ v, |H v| ≤ 1) :
    gamma5FeedbackTriangleIntegral legal H =
      ∫ p : ℝ × ℝ, gamma5FeedbackSource legal H p.1 p.2 := by
  have hs : Function.support (fun t => ∫ u, gamma5FeedbackSource legal H t u) ⊆
      Icc gamma5MassA gamma5ClassicalB := by
    intro t ht
    by_contra hn
    apply ht
    have he (u : ℝ) : gamma5FeedbackSource legal H t u = 0 := by
      apply if_neg
      exact fun h => hn (gamma5Gain_triangle_bounds h.1).1
    simp only [he, integral_zero]
  rw [show (∫ p : ℝ × ℝ, gamma5FeedbackSource legal H p.1 p.2) =
      ∫ t, ∫ u, gamma5FeedbackSource legal H t u from
        integral_prod _ (gamma5Feedback_source_integrable legal hm hb),
    truncatedSixthMass_integral_eq_interval gamma5Mass_constants.2.1.le hs]
  symm
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le gamma5Mass_constants.2.1.le]
  exact fun t ht => gamma5Feedback_source_inner legal H ht

/-- The entire affine/Fubini transport, for a bounded measurable input. -/
theorem gamma5Feedback_transport (legal : Bool) {H : ℝ → ℝ}
    (hm : Measurable H) (hb : ∀ v, |H v| ≤ 1) :
    gamma5FeedbackTriangleIntegral legal H =
      ∫ v in (1 : ℝ)..3, H v *
        (if legal then gamma5FeedbackLegalKernel v else gamma5FeedbackFullKernel v) := by
  rw [gamma5Feedback_triangle_product legal hm hb]
  rw [show (∫ p : ℝ × ℝ, gamma5FeedbackSource legal H p.1 p.2) =
      ∫ t, ∫ u, gamma5FeedbackSource legal H t u from
        integral_prod _ (gamma5Feedback_source_integrable legal hm hb)]
  simp_rw [gamma5Feedback_inner_substitution]
  rw [integral_integral_swap (f := fun t v => H v * gamma5FeedbackMasked legal v t)
    (gamma5Feedback_weighted_integrable legal hm hb).swap]
  simp_rw [integral_const_mul]
  have heval (v : ℝ) : (∫ t, gamma5FeedbackMasked legal v t) =
      if legal then gamma5FeedbackLegalKernel v else gamma5FeedbackFullKernel v := by
    cases legal
    · exact gamma5Feedback_full_slice v
    · exact gamma5Feedback_legal_slice v
  have hs : Function.support (fun v => H v * ∫ t, gamma5FeedbackMasked legal v t) ⊆ Icc (1 : ℝ) 3 := by
    intro v hv
    by_contra hn
    have he (t : ℝ) : gamma5FeedbackMasked legal v t = 0 := by
      by_contra he
      exact hn (gamma5Feedback_masked_support legal (a := (v, t)) he).1
    exact hv (by dsimp only; simp only [he, integral_zero, mul_zero])
  rw [truncatedSixthMass_integral_eq_interval (by norm_num : (1 : ℝ) ≤ 3) hs]
  simp_rw [heval]

theorem gamma5Feedback_weighted_kernel_integrable (legal : Bool) {H : ℝ → ℝ}
    (hm : Measurable H) (hb : ∀ v, |H v| ≤ 1) :
    Integrable (fun v => H v *
      (if legal then gamma5FeedbackLegalKernel v else gamma5FeedbackFullKernel v)) := by
  have hi := (gamma5Feedback_weighted_integrable legal hm hb).integral_prod_left
  simp_rw [integral_const_mul] at hi
  cases legal
  · simpa only [Bool.false_eq_true, if_false, gamma5Feedback_full_slice] using hi
  · simpa only [if_true, gamma5Feedback_legal_slice] using hi

end Wu2008DoubleSieve
