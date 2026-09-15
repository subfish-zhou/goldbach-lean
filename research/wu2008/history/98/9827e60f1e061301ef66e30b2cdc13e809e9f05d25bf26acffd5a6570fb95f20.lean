import MathlibNt.Wu2008DoubleSieve.Gamma5FeedbackSlices

namespace Wu2008DoubleSieve

open Real Set MeasureTheory
open scoped Classical Topology Interval

theorem gamma5Feedback_slice_measurable (legal : Bool) :
    MeasurableSet {p : ℝ × ℝ | gamma5FeedbackSlice legal p.1 p.2} := by
  cases legal <;> simp only [gamma5FeedbackSlice, Bool.false_eq_true, false_implies,
    true_implies, and_true]
  all_goals
    unfold gamma5FeedbackW
    measurability

theorem gamma5Feedback_masked_measurable (legal : Bool) :
    Measurable (fun p : ℝ × ℝ => gamma5FeedbackMasked legal p.1 p.2) := by
  apply Measurable.ite (gamma5Feedback_slice_measurable legal) _ measurable_const
  unfold gamma5FeedbackDensity gamma5FeedbackW
  fun_prop

theorem gamma5Feedback_masked_bounds (legal : Bool) (v t : ℝ) :
    0 ≤ gamma5FeedbackMasked legal v t ∧ gamma5FeedbackMasked legal v t ≤ 100 := by
  by_cases h : gamma5FeedbackSlice legal v t
  · have hb := gamma5Feedback_slice_bounds h
    have hv : 1 ≤ v := gamma5Feedback_breakpoints.2.2.2.2.2.1.le.trans hb.1.1
    have ht : 1 / 10 ≤ t := gamma5Mass_constants.1.trans hb.2.1.1
    have hu : 1 / 10 ≤ gamma5FeedbackW v - t := gamma5Mass_constants.1.trans hb.2.2.1
    have htu := mul_le_mul ht hu (by norm_num) (by linarith : 0 ≤ t)
    have hden := mul_le_mul hv htu (by norm_num : (0 : ℝ) ≤ 1 / 10 * (1 / 10)) (by linarith)
    have hp : 0 < v * t * (gamma5FeedbackW v - t) := by nlinarith [hden]
    rw [gamma5FeedbackMasked, if_pos h, gamma5FeedbackDensity]
    exact ⟨(div_pos (by norm_num) hp).le, (div_le_iff₀ hp).mpr (by nlinarith [hden])⟩
  · simp only [gamma5FeedbackMasked, if_neg h]
    norm_num

theorem gamma5Feedback_masked_support (legal : Bool) :
    Function.support (fun p : ℝ × ℝ => gamma5FeedbackMasked legal p.1 p.2) ⊆
      Icc (1 : ℝ) 3 ×ˢ Icc gamma5MassA gamma5ClassicalB := by
  intro p hp
  have h : gamma5FeedbackSlice legal p.1 p.2 := by
    by_contra h
    exact hp (if_neg h)
  have hb := gamma5Feedback_slice_bounds h
  have ho := gamma5Feedback_breakpoints
  exact ⟨⟨ho.2.2.2.2.2.1.le.trans hb.1.1, hb.1.2.trans ho.2.2.2.2.2.2.2.2.2.2.le⟩, hb.2.1⟩

theorem gamma5Feedback_weighted_integrable (legal : Bool) {H : ℝ → ℝ}
    (hm : Measurable H) (hb : ∀ v, |H v| ≤ 1) :
    Integrable (fun p : ℝ × ℝ => H p.1 * gamma5FeedbackMasked legal p.1 p.2) := by
  have hs : Function.support (fun p : ℝ × ℝ => H p.1 * gamma5FeedbackMasked legal p.1 p.2) ⊆
      Icc (1 : ℝ) 3 ×ˢ Icc gamma5MassA gamma5ClassicalB := by
    intro p hp
    exact gamma5Feedback_masked_support legal (fun h => hp (by rw [h, mul_zero]))
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  apply Measure.integrableOn_of_bounded (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
    ((hm.comp measurable_fst).mul (gamma5Feedback_masked_measurable legal)).aestronglyMeasurable
    (C := 100)
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gamma5Feedback_masked_bounds legal p.1 p.2).1]
  exact (mul_le_mul (hb p.1) (gamma5Feedback_masked_bounds legal p.1 p.2).2
    (gamma5Feedback_masked_bounds legal p.1 p.2).1 (by norm_num)).trans_eq (by norm_num)

theorem gamma5Feedback_masked_integrable (legal : Bool) :
    Integrable (fun p : ℝ × ℝ => gamma5FeedbackMasked legal p.1 p.2) := by
  simpa only [one_mul] using gamma5Feedback_weighted_integrable legal measurable_const
    (show ∀ _ : ℝ, |(1 : ℝ)| ≤ 1 by intro _; norm_num)

theorem gamma5Feedback_slice_integrable (legal : Bool) (v : ℝ) :
    Integrable (gamma5FeedbackMasked legal v) := by
  have hs : Function.support (gamma5FeedbackMasked legal v) ⊆ Icc gamma5MassA gamma5ClassicalB := by
    intro t ht
    exact (gamma5Feedback_masked_support legal (p := (v, t)) ht).2
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  apply Measure.integrableOn_of_bounded isCompact_Icc.measure_lt_top.ne
    ((gamma5Feedback_masked_measurable legal).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (C := 100)
  exact Filter.Eventually.of_forall (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (gamma5Feedback_masked_bounds legal v t).1]
    exact (gamma5Feedback_masked_bounds legal v t).2)

theorem gamma5Feedback_slice_integral_bounds (legal : Bool) (v : ℝ) :
    0 ≤ (∫ t : ℝ, gamma5FeedbackMasked legal v t) ∧
      (∫ t : ℝ, gamma5FeedbackMasked legal v t) ≤ 100 := by
  refine ⟨integral_nonneg (fun t => (gamma5Feedback_masked_bounds legal v t).1), ?_⟩
  have hi : Integrable ((Icc gamma5MassA gamma5ClassicalB).indicator (fun _ => (100 : ℝ))) :=
    (integrableOn_const isCompact_Icc.measure_lt_top.ne).integrable_indicator measurableSet_Icc
  have hpoint (t : ℝ) : gamma5FeedbackMasked legal v t ≤
      (Icc gamma5MassA gamma5ClassicalB).indicator (fun _ => (100 : ℝ)) t := by
    by_cases ht : t ∈ Icc gamma5MassA gamma5ClassicalB
    · rw [indicator_of_mem ht]
      exact (gamma5Feedback_masked_bounds legal v t).2
    · rw [indicator_of_notMem ht]
      have h : ¬gamma5FeedbackSlice legal v t :=
        fun h => ht (gamma5Feedback_slice_bounds h).2.1
      exact le_of_eq (if_neg h)
  have hh := integral_mono (gamma5Feedback_slice_integrable legal v) hi hpoint
  rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
    Real.volume_real_Icc_of_le gamma5Mass_constants.2.1.le] at hh
  have hw : gamma5ClassicalB - gamma5MassA ≤ 1 := by
    norm_num [gamma5ClassicalB, gamma5MassA, gamma5ClassicalS]
  linarith

theorem gamma5Feedback_full_legal_bounds (v : ℝ) :
    0 ≤ gamma5FeedbackLegalKernel v ∧ gamma5FeedbackLegalKernel v ≤ gamma5FeedbackFullKernel v ∧
      gamma5FeedbackFullKernel v ≤ 100 := by
  rw [← gamma5Feedback_legal_slice, ← gamma5Feedback_full_slice]
  refine ⟨(gamma5Feedback_slice_integral_bounds true v).1, ?_,
    (gamma5Feedback_slice_integral_bounds false v).2⟩
  apply integral_mono (gamma5Feedback_slice_integrable true v) (gamma5Feedback_slice_integrable false v)
  intro t
  by_cases h : gamma5FeedbackSlice true v t
  · have hf : gamma5FeedbackSlice false v t := ⟨h.1, h.2.1, h.2.2.1, by simp⟩
    rw [gamma5FeedbackMasked, gamma5FeedbackMasked, if_pos h, if_pos hf]
  · rw [gamma5FeedbackMasked, if_neg h]
    exact (gamma5Feedback_masked_bounds false v t).1

theorem gamma5Feedback_full_integrable : Integrable gamma5FeedbackFullKernel := by
  have h := (gamma5Feedback_masked_integrable false).integral_prod_left
  simpa only [gamma5Feedback_full_slice] using h

theorem gamma5Feedback_legal_integrable : Integrable gamma5FeedbackLegalKernel := by
  have h := (gamma5Feedback_masked_integrable true).integral_prod_left
  simpa only [gamma5Feedback_legal_slice] using h

end Wu2008DoubleSieve
