import MathlibNt.Wu2008DoubleSieve.Gamma5FeedbackMain

/-!
# Literal integrability, support, and positive kernel documentation
-/

namespace Wu2008DoubleSieve

open Real Set MeasureTheory
open scoped Classical Topology Interval

theorem gamma5Feedback_denominators {v : ℝ} (hv : v ∈ Icc (1 : ℝ) 3) :
    0 < v ∧ 0 < gamma5FeedbackW v ∧ 0 < v * gamma5FeedbackW v ∧
      0 < gamma5FeedbackP v := by
  have hv0 : 0 < v := by linarith [hv.1]
  have hw : 0 < gamma5FeedbackW v := by
    unfold gamma5FeedbackW
    norm_num [gamma5ClassicalS]
    linarith [hv.2]
  exact ⟨hv0, hw, mul_pos hv0 hw, div_pos (by norm_num) (mul_pos hv0 hw)⟩

theorem gamma5Feedback_kernels_measurable :
    Measurable gamma5FeedbackFullKernel ∧ Measurable gamma5FeedbackLegalKernel ∧
      Measurable gamma5FeedbackLossKernel := by
  have hB : Measurable gamma5FeedbackB := by
    unfold gamma5FeedbackB gamma5FeedbackP gamma5FeedbackW
    fun_prop
  have hA : Measurable gamma5FeedbackA := by
    unfold gamma5FeedbackA gamma5FeedbackP gamma5FeedbackW
    fun_prop
  have hR : Measurable gamma5FeedbackR := by
    unfold gamma5FeedbackR gamma5FeedbackP gamma5FeedbackW
    fun_prop
  have hM : Measurable gamma5FeedbackLegalMiddle := by
    unfold gamma5FeedbackLegalMiddle gamma5FeedbackP gamma5FeedbackW
    fun_prop
  exact ⟨hB.ite measurableSet_Icc (hA.ite measurableSet_Ioc measurable_const),
    hM.ite measurableSet_Ioo (hB.ite measurableSet_Icc (hA.ite measurableSet_Ioc measurable_const)),
    (hB.div_const 5).ite measurableSet_Icc ((hR.div_const 5).ite measurableSet_Ioo measurable_const)⟩

theorem gamma5Feedback_kernels_nonnegative (v : ℝ) :
    0 ≤ gamma5FeedbackFullKernel v ∧ 0 ≤ gamma5FeedbackLegalKernel v ∧
      0 ≤ gamma5FeedbackLossKernel v := by
  have h := gamma5Feedback_full_legal_bounds v
  exact ⟨h.1.trans h.2.1, h.1, (gamma5Feedback_loss_bounds v).1⟩

theorem gamma5Feedback_loss_formula (v : ℝ) :
    gamma5FeedbackLossKernel v =
      if gamma5FeedbackVm ≤ v ∧ v ≤ gamma5FeedbackVc then
        gamma5FeedbackP v / 5 * log (gamma5ClassicalS /
          (gamma5FeedbackKappa * gamma5ClassicalS - gamma5ClassicalS - gamma5FeedbackKappa * v))
      else if gamma5FeedbackVc < v ∧ v < gamma5FeedbackVe then
        gamma5FeedbackP v / 5 * log ((gamma5ClassicalS - 2 * v) / v) else 0 := by
  unfold gamma5FeedbackLossKernel gamma5FeedbackB gamma5FeedbackR
  split_ifs <;> ring

theorem gamma5Feedback_source_slice_integrable (legal : Bool) {H : ℝ → ℝ}
    (hm : Measurable H) (hb : ∀ v, |H v| ≤ 1) (t : ℝ) :
    Integrable (gamma5FeedbackSource legal H t) := by
  have hs : Function.support (gamma5FeedbackSource legal H t) ⊆ Icc gamma5MassA gamma5ClassicalB := by
    intro u hu
    exact (gamma5Feedback_source_support legal H (a := (t, u)) hu).2
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  apply Measure.integrableOn_of_bounded isCompact_Icc.measure_lt_top.ne
    ((gamma5Feedback_source_measurable legal hm).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable (M := 400)
  exact Filter.Eventually.of_forall (fun u => gamma5Feedback_source_bound legal hb t u)

theorem gamma5Feedback_full_source_eq {δ t u : ℝ}
    (ht : gamma5MassA ≤ t) (htu : t ≤ u) (hu : u ≤ gamma5ClassicalB) :
    gamma5FeedbackSource false (gamma5GainH δ) t u =
      wuImprovementLimit true δ (gamma5GainV t u) / (t * u * (1 - t - u)) := by
  have htri : gamma5GainTriangle (t, u) := ⟨ht, htu, hu⟩
  have hv := gamma5Gain_triangle_bounds htri
  rw [gamma5FeedbackSource, if_pos ⟨htri, by simp⟩,
    gamma5Feedback_H_eq ⟨hv.2.2.1.le, hv.2.2.2.1.le⟩]
  simp only [gamma5MassKernel, mul_one_div]

theorem gamma5Feedback_full_inner_integrable {δ t : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (ht : t ∈ Icc gamma5MassA gamma5ClassicalB) :
    IntervalIntegrable (fun u => wuImprovementLimit true δ (gamma5GainV t u) /
      (t * u * (1 - t - u))) volume t gamma5ClassicalB := by
  have hi := gamma5Feedback_source_slice_integrable false
    (gamma5Gain_H_antitone hδ hδhi).measurable (gamma5Feedback_H_abs hδ hδhi) t
  apply hi.intervalIntegrable.congr
  intro u hu
  have hu' : u ∈ Icc t gamma5ClassicalB := by
    simpa only [uIcc_of_le ht.2] using uIoc_subset_uIcc hu
  exact gamma5Feedback_full_source_eq ht.1 hu'.1 hu'.2

theorem gamma5Feedback_full_inner_eq {δ t : ℝ} (ht : t ∈ Icc gamma5MassA gamma5ClassicalB) :
    (∫ u, gamma5FeedbackSource false (gamma5GainH δ) t u) =
      ∫ u in t..gamma5ClassicalB,
        wuImprovementLimit true δ (gamma5GainV t u) / (t * u * (1 - t - u)) := by
  rw [gamma5Feedback_source_inner false (gamma5GainH δ) ht]
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le ht.2]
  intro u hu
  dsimp only
  have hv := gamma5Gain_triangle_bounds (v := (t, u)) ⟨ht.1, hu.1, hu.2⟩
  rw [gamma5Feedback_H_eq ⟨hv.2.2.1.le, hv.2.2.2.1.le⟩]
  simp only [Bool.false_eq_true, false_implies, if_true, gamma5MassKernel, mul_one_div]

theorem gamma5Feedback_full_outer_integrable {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    IntervalIntegrable (fun t => ∫ u in t..gamma5ClassicalB,
      wuImprovementLimit true δ (gamma5GainV t u) / (t * u * (1 - t - u)))
      volume gamma5MassA gamma5ClassicalB := by
  have hi := (gamma5Feedback_source_integrable false
    (gamma5Gain_H_antitone hδ hδhi).measurable (gamma5Feedback_H_abs hδ hδhi)).integral_prod_left
  apply hi.intervalIntegrable.congr
  intro t ht
  exact gamma5Feedback_full_inner_eq (by
    simpa only [uIcc_of_le gamma5Mass_constants.2.1.le] using uIoc_subset_uIcc ht)

theorem gamma5Feedback_actual_loss_nonnegative {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    0 ≤ (gamma5FeedbackFullGain δ - gamma5GainIntegral δ) / 5 := by
  rw [gamma5Feedback_loss_gain_eq hδ hδhi]
  apply intervalIntegral.integral_nonneg (by norm_num : (1 : ℝ) ≤ 3)
  intro v hv
  have hH := (gamma5Gain_H_bounds hδ hδhi v).1
  rw [gamma5Feedback_H_eq hv] at hH
  exact mul_nonneg hH (gamma5Feedback_loss_bounds v).1

end Wu2008DoubleSieve
