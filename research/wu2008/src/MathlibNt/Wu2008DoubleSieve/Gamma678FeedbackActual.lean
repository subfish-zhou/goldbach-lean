import MathlibNt.Wu2008DoubleSieve.Gamma678FeedbackTransport
import MathlibNt.Wu2008DoubleSieve.Gamma5FeedbackMain

/-! Literal actual-H endpoints. Clipping is removed on both sides of the equality. -/
namespace Wu2008DoubleSieve.Gamma678Feedback
open Real Set MeasureTheory
open scoped Classical Topology Interval

theorem actual_source_eq {j : Kind} {δ t u : ℝ} (h : region j t u) :
    source j (gamma5GainH δ) t u =
      wuImprovementLimit true δ (V j t u) / (t * u * (1 - t - u)) := by
  have hv : V j t u ∈ Icc (1 : ℝ) 3 :=
    ⟨(image_constants j).1.le.trans (region_image h).1,
      (region_image h).2.trans (image_constants j).2.le⟩
  rw [source, if_pos h, gamma5Feedback_H_eq hv]
  simp only [D, mul_one_div]

theorem actual_inner_eq (j : Kind) {δ t : ℝ} (ht : t ∈ Icc a b) :
    (∫ u : ℝ, source j (gamma5GainH δ) t u) =
      ∫ u in lo j t..hi j, wuImprovementLimit true δ (V j t u) / (t * u * (1 - t - u)) := by
  rw [source_inner j _ ht]
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le (lo_le_hi j ht)]
  intro u hu
  have h : region j t u := ⟨ht, hu⟩
  exact (if_pos h : source j (gamma5GainH δ) t u = _).symm.trans (actual_source_eq h)

theorem actual_inner_integrable (j : Kind) {δ t : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (ht : t ∈ Icc a b) :
    IntervalIntegrable (fun u => wuImprovementLimit true δ (V j t u) / (t * u * (1 - t - u)))
      volume (lo j t) (hi j) := by
  apply (source_row_integrable j (gamma5Gain_H_antitone hδ hδhi).measurable
    (by norm_num : (0 : ℝ) ≤ 1) (gamma5Feedback_H_abs hδ hδhi) t).intervalIntegrable.congr
  intro u hu
  apply actual_source_eq
  exact ⟨ht, by simpa only [uIcc_of_le (lo_le_hi j ht)] using uIoc_subset_uIcc hu⟩

theorem actual_outer_integrable (j : Kind) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    IntervalIntegrable (fun t => ∫ u in lo j t..hi j,
      wuImprovementLimit true δ (V j t u) / (t * u * (1 - t - u))) volume a b := by
  apply (source_integrable j (gamma5Gain_H_antitone hδ hδhi).measurable
    (by norm_num : (0 : ℝ) ≤ 1) (gamma5Feedback_H_abs hδ hδhi)).integral_prod_left.intervalIntegrable.congr
  intro t ht
  exact actual_inner_eq j (by simpa only [uIcc_of_le constants.2.1.le] using uIoc_subset_uIcc ht)

theorem actual_rhs_integrable (j : Kind) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    IntervalIntegrable (fun v => wuImprovementLimit true δ v * K j v) volume 1 3 := by
  apply (weighted_kernel_integrable j (gamma5Gain_H_antitone hδ hδhi).measurable
    (by norm_num : (0 : ℝ) ≤ 1) (gamma5Feedback_H_abs hδ hδhi)).intervalIntegrable.congr
  intro v hv
  have hv' : v ∈ Icc (1 : ℝ) 3 := by
    simpa only [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] using uIoc_subset_uIcc hv
  dsimp only
  rw [gamma5Feedback_H_eq hv']

theorem actual_eq (j : Kind) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    (∫ t in a..b, ∫ u in lo j t..hi j,
      wuImprovementLimit true δ (V j t u) / (t * u * (1 - t - u))) =
      ∫ v in (1 : ℝ)..3, wuImprovementLimit true δ v * K j v := by
  calc
    _ = I j (gamma5GainH δ) := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le constants.2.1.le]
      intro t ht
      exact (actual_inner_eq j ht).symm.trans (source_inner j _ ht)
    _ = ∫ v in (1 : ℝ)..3, gamma5GainH δ v * K j v :=
      transport j (gamma5Gain_H_antitone hδ hδhi).measurable
        (by norm_num : (0 : ℝ) ≤ 1) (gamma5Feedback_H_abs hδ hδhi)
    _ = _ := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
      intro v hv
      dsimp only
      rw [gamma5Feedback_H_eq hv]

theorem actual6_eq {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    (∫ t in a..b, ∫ u in c..f,
      wuImprovementLimit true δ (S * (1 - t - u)) / (t * u * (1 - t - u))) =
      ∫ v in (1 : ℝ)..3, wuImprovementLimit true δ v * K6 v := actual_eq .six hδ hδhi

theorem actual7_eq {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    (∫ t in a..b, ∫ u in t..b,
      wuImprovementLimit true δ ((1 - t - u) / t) / (t * u * (1 - t - u))) =
      ∫ v in (1 : ℝ)..3, wuImprovementLimit true δ v * K7 v := actual_eq .seven hδ hδhi

theorem actual8_eq {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    (∫ t in a..b, ∫ u in b..c,
      wuImprovementLimit true δ ((1 - t - u) / t) / (t * u * (1 - t - u))) =
      ∫ v in (1 : ℝ)..3, wuImprovementLimit true δ v * K8 v := actual_eq .eight hδ hδhi

theorem actual6_inner_integrable {δ t : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (ht : t ∈ Icc a b) :
    IntervalIntegrable (fun u => wuImprovementLimit true δ (S * (1 - t - u)) /
      (t * u * (1 - t - u))) volume c f := actual_inner_integrable .six hδ hδhi ht

theorem actual7_inner_integrable {δ t : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (ht : t ∈ Icc a b) :
    IntervalIntegrable (fun u => wuImprovementLimit true δ ((1 - t - u) / t) /
      (t * u * (1 - t - u))) volume t b := actual_inner_integrable .seven hδ hδhi ht

theorem actual8_inner_integrable {δ t : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (ht : t ∈ Icc a b) :
    IntervalIntegrable (fun u => wuImprovementLimit true δ ((1 - t - u) / t) /
      (t * u * (1 - t - u))) volume b c := actual_inner_integrable .eight hδ hδhi ht

theorem actual6_outer_integrable {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    IntervalIntegrable (fun t => ∫ u in c..f, wuImprovementLimit true δ (S * (1 - t - u)) /
      (t * u * (1 - t - u))) volume a b := actual_outer_integrable .six hδ hδhi

theorem actual7_outer_integrable {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    IntervalIntegrable (fun t => ∫ u in t..b, wuImprovementLimit true δ ((1 - t - u) / t) /
      (t * u * (1 - t - u))) volume a b := actual_outer_integrable .seven hδ hδhi

theorem actual8_outer_integrable {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    IntervalIntegrable (fun t => ∫ u in b..c, wuImprovementLimit true δ ((1 - t - u) / t) /
      (t * u * (1 - t - u))) volume a b := actual_outer_integrable .eight hδ hδhi

theorem actual6_rhs_integrable {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    IntervalIntegrable (fun v => wuImprovementLimit true δ v * K6 v) volume 1 3 :=
  actual_rhs_integrable .six hδ hδhi

theorem actual7_rhs_integrable {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    IntervalIntegrable (fun v => wuImprovementLimit true δ v * K7 v) volume 1 3 :=
  actual_rhs_integrable .seven hδ hδhi

theorem actual8_rhs_integrable {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    IntervalIntegrable (fun v => wuImprovementLimit true δ v * K8 v) volume 1 3 :=
  actual_rhs_integrable .eight hδ hδhi

end Wu2008DoubleSieve.Gamma678Feedback
