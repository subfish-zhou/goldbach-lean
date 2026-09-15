import MathlibNt.Wu2008DoubleSieve.Gamma678FeedbackKernel

/-! Absolute integrability before either affine substitution or Fubini. -/
namespace Wu2008DoubleSieve.Gamma678Feedback
open Real Set MeasureTheory
open scoped Classical Topology Interval

noncomputable def D (t u : ℝ) : ℝ := 1 / (t * u * (1 - t - u))
noncomputable def source (j : Kind) (H : ℝ → ℝ) (t u : ℝ) : ℝ :=
  if region j t u then H (V j t u) * D t u else 0
noncomputable def I (j : Kind) (H : ℝ → ℝ) : ℝ :=
  ∫ t in a..b, ∫ u in lo j t..hi j, H (V j t u) * D t u

theorem source_measurable (j : Kind) {H : ℝ → ℝ} (hm : Measurable H) :
    Measurable (fun p : ℝ × ℝ => source j H p.1 p.2) := by
  have hr : MeasurableSet {p : ℝ × ℝ | region j p.1 p.2} := by
    cases j <;> unfold region lo hi <;> measurability
  apply Measurable.ite hr _ measurable_const
  have hv : Measurable (fun p : ℝ × ℝ => V j p.1 p.2) := by
    cases j <;> unfold V <;> fun_prop
  exact (hm.comp hv).mul (by unfold D; fun_prop)

theorem masked_measurable (j : Kind) :
    Measurable (fun p : ℝ × ℝ => masked j p.1 p.2) := by
  have hs : MeasurableSet {p : ℝ × ℝ | slice j p.1 p.2} := by
    cases j <;> unfold slice region lo hi invU <;>
      try unfold gamma5FeedbackW
    all_goals measurability
  apply Measurable.ite hs _ measurable_const
  cases j <;> unfold density invU <;> try unfold gamma5FeedbackW
  all_goals fun_prop

theorem source_support (j : Kind) (H : ℝ → ℝ) :
    Function.support (fun p : ℝ × ℝ => source j H p.1 p.2) ⊆ Icc a b ×ˢ Icc a f := by
  intro p hp
  have h : region j p.1 p.2 := by
    by_contra hn
    exact hp (if_neg hn)
  exact ⟨(region_bounds h).1, (region_bounds h).2.1⟩

theorem masked_support (j : Kind) :
    Function.support (fun p : ℝ × ℝ => masked j p.1 p.2) ⊆ Icc (1 : ℝ) 3 ×ˢ Icc a b := by
  intro p hp
  have h : slice j p.1 p.2 := by
    by_contra hn
    exact hp (if_neg hn)
  exact ⟨slice_unit h, (slice_bounds h).2.1⟩

theorem density_bound {j : Kind} {v t : ℝ} (h : slice j v t) :
    0 < density j v t ∧ density j v t ≤ 100 := by
  have hv : 1 ≤ v := (slice_unit h).1
  have ht : 1 / 10 ≤ t := constants.2.2.2.2.1.trans (slice_bounds h).2.1.1
  have hu : 1 / 10 ≤ invU j v t := constants.2.2.2.2.1.trans (slice_bounds h).2.2.1
  have htu := mul_le_mul ht hu (by norm_num) (by linarith : 0 ≤ t)
  have hd := mul_le_mul hv htu (by norm_num : (0 : ℝ) ≤ 1 / 10 * (1 / 10)) (by linarith)
  have hp : 0 < v * t * invU j v t := by nlinarith [hd]
  exact ⟨div_pos (by norm_num) hp, (div_le_iff₀ hp).mpr (by nlinarith [hd])⟩

theorem source_density_bound {j : Kind} {t u : ℝ} (h : region j t u) :
    0 < D t u ∧ D t u ≤ 400 := by
  have hb := region_bounds h
  have ht : 1 / 10 ≤ t := constants.2.2.2.2.1.trans hb.1.1
  have hu : 1 / 10 ≤ u := constants.2.2.2.2.1.trans hb.2.1.1
  have htu := mul_le_mul ht hu (by norm_num) (by linarith : 0 ≤ t)
  have hd := mul_le_mul htu hb.2.2.le (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by nlinarith : 0 ≤ t * u)
  have hp : 0 < t * u * (1 - t - u) := by nlinarith [hd]
  exact ⟨div_pos (by norm_num) hp, (div_le_iff₀ hp).mpr (by nlinarith [hd])⟩

theorem masked_bounds (j : Kind) (v t : ℝ) : 0 ≤ masked j v t ∧ masked j v t ≤ 100 := by
  by_cases h : slice j v t
  · rw [masked, if_pos h]
    exact ⟨(density_bound h).1.le, (density_bound h).2⟩
  · simp only [masked, if_neg h]
    norm_num

theorem source_bound (j : Kind) {H : ℝ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ v, |H v| ≤ M) (t u : ℝ) : ‖source j H t u‖ ≤ 400 * M := by
  by_cases h : region j t u
  · rw [source, if_pos h, Real.norm_eq_abs, abs_mul, abs_of_pos (source_density_bound h).1]
    exact (mul_le_mul (hb _) (source_density_bound h).2 (source_density_bound h).1.le hM).trans_eq (by ring)
  · rw [source, if_neg h, norm_zero]
    positivity

theorem weighted_bound (j : Kind) {H : ℝ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ v, |H v| ≤ M) (v t : ℝ) : ‖H v * masked j v t‖ ≤ 100 * M := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (masked_bounds j v t).1]
  exact (mul_le_mul (hb _) (masked_bounds j v t).2 (masked_bounds j v t).1 hM).trans_eq (by ring)

theorem source_integrable (j : Kind) {H : ℝ → ℝ} {M : ℝ}
    (hm : Measurable H) (hM : 0 ≤ M) (hb : ∀ v, |H v| ≤ M) :
    Integrable (fun p : ℝ × ℝ => source j H p.1 p.2) := by
  apply (integrableOn_iff_integrable_of_support_subset (source_support j H)).mp
  apply Measure.integrableOn_of_bounded (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
    (source_measurable j hm).aestronglyMeasurable (M := 400 * M)
  exact Filter.Eventually.of_forall (fun p => source_bound j hM hb p.1 p.2)

theorem source_row_integrable (j : Kind) {H : ℝ → ℝ} {M : ℝ}
    (hm : Measurable H) (hM : 0 ≤ M) (hb : ∀ v, |H v| ≤ M) (t : ℝ) :
    Integrable (source j H t) := by
  have hs : Function.support (source j H t) ⊆ Icc a f := by
    intro u hu
    exact (source_support j H (a := (t, u)) hu).2
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  apply Measure.integrableOn_of_bounded isCompact_Icc.measure_lt_top.ne
    ((source_measurable j hm).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (M := 400 * M)
  exact Filter.Eventually.of_forall (fun u => source_bound j hM hb t u)

theorem weighted_integrable (j : Kind) {H : ℝ → ℝ} {M : ℝ}
    (hm : Measurable H) (hM : 0 ≤ M) (hb : ∀ v, |H v| ≤ M) :
    Integrable (fun p : ℝ × ℝ => H p.1 * masked j p.1 p.2) := by
  have hs : Function.support (fun p : ℝ × ℝ => H p.1 * masked j p.1 p.2) ⊆
      Icc (1 : ℝ) 3 ×ˢ Icc a b := by
    intro p hp
    exact masked_support j (fun h => hp (by dsimp only at h ⊢; rw [h, mul_zero]))
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  apply Measure.integrableOn_of_bounded (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
    ((hm.comp measurable_fst).mul (masked_measurable j)).aestronglyMeasurable (M := 100 * M)
  exact Filter.Eventually.of_forall (fun p => weighted_bound j hM hb p.1 p.2)

theorem masked_row_integrable (j : Kind) (v : ℝ) : Integrable (masked j v) := by
  have hs : Function.support (masked j v) ⊆ Icc a b := by
    intro t ht
    exact (masked_support j (a := (v, t)) ht).2
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  apply Measure.integrableOn_of_bounded isCompact_Icc.measure_lt_top.ne
    ((masked_measurable j).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable (M := 100)
  exact Filter.Eventually.of_forall (fun t => by
    change ‖masked j v t‖ ≤ 100
    rw [Real.norm_eq_abs, abs_of_nonneg (masked_bounds j v t).1]
    exact (masked_bounds j v t).2)

end Wu2008DoubleSieve.Gamma678Feedback
