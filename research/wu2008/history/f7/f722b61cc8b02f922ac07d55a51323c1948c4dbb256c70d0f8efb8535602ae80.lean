import MathlibNt.Wu2008DoubleSieve.Gamma6GainGeometry

namespace Wu2008DoubleSieve

open Set Real Filter MeasureTheory
open scoped Classical Topology Interval

def gamma6GainRegion : Set (ℝ × ℝ) :=
  Icc gamma5MassA gamma6BaseB ×ˢ Icc gamma6BaseC gamma6BaseF

noncomputable def gamma6GainLiteral (δ t u : ℝ) : ℝ :=
  wuImprovementLimit true δ (gamma5GainV t u) / (t * u * (1 - t - u))

noncomputable def gamma6GainIntegral (δ : ℝ) : ℝ :=
  ∫ t in gamma5MassA..gamma6BaseB, ∫ u in gamma6BaseC..gamma6BaseF, gamma6GainLiteral δ t u

noncomputable def gamma6GainKernel (δ : ℝ) : ℝ × ℝ → ℝ :=
  gamma6GainRegion.indicator (fun v => gamma5GainH δ (gamma5GainV v.1 v.2) * gamma5GainSmooth v)

/-- The old smooth extension also equals K here: only the sum of the
coordinates, not the old individual upper cap, enters its last clamp. -/
theorem gamma6Gain_smooth_eq {t u : ℝ}
    (ht : t ∈ Icc gamma5MassA gamma6BaseB) (hu : u ∈ Icc gamma6BaseC gamma6BaseF) :
    gamma5GainSmooth (t, u) = gamma5MassKernel t u := by
  have hca : gamma5MassA ≤ gamma6BaseC := by
    norm_num [gamma5MassA, gamma5ClassicalS, gamma6BaseC]
  have hsum : gamma6BaseB + gamma6BaseF ≤ 2 * gamma5ClassicalB := by
    norm_num [gamma6BaseB, gamma6BaseF, gamma5ClassicalB]
  simp only [gamma5GainSmooth, gamma5MassKernel, max_eq_right ht.1,
    max_eq_right (hca.trans hu.1),
    max_eq_right (show 1 - 2 * gamma5ClassicalB ≤ 1 - t - u by linarith [ht.2, hu.2])]

theorem gamma6Gain_smooth_rectangle_eq {A B C D : ℝ}
    (hA : gamma5MassA ≤ A) (hAB : A ≤ B) (hB : B ≤ gamma6BaseB)
    (hC : gamma6BaseC ≤ C) (hCD : C ≤ D) (hD : D ≤ gamma6BaseF) :
    gamma5GainSmoothRectangle A B C D = gamma6BaseIntegral A B C D := by
  unfold gamma5GainSmoothRectangle gamma6BaseIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc A B := by simpa only [uIcc_of_le hAB] using ht
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u ∈ Icc C D := by simpa only [uIcc_of_le hCD] using hu
  exact gamma6Gain_smooth_eq ⟨hA.trans ht'.1, ht'.2.trans hB⟩ ⟨hC.trans hu'.1, hu'.2.trans hD⟩

theorem gamma6Gain_kernel_measurable {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    Measurable (gamma6GainKernel δ) := by
  have hv : Measurable (fun v : ℝ × ℝ => gamma5GainV v.1 v.2) := by
    unfold gamma5GainV
    fun_prop
  exact (((gamma5Gain_H_antitone hδ hδhi).measurable.comp hv).mul
    gamma5Gain_smooth_continuous.measurable).indicator (measurableSet_Icc.prod measurableSet_Icc)

theorem gamma6Gain_kernel_bounds {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) (v : ℝ × ℝ) :
    0 ≤ gamma6GainKernel δ v ∧ gamma6GainKernel δ v ≤ 400 := by
  by_cases hv : v ∈ gamma6GainRegion
  · rw [gamma6GainKernel, Set.indicator_of_mem hv]
    have hh := gamma5Gain_H_bounds hδ hδhi (gamma5GainV v.1 v.2)
    have hs := gamma5Gain_smooth_bounds v
    exact ⟨mul_nonneg hh.1 hs.1,
      (mul_le_mul hh.2 hs.2 hs.1 (by norm_num)).trans_eq (by norm_num)⟩
  · rw [gamma6GainKernel, Set.indicator_of_notMem hv]
    norm_num

theorem gamma6Gain_kernel_integrable {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    Integrable (gamma6GainKernel δ) := by
  have hs : Function.support (gamma6GainKernel δ) ⊆ gamma6GainRegion :=
    Function.support_indicator_subset_left _ _
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  apply Measure.integrableOn_of_bounded
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
    (gamma6Gain_kernel_measurable hδ hδhi).aestronglyMeasurable
  exact Eventually.of_forall (fun v => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (gamma6Gain_kernel_bounds hδ hδhi v).1]
      using (gamma6Gain_kernel_bounds hδ hδhi v).2)

theorem gamma6Gain_slice_integrable {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) (t : ℝ) :
    Integrable (fun u => gamma6GainKernel δ (t, u)) := by
  have hs : Function.support (fun u => gamma6GainKernel δ (t, u)) ⊆
      Icc gamma6BaseC gamma6BaseF := by
    intro u hu
    by_contra hn
    exact hu (Set.indicator_of_notMem (show (t,u) ∉ gamma6GainRegion from fun h => hn h.2) _)
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  apply Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
    ((gamma6Gain_kernel_measurable hδ hδhi).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact Eventually.of_forall (fun u => by
    simpa only [Function.comp_def, id_eq, Real.norm_eq_abs,
      abs_of_nonneg (gamma6Gain_kernel_bounds hδ hδhi (t, u)).1]
      using (gamma6Gain_kernel_bounds hδ hδhi (t, u)).2)

theorem gamma6Gain_kernel_eq_literal {δ t u : ℝ}
    (ht : t ∈ Icc gamma5MassA gamma6BaseB) (hu : u ∈ Icc gamma6BaseC gamma6BaseF) :
    gamma6GainKernel δ (t,u) = gamma6GainLiteral δ t u := by
  have hb := gamma6Gain_domain_bounds ht hu
  have hv : gamma5GainV t u ∈ Icc 1 3 :=
    ⟨hb.2.2.2.2.2.2.2.1.le, by linarith [hb.2.2.2.2.2.2.2.2.1]⟩
  rw [gamma6GainKernel, Set.indicator_of_mem (show (t,u) ∈ gamma6GainRegion from ⟨ht,hu⟩),
    gamma5GainH, gamma5Gain_clip_eq hv, gamma6Gain_smooth_eq ht hu]
  exact mul_one_div _ _

theorem gamma6Gain_inner_integrable {δ t : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (ht : t ∈ Icc gamma5MassA gamma6BaseB) :
    IntervalIntegrable (gamma6GainLiteral δ t) volume gamma6BaseC gamma6BaseF := by
  apply (gamma6Gain_slice_integrable hδ hδhi t).intervalIntegrable.congr
  intro u hu
  exact gamma6Gain_kernel_eq_literal ht
    (by simpa only [uIcc_of_le gamma6Base_constants.2.2.2.1.le] using uIoc_subset_uIcc hu)

theorem gamma6Gain_inner_eq {δ t : ℝ} (ht : t ∈ Icc gamma5MassA gamma6BaseB) :
    (∫ u, gamma6GainKernel δ (t,u)) =
      ∫ u in gamma6BaseC..gamma6BaseF, gamma6GainLiteral δ t u := by
  have hs : Function.support (fun u => gamma6GainKernel δ (t,u)) ⊆ Icc gamma6BaseC gamma6BaseF := by
    intro u hu
    by_contra hn
    exact hu (Set.indicator_of_notMem (show (t,u) ∉ gamma6GainRegion from fun h => hn h.2) _)
  rw [truncatedSixthMass_integral_eq_interval gamma6Base_constants.2.2.2.1.le hs]
  apply intervalIntegral.integral_congr
  intro u hu
  exact gamma6Gain_kernel_eq_literal ht
    (by simpa only [uIcc_of_le gamma6Base_constants.2.2.2.1.le] using hu)

theorem gamma6Gain_outer_integrable {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    IntervalIntegrable (fun t => ∫ u in gamma6BaseC..gamma6BaseF, gamma6GainLiteral δ t u)
      volume gamma5MassA gamma6BaseB := by
  apply (gamma6Gain_kernel_integrable hδ hδhi).integral_prod_left.intervalIntegrable.congr
  intro t ht
  exact gamma6Gain_inner_eq
    (by simpa only [uIcc_of_le gamma6Base_constants.2.1.le] using uIoc_subset_uIcc ht)

theorem gamma6Gain_integral_eq {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    gamma6GainIntegral δ = ∫ v : ℝ × ℝ, gamma6GainKernel δ v := by
  have hs : Function.support (fun t => ∫ u, gamma6GainKernel δ (t,u)) ⊆
      Icc gamma5MassA gamma6BaseB := by
    intro t ht
    by_contra hn
    apply ht
    have he : (fun u => gamma6GainKernel δ (t,u)) = 0 := by
      funext u
      exact Set.indicator_of_notMem (show (t,u) ∉ gamma6GainRegion from fun h => hn h.1) _
    rw [he]
    simp
  rw [show (∫ v : ℝ × ℝ, gamma6GainKernel δ v) = ∫ t, ∫ u, gamma6GainKernel δ (t,u) from
      integral_prod _ (gamma6Gain_kernel_integrable hδ hδhi),
    truncatedSixthMass_integral_eq_interval gamma6Base_constants.2.1.le hs]
  symm
  apply intervalIntegral.integral_congr
  intro t ht
  exact gamma6Gain_inner_eq (by simpa only [uIcc_of_le gamma6Base_constants.2.1.le] using ht)

theorem gamma6Gain_integral_bounds {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    0 ≤ gamma6GainIntegral δ ∧ gamma6GainIntegral δ ≤ gamma6BaseC6 := by
  constructor
  · rw [gamma6Gain_integral_eq hδ hδhi]
    exact integral_nonneg (fun v => (gamma6Gain_kernel_bounds hδ hδhi v).1)
  · apply intervalIntegral.integral_mono_on gamma6Base_constants.2.1.le
      (gamma6Gain_outer_integrable hδ hδhi)
      (gamma6Base_outer_integrable le_rfl gamma6Base_constants.2.1.le le_rfl le_rfl
        gamma6Base_constants.2.2.2.1.le le_rfl)
    intro t ht
    apply intervalIntegral.integral_mono_on gamma6Base_constants.2.2.2.1.le
      (gamma6Gain_inner_integrable hδ hδhi ht)
      (gamma6Base_inner_integrable ht.1 ht.2 le_rfl gamma6Base_constants.2.2.2.1.le le_rfl)
    intro u hu
    rw [← gamma6Gain_kernel_eq_literal ht hu, gamma6GainKernel,
      Set.indicator_of_mem (show (t,u) ∈ gamma6GainRegion from ⟨ht,hu⟩),
      ← gamma6Gain_smooth_eq ht hu]
    exact (mul_le_mul_of_nonneg_right (gamma5Gain_H_bounds hδ hδhi _).2
      (gamma5Gain_smooth_bounds _).1).trans_eq (one_mul _)

theorem gamma6Gain_rectangle_inner_approx (r : Gamma6GainRectangle) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ r.A + τ < r.B - τ ∧ r.C + τ < r.D - τ ∧
      gamma6BaseIntegral r.A r.B r.C r.D - ε <
        gamma6BaseIntegral (r.A + τ) (r.B - τ) (r.C + τ) (r.D - τ) := by
  have ht : Tendsto (fun τ : ℝ =>
      gamma5GainSmoothRectangle (r.A + τ) (r.B - τ) (r.C + τ) (r.D - τ))
      (𝓝 0) (𝓝 (gamma5GainSmoothRectangle r.A r.B r.C r.D)) := by
    have hc : Continuous (fun τ : ℝ => (r.A + τ, r.B - τ, r.C + τ, r.D - τ)) := by fun_prop
    simpa only [Function.comp_def, add_zero, sub_zero] using
      (gamma5Gain_smooth_rectangle_continuous.comp hc).continuousAt.tendsto (x := (0 : ℝ))
  have he := ht.eventually (lt_mem_nhds (sub_lt_self _ hε))
  have hab : ∀ᶠ τ : ℝ in 𝓝 0, r.A + τ < r.B - τ :=
    (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds (by simpa using r.first)
  have hcd : ∀ᶠ τ : ℝ in 𝓝 0, r.C + τ < r.D - τ :=
    (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds (by simpa using r.second)
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp (hab.and (hcd.and he))
  let τ := ρ / 2
  have hτ : 0 < τ := half_pos hρ
  obtain ⟨hA, hC, hI⟩ := hball (show dist τ 0 < ρ by
    rw [Real.dist_eq, sub_zero, abs_of_pos hτ]
    dsimp [τ]
    linarith)
  refine ⟨τ, hτ, hA, hC, ?_⟩
  rw [gamma6Gain_smooth_rectangle_eq r.lower.le r.first.le r.firstUpper.le
      r.secondLower.le r.second.le r.upper.le,
    gamma6Gain_smooth_rectangle_eq (by linarith [r.lower]) hA.le
      (by linarith [r.firstUpper]) (by linarith [r.secondLower]) hC.le (by linarith [r.upper])] at hI
  exact hI

end Wu2008DoubleSieve
