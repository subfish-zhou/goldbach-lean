import MathlibNt.Wu2008DoubleSieve.Gamma78GainPacking

namespace Wu2008DoubleSieve

open Set Real Filter MeasureTheory
open scoped Classical Topology Interval

noncomputable def gamma78GainLiteral (δ t u : ℝ) : ℝ :=
  wuImprovementLimit true δ (gamma78GainV t u) / (t*u*(1-t-u))

noncomputable def gamma78GainIntegral (tri : Bool) (δ : ℝ) : ℝ :=
  ∫ t in gamma5MassA..gamma6BaseB,
    ∫ u in gamma78GainStart tri t..gamma78GainUpper tri, gamma78GainLiteral δ t u

noncomputable def gamma78GainC (tri : Bool) : ℝ :=
  ∫ t in gamma5MassA..gamma6BaseB,
    ∫ u in gamma78GainStart tri t..gamma78GainUpper tri, gamma5MassKernel t u

noncomputable def gamma78GainKernel (tri : Bool) (δ : ℝ) : ℝ × ℝ → ℝ :=
  (gamma78GainRegion tri).indicator
    (fun v => gamma5GainH δ (gamma78GainV v.1 v.2) * gamma5GainSmooth v)

theorem gamma78Gain_start_bounds (tri : Bool) {t : ℝ}
    (ht : t ∈ Icc gamma5MassA gamma6BaseB) :
    t ≤ gamma78GainStart tri t ∧ gamma78GainStart tri t ≤ gamma78GainUpper tri := by
  cases tri <;> simp only [gamma78GainStart,gamma78GainUpper,Bool.false_eq_true,if_false,if_true]
  · exact ⟨ht.2,(gamma78Gain_constants false).2.1.le⟩
  · exact ⟨le_rfl,ht.2⟩

theorem gamma78Gain_region_measurable (tri : Bool) : MeasurableSet (gamma78GainRegion tri) := by
  have hs : Continuous (gamma78GainStart tri) := by cases tri <;> exact continuous_const <|> exact continuous_id
  exact (isClosed_le continuous_const continuous_fst).measurableSet.inter
    (isClosed_le continuous_fst continuous_const).measurableSet |>.inter
      ((isClosed_le (hs.comp continuous_fst) continuous_snd).measurableSet.inter
        (isClosed_le continuous_snd continuous_const).measurableSet)

theorem gamma78Gain_region_unit {tri : Bool} {v : ℝ × ℝ} (hv : v ∈ gamma78GainRegion tri) :
    v ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
  have h := gamma78Gain_region_bounds hv
  exact ⟨⟨h.2.2.1.le,h.2.2.2.2.1.le⟩,⟨h.2.2.2.1.le,h.2.2.2.2.2.1.le⟩⟩

theorem gamma78Gain_H_pullback_ae {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∀ᵐ v : ℝ × ℝ, ContinuousAt (gamma5GainH δ) (gamma78GainV v.1 v.2) := by
  let g := fun s => -gamma5GainH δ s
  have hg : Monotone g := (gamma5Gain_H_antitone hδ hδhi).neg
  have hcount := hg.countable_not_continuousAt
  have hv : Measurable (fun v : ℝ × ℝ => gamma78GainV v.1 v.2) := by
    unfold gamma78GainV
    fun_prop
  have hm := (measurableSet_of_continuousAt g).preimage hv
  have hae : ∀ᵐ v : ℝ × ℝ, ContinuousAt g (gamma78GainV v.1 v.2) := by
    change ∀ᵐ v : ℝ × ℝ ∂(volume.prod volume), ContinuousAt g (gamma78GainV v.1 v.2)
    rw [Measure.ae_prod_iff_ae_ae hm]
    filter_upwards [show ∀ᵐ t : ℝ, t ≠ 0 from ae_iff.mpr (Set.countable_singleton 0).measure_zero]
      with t ht
    have hinj : Function.Injective (fun u => gamma78GainV t u) := by
      intro u w he
      have hh := (div_left_inj' ht).mp he
      linarith
    exact ae_iff.mpr ((hcount.preimage hinj).measure_zero volume)
  filter_upwards [hae] with v hc
  simpa only [g,neg_neg] using hc.neg

theorem gamma78Gain_ratio_level_line {t u r : ℝ} (ht : t ≠ 0) :
    gamma78GainV t u = r ↔ (r+1)*t+u=1 := by
  rw [gamma78GainV,div_eq_iff ht]
  constructor <;> intro h <;> nlinarith

theorem gamma78Gain_kernel_measurable {δ : ℝ} (tri : Bool) (hδ : 0 < δ) (hδhi : δ < 1/2) :
    Measurable (gamma78GainKernel tri δ) := by
  have hv : Measurable (fun v : ℝ × ℝ => gamma78GainV v.1 v.2) := by
    unfold gamma78GainV
    fun_prop
  exact (((gamma5Gain_H_antitone hδ hδhi).measurable.comp hv).mul
    gamma5Gain_smooth_continuous.measurable).indicator (gamma78Gain_region_measurable tri)

theorem gamma78Gain_kernel_bounds {δ : ℝ} (tri : Bool) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (v : ℝ × ℝ) : 0 ≤ gamma78GainKernel tri δ v ∧ gamma78GainKernel tri δ v ≤ 400 := by
  by_cases hv : v ∈ gamma78GainRegion tri
  · rw [gamma78GainKernel,Set.indicator_of_mem hv]
    have hh := gamma5Gain_H_bounds hδ hδhi (gamma78GainV v.1 v.2)
    have hk := gamma5Gain_smooth_bounds v
    exact ⟨mul_nonneg hh.1 hk.1,(mul_le_mul hh.2 hk.2 hk.1 (by norm_num)).trans_eq (by norm_num)⟩
  · rw [gamma78GainKernel,Set.indicator_of_notMem hv]
    norm_num

theorem gamma78Gain_kernel_integrable {δ : ℝ} (tri : Bool) (hδ : 0 < δ) (hδhi : δ < 1/2) :
    Integrable (gamma78GainKernel tri δ) := by
  have hs : Function.support (gamma78GainKernel tri δ) ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    intro v hv
    by_contra hn
    exact hv (Set.indicator_of_notMem (fun h => hn (gamma78Gain_region_unit h)) _)
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  apply Measure.integrableOn_of_bounded
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
    (gamma78Gain_kernel_measurable tri hδ hδhi).aestronglyMeasurable
  exact Eventually.of_forall (fun v => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (gamma78Gain_kernel_bounds tri hδ hδhi v).1]
      using (gamma78Gain_kernel_bounds tri hδ hδhi v).2)

theorem gamma78Gain_slice_support (tri : Bool) (δ t : ℝ) :
    Function.support (fun u => gamma78GainKernel tri δ (t,u)) ⊆
      Icc (gamma78GainStart tri t) (gamma78GainUpper tri) := by
  intro u hu
  by_contra hn
  exact hu (Set.indicator_of_notMem (show (t,u) ∉ gamma78GainRegion tri from fun h => hn h.2) _)

theorem gamma78Gain_slice_integrable {δ : ℝ} (tri : Bool) (hδ : 0 < δ) (hδhi : δ < 1/2) (t : ℝ) :
    Integrable (fun u => gamma78GainKernel tri δ (t,u)) := by
  apply (integrableOn_iff_integrable_of_support_subset (gamma78Gain_slice_support tri δ t)).mp
  apply Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
    ((gamma78Gain_kernel_measurable tri hδ hδhi).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact Eventually.of_forall (fun u => by
    simpa only [Function.comp_def,id_eq,Real.norm_eq_abs,
      abs_of_nonneg (gamma78Gain_kernel_bounds tri hδ hδhi (t,u)).1]
      using (gamma78Gain_kernel_bounds tri hδ hδhi (t,u)).2)

theorem gamma78Gain_kernel_eq_literal {tri : Bool} {δ t u : ℝ}
    (hv : (t,u) ∈ gamma78GainRegion tri) :
    gamma78GainKernel tri δ (t,u) = gamma78GainLiteral δ t u := by
  have hb := gamma78Gain_region_bounds hv
  have hxy := gamma5Gain_triangle_bounds hb.1
  rw [gamma78GainKernel,Set.indicator_of_mem hv,gamma5GainH,
    gamma5Gain_clip_eq ⟨hb.2.2.2.2.2.2.2.2.1.le,hb.2.2.2.2.2.2.2.2.2.le⟩,
    gamma5Gain_smooth_eq hxy.1 hxy.2.1]
  exact mul_one_div _ _

theorem gamma78Gain_inner_integrable {δ t : ℝ} (tri : Bool)
    (hδ : 0 < δ) (hδhi : δ < 1/2) (ht : t ∈ Icc gamma5MassA gamma6BaseB) :
    IntervalIntegrable (gamma78GainLiteral δ t) volume (gamma78GainStart tri t) (gamma78GainUpper tri) := by
  apply (gamma78Gain_slice_integrable tri hδ hδhi t).intervalIntegrable.congr
  intro u hu
  exact gamma78Gain_kernel_eq_literal ⟨ht,by
    simpa only [uIcc_of_le (gamma78Gain_start_bounds tri ht).2] using uIoc_subset_uIcc hu⟩

theorem gamma78Gain_inner_eq {δ t : ℝ} (tri : Bool) (ht : t ∈ Icc gamma5MassA gamma6BaseB) :
    (∫ u, gamma78GainKernel tri δ (t,u)) =
      ∫ u in gamma78GainStart tri t..gamma78GainUpper tri, gamma78GainLiteral δ t u := by
  rw [truncatedSixthMass_integral_eq_interval (gamma78Gain_start_bounds tri ht).2
    (gamma78Gain_slice_support tri δ t)]
  apply intervalIntegral.integral_congr
  intro u hu
  exact gamma78Gain_kernel_eq_literal ⟨ht,by
    simpa only [uIcc_of_le (gamma78Gain_start_bounds tri ht).2] using hu⟩

theorem gamma78Gain_outer_integrable {δ : ℝ} (tri : Bool) (hδ : 0 < δ) (hδhi : δ < 1/2) :
    IntervalIntegrable
      (fun t => ∫ u in gamma78GainStart tri t..gamma78GainUpper tri, gamma78GainLiteral δ t u)
      volume gamma5MassA gamma6BaseB := by
  apply (gamma78Gain_kernel_integrable tri hδ hδhi).integral_prod_left.intervalIntegrable.congr
  intro t ht
  exact gamma78Gain_inner_eq tri
    (by simpa only [uIcc_of_le (gamma78Gain_constants tri).1.le] using uIoc_subset_uIcc ht)

theorem gamma78Gain_integral_eq {δ : ℝ} (tri : Bool) (hδ : 0 < δ) (hδhi : δ < 1/2) :
    gamma78GainIntegral tri δ = ∫ v : ℝ × ℝ, gamma78GainKernel tri δ v := by
  have hs : Function.support (fun t => ∫ u, gamma78GainKernel tri δ (t,u)) ⊆
      Icc gamma5MassA gamma6BaseB := by
    intro t ht
    by_contra hn
    apply ht
    change (∫ u, gamma78GainKernel tri δ (t,u)) = 0
    have he : (fun u => gamma78GainKernel tri δ (t,u)) = 0 := by
      funext u
      exact Set.indicator_of_notMem (show (t,u) ∉ gamma78GainRegion tri from fun h => hn h.1) _
    rw [he]
    simp
  rw [show (∫ v : ℝ × ℝ, gamma78GainKernel tri δ v) =
      ∫ t, ∫ u, gamma78GainKernel tri δ (t,u) from integral_prod _ (gamma78Gain_kernel_integrable tri hδ hδhi),
    truncatedSixthMass_integral_eq_interval (gamma78Gain_constants tri).1.le hs]
  symm
  apply intervalIntegral.integral_congr
  intro t ht
  exact gamma78Gain_inner_eq tri
    (by simpa only [uIcc_of_le (gamma78Gain_constants tri).1.le] using ht)

theorem gamma78Gain_C_inner_integrable (tri : Bool) {t : ℝ} (ht : t ∈ Icc gamma5MassA gamma6BaseB) :
    IntervalIntegrable (gamma5MassKernel t) volume (gamma78GainStart tri t) (gamma78GainUpper tri) := by
  apply (gamma5Gain_smooth_continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable.congr
  intro u hu
  have hreg : (t,u) ∈ gamma78GainRegion tri := ⟨ht,by
    simpa only [uIcc_of_le (gamma78Gain_start_bounds tri ht).2] using uIoc_subset_uIcc hu⟩
  have hh := gamma5Gain_triangle_bounds (gamma78Gain_region_bounds hreg).1
  exact gamma5Gain_smooth_eq hh.1 hh.2.1

theorem gamma78Gain_C_outer_integrable (tri : Bool) :
    IntervalIntegrable
      (fun t => ∫ u in gamma78GainStart tri t..gamma78GainUpper tri, gamma5MassKernel t u)
      volume gamma5MassA gamma6BaseB := by
  have hs : Continuous (gamma78GainStart tri) := by cases tri <;> exact continuous_const <|> exact continuous_id
  apply (gamma5Gain_moving_integral gamma5Gain_smooth_continuous hs continuous_const).intervalIntegrable.congr
  intro t ht
  have ht' : t ∈ Icc gamma5MassA gamma6BaseB := by
    simpa only [uIcc_of_le (gamma78Gain_constants tri).1.le] using uIoc_subset_uIcc ht
  apply intervalIntegral.integral_congr
  intro u hu
  have hreg : (t,u) ∈ gamma78GainRegion tri := ⟨ht',by
    simpa only [uIcc_of_le (gamma78Gain_start_bounds tri ht').2] using hu⟩
  have hh := gamma5Gain_triangle_bounds (gamma78Gain_region_bounds hreg).1
  exact gamma5Gain_smooth_eq hh.1 hh.2.1

theorem gamma78Gain_integral_bounds {δ : ℝ} (tri : Bool) (hδ : 0 < δ) (hδhi : δ < 1/2) :
    0 ≤ gamma78GainIntegral tri δ ∧ gamma78GainIntegral tri δ ≤ gamma78GainC tri := by
  constructor
  · rw [gamma78Gain_integral_eq tri hδ hδhi]
    exact integral_nonneg (fun v => (gamma78Gain_kernel_bounds tri hδ hδhi v).1)
  · apply intervalIntegral.integral_mono_on (gamma78Gain_constants tri).1.le
      (gamma78Gain_outer_integrable tri hδ hδhi) (gamma78Gain_C_outer_integrable tri)
    intro t ht
    apply intervalIntegral.integral_mono_on (gamma78Gain_start_bounds tri ht).2
      (gamma78Gain_inner_integrable tri hδ hδhi ht) (gamma78Gain_C_inner_integrable tri ht)
    intro u hu
    have hv : (t,u) ∈ gamma78GainRegion tri := ⟨ht,hu⟩
    have hh := gamma5Gain_triangle_bounds (gamma78Gain_region_bounds hv).1
    rw [← gamma78Gain_kernel_eq_literal hv,gamma78GainKernel,Set.indicator_of_mem hv,
      ← gamma5Gain_smooth_eq hh.1 hh.2.1]
    exact (mul_le_mul_of_nonneg_right (gamma5Gain_H_bounds hδ hδhi _).2
      (gamma5Gain_smooth_bounds _).1).trans_eq (one_mul _)

theorem gamma78Gain_C_rectangle (tri : Bool) :
    gamma5MassRectangleIntegral gamma5MassA gamma6BaseB (gamma78GainLower tri)
      (gamma78GainUpper tri) = gamma78GainC tri := by
  unfold gamma5MassRectangleIntegral gamma78GainC
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc gamma5MassA gamma6BaseB := by
    simpa only [uIcc_of_le (gamma78Gain_constants tri).1.le] using ht
  cases tri
  · simp only [gamma78GainLower,gamma78GainUpper,gamma78GainStart,Bool.false_eq_true,if_false,
      gamma5MassSectionStart,max_eq_left ht'.2,min_eq_right (gamma78Gain_constants false).2.1.le]
  · simp only [gamma78GainLower,gamma78GainUpper,gamma78GainStart,if_true,
      gamma5MassSectionStart,max_eq_right ht'.1,min_eq_right ht'.2]

end Wu2008DoubleSieve
