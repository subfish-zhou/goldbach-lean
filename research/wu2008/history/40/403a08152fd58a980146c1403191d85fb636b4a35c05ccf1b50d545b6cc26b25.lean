import MathlibNt.Wu2008DoubleSieve.Gamma78GainIntegral

namespace Wu2008DoubleSieve

open Finset Set Real Filter MeasureTheory
open scoped Classical Topology

noncomputable def gamma78GainSample (n : ℕ) (j : ℕ × ℕ) : ℝ :=
  gamma78GainV (truncatedSixthClosureLo n j.1) (truncatedSixthClosureLo n j.2) +
    1/((n+1 : ℕ) : ℝ)

noncomputable def gamma78GainInner (tri : Bool) (n : ℕ) : Finset (ℕ × ℕ) :=
  (truncatedSixthClosureCells n).filter (fun j =>
    gamma5MassA < truncatedSixthClosureLo n j.1 ∧
    truncatedSixthClosureHi n j.1 < gamma6BaseB ∧
    truncatedSixthClosureHi n j.1 < truncatedSixthClosureLo n j.2 ∧
    gamma78GainLower tri < truncatedSixthClosureLo n j.2 ∧
    truncatedSixthClosureHi n j.2 < gamma78GainUpper tri ∧ gamma78GainSample n j < 3)

noncomputable def gamma78GainInnerRectangle (tri : Bool) (n : ℕ)
    (j : {j // j ∈ gamma78GainInner tri n}) : Gamma78GainRectangle tri where
  box := {
    A := truncatedSixthClosureLo n j.val.1
    B := truncatedSixthClosureHi n j.val.1
    C := truncatedSixthClosureLo n j.val.2
    D := truncatedSixthClosureHi n j.val.2
    s := 5/2
    lower := (mem_filter.mp j.property).2.1
    first := truncatedSixthClosure_lo_lt_hi _ _
    ordered := (mem_filter.mp j.property).2.2.2.1
    second := truncatedSixthClosure_lo_lt_hi _ _
    upper := (mem_filter.mp j.property).2.2.2.2.2.1.trans_le
      (gamma78Gain_constants tri).2.2.2.2.2
    legal := by
      have hb := (mem_filter.mp j.property).2.2.1
      have hd := (mem_filter.mp j.property).2.2.2.2.2.1.trans_le
        (gamma78Gain_constants tri).2.2.2.2.2
      norm_num [gamma6BaseB,gamma5ClassicalB] at hb hd
      linarith
    rightEnd := by
      have ha := (mem_filter.mp j.property).2.1
      have hca : gamma5MassA < truncatedSixthClosureLo n j.val.2 :=
        ha.trans ((truncatedSixthClosure_lo_lt_hi _ _).trans (mem_filter.mp j.property).2.2.2.1)
      dsimp [gamma5GainV]
      norm_num [gamma5MassA,gamma5ClassicalS] at ha hca ⊢
      linarith
    parameter := by norm_num }
  firstUpper := (mem_filter.mp j.property).2.2.1
  secondLower := (mem_filter.mp j.property).2.2.2.2.1
  upper := (mem_filter.mp j.property).2.2.2.2.2.1
  s := gamma78GainSample n j.val
  rightEnd := lt_add_of_pos_right _ (by positivity)
  parameter := (mem_filter.mp j.property).2.2.2.2.2.2

noncomputable def gamma78GainApprox (tri : Bool) (δ : ℝ) (n : ℕ) (v : ℝ × ℝ) : ℝ :=
  ∑ j ∈ gamma78GainInner tri n, (truncatedSixthClosureCell n j).indicator
    (fun v => gamma5GainH δ (gamma78GainSample n j) * gamma5GainSmooth v) v

theorem gamma78Gain_inner_subset {tri : Bool} {n : ℕ} {j : ℕ × ℕ}
    (hj : j ∈ gamma78GainInner tri n) :
    truncatedSixthClosureCell n j ⊆ gamma78GainRegion tri := by
  let r := gamma78GainInnerRectangle tri n ⟨j,hj⟩
  intro v hv
  change v.1 ∈ Ico r.box.A r.box.B ∧ v.2 ∈ Ico r.box.C r.box.D at hv
  refine ⟨⟨r.box.lower.le.trans hv.1.1,hv.1.2.le.trans r.firstUpper.le⟩,?_,
    hv.2.2.le.trans r.upper.le⟩
  cases tri
  · exact r.secondLower.le.trans hv.2.1
  · exact hv.1.2.le.trans (r.box.ordered.le.trans hv.2.1)

theorem gamma78Gain_approx_at_cell {tri : Bool} {δ : ℝ} {n : ℕ} {j : ℕ × ℕ} {v : ℝ × ℝ}
    (hj : j ∈ gamma78GainInner tri n) (hv : v ∈ truncatedSixthClosureCell n j) :
    gamma78GainApprox tri δ n v = gamma5GainH δ (gamma78GainSample n j) * gamma5GainSmooth v := by
  unfold gamma78GainApprox
  rw [sum_eq_single j]
  · exact Set.indicator_of_mem hv _
  · intro l _ hlj
    exact Set.indicator_of_notMem (fun hl => hlj (truncatedSixthClosure_cell_unique hl hv)) _
  · exact fun hn => False.elim (hn hj)

theorem gamma78Gain_approx_zero {tri : Bool} {δ : ℝ} {n : ℕ} {v : ℝ × ℝ}
    (h : ∀ j ∈ gamma78GainInner tri n, v ∉ truncatedSixthClosureCell n j) :
    gamma78GainApprox tri δ n v = 0 :=
  sum_eq_zero (fun j hj => Set.indicator_of_notMem (h j hj) _)

theorem gamma78Gain_approx_measurable (tri : Bool) (δ : ℝ) (n : ℕ) :
    Measurable (gamma78GainApprox tri δ n) := by
  apply Finset.measurable_sum
  intro j _
  exact (measurable_const.mul gamma5Gain_smooth_continuous.measurable).indicator
    (truncatedSixthClosure_cell_measurable n j)

theorem gamma78Gain_approx_bound {δ : ℝ} (tri : Bool) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (n : ℕ) (v : ℝ × ℝ) :
    ‖gamma78GainApprox tri δ n v‖ ≤
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1).indicator (fun _ => (400 : ℝ)) v := by
  by_cases hex : ∃ j ∈ gamma78GainInner tri n, v ∈ truncatedSixthClosureCell n j
  · obtain ⟨j,hj,hv⟩ := hex
    rw [gamma78Gain_approx_at_cell hj hv,Set.indicator_of_mem
      (gamma78Gain_region_unit (gamma78Gain_inner_subset hj hv))]
    have hh := gamma5Gain_H_bounds hδ hδhi (gamma78GainSample n j)
    have hk := gamma5Gain_smooth_bounds v
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hh.1 hk.1)]
    nlinarith [mul_le_mul hh.2 hk.2 hk.1 (by norm_num : (0 : ℝ) ≤ 1)]
  · rw [gamma78Gain_approx_zero (by simpa only [not_exists,not_and] using hex),norm_zero]
    exact Set.indicator_nonneg (fun _ _ => by norm_num) _

theorem gamma78Gain_strict_ae (tri : Bool) :
    ∀ᵐ v : ℝ × ℝ, v ∈ gamma78GainRegion tri →
      gamma5MassA < v.1 ∧ v.1 < gamma6BaseB ∧ v.1 < v.2 ∧
      gamma78GainLower tri < v.2 ∧ v.2 < gamma78GainUpper tri := by
  filter_upwards [gamma5Gain_vertical_ne_ae gamma5MassA,
    gamma5Gain_vertical_ne_ae gamma6BaseB,
    gamma5Gain_affine_ne_ae 1 (-1) 0 (by norm_num),
    gamma5Gain_affine_ne_ae 0 1 (gamma78GainLower tri) (by norm_num),
    gamma5Gain_affine_ne_ae 0 1 (gamma78GainUpper tri) (by norm_num)] with v ha hb hdiag hc hd
  intro hv
  simp only [zero_mul,one_mul,zero_add,neg_one_mul] at hdiag hc hd
  have ht := (gamma78Gain_region_bounds hv).1.2.1
  have hlu : gamma78GainLower tri ≤ v.2 := by
    cases tri
    · exact hv.2.1
    · exact hv.1.1.trans ht
  refine ⟨lt_of_le_of_ne hv.1.1 ha.symm,lt_of_le_of_ne hv.1.2 hb,?_,
    lt_of_le_of_ne hlu hc.symm,lt_of_le_of_ne hv.2.2 hd⟩
  by_contra hn
  have he : v.1=v.2 := le_antisymm ht (le_of_not_gt hn)
  exact hdiag (by rw [he]; ring)

theorem gamma78Gain_sample_tendsto {v : ℝ × ℝ} (ht : 0 < v.1) (hu : 0 ≤ v.2) :
    Tendsto (fun n => gamma78GainSample n
      (truncatedSixthClosureIndex n v.1,truncatedSixthClosureIndex n v.2))
      atTop (𝓝 (gamma78GainV v.1 v.2)) := by
  have hx := (truncatedSixthClosure_corner_tendsto ht.le).1
  have hy := (truncatedSixthClosure_corner_tendsto hu).1
  have he : Tendsto (fun n : ℕ => 1/((n+1 : ℕ) : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    by simpa only [Nat.cast_add,Nat.cast_one] using tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [gamma78GainSample,gamma78GainV,add_zero] using
    (((tendsto_const_nhds.sub hx).sub hy).div hx ht.ne').add he

theorem gamma78Gain_approx_tendsto {tri : Bool} {δ : ℝ} {v : ℝ × ℝ}
    (hstrict : v ∈ gamma78GainRegion tri →
      gamma5MassA < v.1 ∧ v.1 < gamma6BaseB ∧ v.1 < v.2 ∧
      gamma78GainLower tri < v.2 ∧ v.2 < gamma78GainUpper tri)
    (hc : ContinuousAt (gamma5GainH δ) (gamma78GainV v.1 v.2)) :
    Tendsto (fun n => gamma78GainApprox tri δ n v) atTop (𝓝 (gamma78GainKernel tri δ v)) := by
  by_cases hv : v ∈ gamma78GainRegion tri
  · have hs := hstrict hv
    have hb := gamma78Gain_region_bounds hv
    have hx := truncatedSixthClosure_corner_tendsto hb.2.2.1.le
    have hy := truncatedSixthClosure_corner_tendsto hb.2.2.2.1.le
    let j := fun n => (truncatedSixthClosureIndex n v.1,truncatedSixthClosureIndex n v.2)
    have hsample := gamma78Gain_sample_tendsto hb.2.2.1 hb.2.2.2.1.le
    have h1 := hx.1.eventually (lt_mem_nhds hs.1)
    have h2 := hx.2.eventually (gt_mem_nhds hs.2.1)
    have h3 := (hx.2.sub hy.1).eventually (gt_mem_nhds (sub_neg.mpr hs.2.2.1))
    have h4 := hy.1.eventually (lt_mem_nhds hs.2.2.2.1)
    have h5 := hy.2.eventually (gt_mem_nhds hs.2.2.2.2)
    have h6 := hsample.eventually (gt_mem_nhds hb.2.2.2.2.2.2.2.2.2)
    have hlim := (hc.tendsto.comp hsample).mul_const (gamma5GainSmooth v)
    rw [gamma78GainKernel,Set.indicator_of_mem hv]
    apply hlim.congr'
    filter_upwards [h1,h2,h3,h4,h5,h6] with n hn1 hn2 hn3 hn4 hn5 hn6
    have hj : j n ∈ gamma78GainInner tri n :=
      mem_filter.mpr ⟨mem_product.mpr
        ⟨mem_range.mpr (truncatedSixthClosure_index_lt n hb.2.2.1.le hb.2.2.2.2.1),
          mem_range.mpr (truncatedSixthClosure_index_lt n hb.2.2.2.1.le hb.2.2.2.2.2.1)⟩,
        hn1,hn2,sub_neg.mp hn3,hn4,hn5,hn6⟩
    exact (gamma78Gain_approx_at_cell hj
      ⟨truncatedSixthClosure_index_bounds n hb.2.2.1.le,
        truncatedSixthClosure_index_bounds n hb.2.2.2.1.le⟩).symm
  · have hz (n : ℕ) : gamma78GainApprox tri δ n v = 0 :=
      gamma78Gain_approx_zero (fun j hj hjv => hv (gamma78Gain_inner_subset hj hjv))
    simp only [hz,gamma78GainKernel,Set.indicator_of_notMem hv]
    exact tendsto_const_nhds

theorem gamma78Gain_approx_integral_tendsto {δ : ℝ} (tri : Bool) (hδ : 0 < δ) (hδhi : δ < 1/2) :
    Tendsto (fun n => ∫ v : ℝ × ℝ, gamma78GainApprox tri δ n v) atTop
      (𝓝 (gamma78GainIntegral tri δ)) := by
  rw [gamma78Gain_integral_eq tri hδ hδhi]
  apply tendsto_integral_of_dominated_convergence
    ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1).indicator (fun _ => (400 : ℝ)))
  · exact fun n => (gamma78Gain_approx_measurable tri δ n).aestronglyMeasurable
  · exact (integrableOn_const (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne).integrable_indicator
      (measurableSet_Icc.prod measurableSet_Icc)
  · exact fun n => Eventually.of_forall (gamma78Gain_approx_bound tri hδ hδhi n)
  · filter_upwards [gamma78Gain_strict_ae tri,gamma78Gain_H_pullback_ae hδ hδhi] with v hv hc
    exact gamma78Gain_approx_tendsto hv hc

theorem gamma78Gain_approx_le_kernel {δ : ℝ} (tri : Bool)
    (hδ : 0 < δ) (hδhi : δ < 1/2) (n : ℕ) (v : ℝ × ℝ) :
    gamma78GainApprox tri δ n v ≤ gamma78GainKernel tri δ v := by
  by_cases hex : ∃ j ∈ gamma78GainInner tri n, v ∈ truncatedSixthClosureCell n j
  · obtain ⟨j,hj,hv⟩ := hex
    have hr := gamma78Gain_inner_subset hj hv
    let r := gamma78GainInnerRectangle tri n ⟨j,hj⟩
    have hsample : gamma78GainV v.1 v.2 ≤ gamma78GainSample n j := by
      have ha : 0 < r.box.A := (by norm_num [gamma5MassA,gamma5ClassicalS] : 0 < gamma5MassA).trans r.box.lower
      have hh := gamma78Gain_V_antitone ha hv.1.1 hv.2.1 (gamma78Gain_region_unit hr).2.2
      exact hh.trans (le_add_of_nonneg_right (by positivity))
    rw [gamma78Gain_approx_at_cell hj hv,gamma78GainKernel,Set.indicator_of_mem hr]
    exact mul_le_mul_of_nonneg_right (gamma5Gain_H_antitone hδ hδhi hsample)
      (gamma5Gain_smooth_bounds v).1
  · rw [gamma78Gain_approx_zero (by simpa only [not_exists,not_and] using hex)]
    exact (gamma78Gain_kernel_bounds tri hδ hδhi v).1

end Wu2008DoubleSieve
