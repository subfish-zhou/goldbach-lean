import MathlibNt.Wu2008DoubleSieve.Gamma6GainIntegral

namespace Wu2008DoubleSieve

open Finset Set Real Filter MeasureTheory
open scoped Classical Topology

noncomputable def gamma6GainInner (n : ℕ) : Finset (ℕ × ℕ) :=
  (truncatedSixthClosureCells n).filter (fun j =>
    gamma5MassA < truncatedSixthClosureLo n j.1 ∧
    truncatedSixthClosureHi n j.1 < gamma6BaseB ∧
    gamma6BaseC < truncatedSixthClosureLo n j.2 ∧
    truncatedSixthClosureHi n j.2 < gamma6BaseF ∧ gamma5GainSample n j < 3)

noncomputable def gamma6GainInnerRectangle (n : ℕ) (j : {j // j ∈ gamma6GainInner n}) :
    Gamma6GainRectangle where
  A := truncatedSixthClosureLo n j.val.1
  B := truncatedSixthClosureHi n j.val.1
  C := truncatedSixthClosureLo n j.val.2
  D := truncatedSixthClosureHi n j.val.2
  s := gamma5GainSample n j.val
  lower := (mem_filter.mp j.property).2.1
  first := truncatedSixthClosure_lo_lt_hi _ _
  firstUpper := (mem_filter.mp j.property).2.2.1
  secondLower := (mem_filter.mp j.property).2.2.2.1
  second := truncatedSixthClosure_lo_lt_hi _ _
  upper := (mem_filter.mp j.property).2.2.2.2.1
  rightEnd := lt_add_of_pos_right _ (by positivity)
  parameter := (mem_filter.mp j.property).2.2.2.2.2

noncomputable def gamma6GainApprox (δ : ℝ) (n : ℕ) (v : ℝ × ℝ) : ℝ :=
  ∑ j ∈ gamma6GainInner n, (truncatedSixthClosureCell n j).indicator
    (fun v => gamma5GainH δ (gamma5GainSample n j) * gamma5GainSmooth v) v

theorem gamma6Gain_inner_subset {n : ℕ} {j : ℕ × ℕ} (hj : j ∈ gamma6GainInner n) :
    truncatedSixthClosureCell n j ⊆ gamma6GainRegion := by
  let r := gamma6GainInnerRectangle n ⟨j,hj⟩
  intro v hv
  change v.1 ∈ Ico r.A r.B ∧ v.2 ∈ Ico r.C r.D at hv
  exact ⟨⟨r.lower.le.trans hv.1.1, hv.1.2.le.trans r.firstUpper.le⟩,
    ⟨r.secondLower.le.trans hv.2.1, hv.2.2.le.trans r.upper.le⟩⟩

theorem gamma6Gain_approx_at_cell {δ : ℝ} {n : ℕ} {j : ℕ × ℕ} {v : ℝ × ℝ}
    (hj : j ∈ gamma6GainInner n) (hv : v ∈ truncatedSixthClosureCell n j) :
    gamma6GainApprox δ n v = gamma5GainH δ (gamma5GainSample n j) * gamma5GainSmooth v := by
  unfold gamma6GainApprox
  rw [sum_eq_single j]
  · exact Set.indicator_of_mem hv _
  · intro l _ hlj
    exact Set.indicator_of_notMem (fun hl => hlj (truncatedSixthClosure_cell_unique hl hv)) _
  · exact fun hn => False.elim (hn hj)

theorem gamma6Gain_approx_zero {δ : ℝ} {n : ℕ} {v : ℝ × ℝ}
    (h : ∀ j ∈ gamma6GainInner n, v ∉ truncatedSixthClosureCell n j) :
    gamma6GainApprox δ n v = 0 :=
  sum_eq_zero (fun j hj => Set.indicator_of_notMem (h j hj) _)

theorem gamma6Gain_approx_measurable (δ : ℝ) (n : ℕ) :
    Measurable (gamma6GainApprox δ n) := by
  apply Finset.measurable_sum
  intro j _
  exact (measurable_const.mul gamma5Gain_smooth_continuous.measurable).indicator
    (truncatedSixthClosure_cell_measurable n j)

theorem gamma6Gain_approx_bound {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (n : ℕ) (v : ℝ × ℝ) :
    ‖gamma6GainApprox δ n v‖ ≤
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1).indicator (fun _ => (400 : ℝ)) v := by
  by_cases hex : ∃ j ∈ gamma6GainInner n, v ∈ truncatedSixthClosureCell n j
  · obtain ⟨j, hj, hv⟩ := hex
    have hu := truncatedSixthClosure_cell_mem (mem_filter.mp hj).1 hv
    rw [gamma6Gain_approx_at_cell hj hv, Set.indicator_of_mem
      (show v ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 from
        ⟨⟨hu.1.1, hu.1.2.le⟩, ⟨hu.2.1, hu.2.2.le⟩⟩)]
    have hh := gamma5Gain_H_bounds hδ hδhi (gamma5GainSample n j)
    have hk := gamma5Gain_smooth_bounds v
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hh.1 hk.1)]
    nlinarith [mul_le_mul hh.2 hk.2 hk.1 (by norm_num : (0 : ℝ) ≤ 1)]
  · rw [gamma6Gain_approx_zero (by simpa only [not_exists, not_and] using hex), norm_zero]
    exact Set.indicator_nonneg (fun _ _ => by norm_num) _

theorem gamma6Gain_strict_ae :
    ∀ᵐ v : ℝ × ℝ, v ∈ gamma6GainRegion →
      gamma5MassA < v.1 ∧ v.1 < gamma6BaseB ∧ gamma6BaseC < v.2 ∧ v.2 < gamma6BaseF := by
  filter_upwards [gamma5Gain_vertical_ne_ae gamma5MassA,
    gamma5Gain_vertical_ne_ae gamma6BaseB,
    gamma5Gain_affine_ne_ae 0 1 gamma6BaseC (by norm_num),
    gamma5Gain_affine_ne_ae 0 1 gamma6BaseF (by norm_num)] with v ha hb hc hf
  intro hv
  simp only [zero_mul, one_mul, zero_add] at hc hf
  exact ⟨lt_of_le_of_ne hv.1.1 ha.symm, lt_of_le_of_ne hv.1.2 hb,
    lt_of_le_of_ne hv.2.1 hc.symm, lt_of_le_of_ne hv.2.2 hf⟩

theorem gamma6Gain_approx_tendsto {δ : ℝ} {v : ℝ × ℝ}
    (hstrict : v ∈ gamma6GainRegion →
      gamma5MassA < v.1 ∧ v.1 < gamma6BaseB ∧ gamma6BaseC < v.2 ∧ v.2 < gamma6BaseF)
    (hc : ContinuousAt (gamma5GainH δ) (gamma5GainV v.1 v.2)) :
    Tendsto (fun n => gamma6GainApprox δ n v) atTop (𝓝 (gamma6GainKernel δ v)) := by
  by_cases hv : v ∈ gamma6GainRegion
  · have hs := hstrict hv
    have hb := gamma6Gain_domain_bounds hv.1 hv.2
    have hx0 := hb.1.le
    have hy0 := hb.2.1.le
    have hx := truncatedSixthClosure_corner_tendsto hx0
    have hy := truncatedSixthClosure_corner_tendsto hy0
    let j := fun n => (truncatedSixthClosureIndex n v.1, truncatedSixthClosureIndex n v.2)
    have hsample := gamma5Gain_sample_tendsto hx0 hy0
    have h1 := hx.1.eventually (lt_mem_nhds hs.1)
    have h2 := hx.2.eventually (gt_mem_nhds hs.2.1)
    have h3 := hy.1.eventually (lt_mem_nhds hs.2.2.1)
    have h4 := hy.2.eventually (gt_mem_nhds hs.2.2.2)
    have h5 := hsample.eventually (gt_mem_nhds
      (show gamma5GainV v.1 v.2 < 3 by linarith [hb.2.2.2.2.2.2.2.2.1]))
    have hlim := (hc.tendsto.comp hsample).mul_const (gamma5GainSmooth v)
    rw [gamma6GainKernel, Set.indicator_of_mem hv]
    apply hlim.congr'
    filter_upwards [h1,h2,h3,h4,h5] with n hn1 hn2 hn3 hn4 hn5
    have hj : j n ∈ gamma6GainInner n :=
      mem_filter.mpr ⟨mem_product.mpr
        ⟨mem_range.mpr (truncatedSixthClosure_index_lt n hx0 hb.2.2.2.1),
          mem_range.mpr (truncatedSixthClosure_index_lt n hy0 hb.2.2.2.2.1)⟩,
        hn1,hn2,hn3,hn4,hn5⟩
    exact (gamma6Gain_approx_at_cell hj
      ⟨truncatedSixthClosure_index_bounds n hx0, truncatedSixthClosure_index_bounds n hy0⟩).symm
  · have hz (n : ℕ) : gamma6GainApprox δ n v = 0 :=
      gamma6Gain_approx_zero (fun j hj hjv => hv (gamma6Gain_inner_subset hj hjv))
    simp only [hz, gamma6GainKernel, Set.indicator_of_notMem hv]
    exact tendsto_const_nhds

theorem gamma6Gain_approx_integral_tendsto {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    Tendsto (fun n => ∫ v : ℝ × ℝ, gamma6GainApprox δ n v) atTop (𝓝 (gamma6GainIntegral δ)) := by
  rw [gamma6Gain_integral_eq hδ hδhi]
  apply tendsto_integral_of_dominated_convergence
    ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1).indicator (fun _ => (400 : ℝ)))
  · exact fun n => (gamma6Gain_approx_measurable δ n).aestronglyMeasurable
  · exact (integrableOn_const (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne).integrable_indicator
      (measurableSet_Icc.prod measurableSet_Icc)
  · exact fun n => Eventually.of_forall (gamma6Gain_approx_bound hδ hδhi n)
  · filter_upwards [gamma6Gain_strict_ae, gamma5Gain_H_pullback_ae hδ hδhi] with v hv hc
    exact gamma6Gain_approx_tendsto hv hc

theorem gamma6Gain_approx_le_kernel {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (n : ℕ) (v : ℝ × ℝ) :
    gamma6GainApprox δ n v ≤ gamma6GainKernel δ v := by
  by_cases hex : ∃ j ∈ gamma6GainInner n, v ∈ truncatedSixthClosureCell n j
  · obtain ⟨j,hj,hv⟩ := hex
    have hr := gamma6Gain_inner_subset hj hv
    have hsample : gamma5GainV v.1 v.2 ≤ gamma5GainSample n j := by
      have hp : (0 : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) := by positivity
      have hS : 0 < gamma5ClassicalS := by norm_num [gamma5ClassicalS]
      dsimp only [gamma5GainSample, gamma5GainV]
      nlinarith [hv.1.1, hv.2.1]
    rw [gamma6Gain_approx_at_cell hj hv, gamma6GainKernel, Set.indicator_of_mem hr]
    exact mul_le_mul_of_nonneg_right (gamma5Gain_H_antitone hδ hδhi hsample)
      (gamma5Gain_smooth_bounds v).1
  · rw [gamma6Gain_approx_zero (by simpa only [not_exists, not_and] using hex)]
    exact (gamma6Gain_kernel_bounds hδ hδhi v).1

end Wu2008DoubleSieve
