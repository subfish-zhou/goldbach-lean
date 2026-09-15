import MathlibNt.Wu2008DoubleSieve.Gamma5GainRectangleIntegral
import MathlibNt.Wu2008DoubleSieve.TruncatedSixthClosureGrid
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Sufficient finite internal right-endpoint families

Only bounded monotonicity of the actual Hdelta is used. The exceptional
affine pullbacks of its countably many discontinuities have zero measure.
-/

namespace Wu2008DoubleSieve

open Finset Set Real Filter MeasureTheory
open scoped Classical Topology

noncomputable def gamma5GainSample (n : ℕ) (j : ℕ × ℕ) : ℝ :=
  gamma5GainV (truncatedSixthClosureLo n j.1) (truncatedSixthClosureLo n j.2) +
    1 / (n + 1 : ℕ)

noncomputable def gamma5GainInner (n : ℕ) : Finset (ℕ × ℕ) :=
  (truncatedSixthClosureCells n).filter (fun j =>
    gamma5MassA < truncatedSixthClosureLo n j.1 ∧
    truncatedSixthClosureHi n j.1 < truncatedSixthClosureLo n j.2 ∧
    truncatedSixthClosureHi n j.2 < gamma5ClassicalB ∧
    truncatedSixthClosureHi n j.2 + 2 * truncatedSixthClosureHi n j.1 < 1 ∧
    gamma5GainSample n j < 3)

noncomputable def gamma5GainInnerRectangle (n : ℕ) (j : {j // j ∈ gamma5GainInner n}) :
    Gamma5GainRectangle where
  A := truncatedSixthClosureLo n j.val.1
  B := truncatedSixthClosureHi n j.val.1
  C := truncatedSixthClosureLo n j.val.2
  D := truncatedSixthClosureHi n j.val.2
  s := gamma5GainSample n j.val
  lower := (mem_filter.mp j.property).2.1
  first := truncatedSixthClosure_lo_lt_hi _ _
  ordered := (mem_filter.mp j.property).2.2.1
  second := truncatedSixthClosure_lo_lt_hi _ _
  upper := (mem_filter.mp j.property).2.2.2.1
  legal := (mem_filter.mp j.property).2.2.2.2.1
  rightEnd := lt_add_of_pos_right _ (by positivity)
  parameter := (mem_filter.mp j.property).2.2.2.2.2

noncomputable def gamma5GainApprox (δ : ℝ) (n : ℕ) (v : ℝ × ℝ) : ℝ :=
  ∑ j ∈ gamma5GainInner n, (truncatedSixthClosureCell n j).indicator
    (fun v => gamma5GainH δ (gamma5GainSample n j) * gamma5GainSmooth v) v

theorem gamma5Gain_inner_subset {n : ℕ} {j : ℕ × ℕ} (hj : j ∈ gamma5GainInner n) :
    truncatedSixthClosureCell n j ⊆ gamma5GainRegion := by
  let r := gamma5GainInnerRectangle n ⟨j, hj⟩
  have hr := gamma5Gain_rectangle_bounds r
  intro v hv
  change v.1 ∈ Ico r.A r.B ∧ v.2 ∈ Ico r.C r.D at hv
  exact ⟨⟨r.lower.le.trans hv.1.1, hv.1.2.le.trans (r.ordered.le.trans hv.2.1),
    hv.2.2.le.trans r.upper.le⟩,
    ⟨by linarith [hr.2.2.2.2.1, hv.2.2], by linarith [r.legal, hv.1.2, hv.2.2]⟩⟩

theorem gamma5Gain_approx_at_cell {δ : ℝ} {n : ℕ} {j : ℕ × ℕ} {v : ℝ × ℝ}
    (hj : j ∈ gamma5GainInner n) (hv : v ∈ truncatedSixthClosureCell n j) :
    gamma5GainApprox δ n v = gamma5GainH δ (gamma5GainSample n j) * gamma5GainSmooth v := by
  unfold gamma5GainApprox
  rw [sum_eq_single j]
  · exact Set.indicator_of_mem hv _
  · intro l _ hlj
    exact Set.indicator_of_notMem (fun hl => hlj (truncatedSixthClosure_cell_unique hl hv)) _
  · exact fun hn => False.elim (hn hj)

theorem gamma5Gain_approx_zero {δ : ℝ} {n : ℕ} {v : ℝ × ℝ}
    (h : ∀ j ∈ gamma5GainInner n, v ∉ truncatedSixthClosureCell n j) :
    gamma5GainApprox δ n v = 0 :=
  sum_eq_zero (fun j hj => Set.indicator_of_notMem (h j hj) _)

theorem gamma5Gain_approx_measurable (δ : ℝ) (n : ℕ) :
    Measurable (gamma5GainApprox δ n) := by
  apply Finset.measurable_sum
  intro j _
  exact (measurable_const.mul gamma5Gain_smooth_continuous.measurable).indicator
    (truncatedSixthClosure_cell_measurable n j)

theorem gamma5Gain_approx_bound {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (n : ℕ) (v : ℝ × ℝ) :
    ‖gamma5GainApprox δ n v‖ ≤
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1).indicator (fun _ => (400 : ℝ)) v := by
  by_cases hex : ∃ j ∈ gamma5GainInner n, v ∈ truncatedSixthClosureCell n j
  · obtain ⟨j, hj, hv⟩ := hex
    have hu := truncatedSixthClosure_cell_mem (mem_filter.mp hj).1 hv
    rw [gamma5Gain_approx_at_cell hj hv, Set.indicator_of_mem
      (show v ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 from
        ⟨⟨hu.1.1, hu.1.2.le⟩, ⟨hu.2.1, hu.2.2.le⟩⟩)]
    have hh := gamma5Gain_H_bounds hδ hδhi (gamma5GainSample n j)
    have hk := gamma5Gain_smooth_bounds v
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hh.1 hk.1)]
    nlinarith [mul_le_mul hh.2 hk.2 hk.1 (by norm_num : (0 : ℝ) ≤ 1)]
  · rw [gamma5Gain_approx_zero (by simpa only [not_exists, not_and] using hex), norm_zero]
    exact Set.indicator_nonneg (fun _ _ => by norm_num) _

theorem gamma5Gain_affine_ne_ae (a b c : ℝ) (hb : b ≠ 0) :
    ∀ᵐ v : ℝ × ℝ, a * v.1 + b * v.2 ≠ c := by
  have hm : MeasurableSet {v : ℝ × ℝ | a * v.1 + b * v.2 ≠ c} :=
    (measurableSet_eq_fun (by fun_prop) measurable_const).compl
  change ∀ᵐ v : ℝ × ℝ ∂(volume.prod volume), a * v.1 + b * v.2 ≠ c
  rw [Measure.ae_prod_iff_ae_ae hm]
  apply Eventually.of_forall
  intro t
  have hinj : Function.Injective (fun u : ℝ => a * t + b * u) := by
    intro x y h
    exact mul_left_cancel₀ hb (add_left_cancel h)
  exact ae_iff.mpr (by simpa only [Set.preimage, Set.mem_singleton_iff, not_not] using
    ((Set.countable_singleton c).preimage hinj).measure_zero volume)

theorem gamma5Gain_vertical_ne_ae (a : ℝ) : ∀ᵐ v : ℝ × ℝ, v.1 ≠ a := by
  have hm : MeasurableSet {v : ℝ × ℝ | v.1 ≠ a} :=
    (measurableSet_eq_fun measurable_fst measurable_const).compl
  change ∀ᵐ v : ℝ × ℝ ∂(volume.prod volume), v.1 ≠ a
  rw [Measure.ae_prod_iff_ae_ae hm]
  filter_upwards [show ∀ᵐ t : ℝ, t ≠ a from ae_iff.mpr (by simp)]
    with t ht
  exact Eventually.of_forall (fun _ => ht)

theorem gamma5Gain_strict_ae :
    ∀ᵐ v : ℝ × ℝ, v ∈ gamma5GainRegion →
      gamma5MassA < v.1 ∧ v.1 < v.2 ∧ v.2 < gamma5ClassicalB ∧ v.2 + 2 * v.1 < 1 := by
  filter_upwards [gamma5Gain_vertical_ne_ae gamma5MassA,
    gamma5Gain_affine_ne_ae 1 (-1) 0 (by norm_num),
    gamma5Gain_affine_ne_ae 0 1 gamma5ClassicalB (by norm_num),
    gamma5Gain_affine_ne_ae 2 1 1 (by norm_num)] with v ha hd hb hl
  intro hv
  refine ⟨lt_of_le_of_ne hv.1.1 (Ne.symm ha), ?_, ?_, ?_⟩
  · exact lt_of_le_of_ne hv.1.2.1 (by intro he; apply hd; rw [he]; ring)
  · exact lt_of_le_of_ne hv.1.2.2 (by simpa only [zero_mul, one_mul, zero_add] using hb)
  · exact lt_of_le_of_ne hv.2.2 (by simpa only [one_mul, add_comm] using hl)

theorem gamma5Gain_sample_tendsto {v : ℝ × ℝ}
    (hx : 0 ≤ v.1) (hy : 0 ≤ v.2) :
    Tendsto (fun n => gamma5GainSample n
      (truncatedSixthClosureIndex n v.1, truncatedSixthClosureIndex n v.2))
      atTop (𝓝 (gamma5GainV v.1 v.2)) := by
  have hmesh : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hx' := (truncatedSixthClosure_corner_tendsto hx).1
  have hy' := (truncatedSixthClosure_corner_tendsto hy).1
  simpa only [gamma5GainSample, gamma5GainV, add_zero] using
    ((((tendsto_const_nhds (x := (1 : ℝ))).sub hx').sub hy').const_mul gamma5ClassicalS).add hmesh

theorem gamma5Gain_approx_tendsto {δ : ℝ} {v : ℝ × ℝ}
    (hstrict : v ∈ gamma5GainRegion →
      gamma5MassA < v.1 ∧ v.1 < v.2 ∧ v.2 < gamma5ClassicalB ∧ v.2 + 2 * v.1 < 1)
    (hc : ContinuousAt (gamma5GainH δ) (gamma5GainV v.1 v.2)) :
    Tendsto (fun n => gamma5GainApprox δ n v) atTop (𝓝 (gamma5GainKernel δ v)) := by
  by_cases hv : v ∈ gamma5GainRegion
  · have hs := hstrict hv
    have hb := gamma5Gain_triangle_bounds hv.1
    have ha : 0 < gamma5MassA := by norm_num [gamma5MassA, gamma5ClassicalS]
    have hx0 := (ha.trans_le hb.1.1).le
    have hy0 := (ha.trans_le hb.2.1.1).le
    have hx := truncatedSixthClosure_corner_tendsto hx0
    have hy := truncatedSixthClosure_corner_tendsto hy0
    let j := fun n => (truncatedSixthClosureIndex n v.1, truncatedSixthClosureIndex n v.2)
    have hsample := gamma5Gain_sample_tendsto hx0 hy0
    have h1 := hx.1.eventually (lt_mem_nhds hs.1)
    have h2 := Filter.Tendsto.eventually_lt hx.2 hy.1 hs.2.1
    have h3 := hy.2.eventually (gt_mem_nhds hs.2.2.1)
    have h4 := (hy.2.add (hx.2.const_mul 2)).eventually (gt_mem_nhds hs.2.2.2)
    have h5 := hsample.eventually (gt_mem_nhds hb.2.2.2.1)
    have hlim := (hc.tendsto.comp hsample).mul_const (gamma5GainSmooth v)
    have heq : gamma5GainKernel δ v =
        gamma5GainH δ (gamma5GainV v.1 v.2) * gamma5GainSmooth v := by
      rw [gamma5GainKernel, if_pos hv, gamma5Gain_smooth_eq hb.1 hb.2.1]
      simp only [gamma5MassKernel, mul_one_div]
    rw [heq]
    apply hlim.congr'
    filter_upwards [h1, h2, h3, h4, h5] with n hn1 hn2 hn3 hn4 hn5
    have hj : j n ∈ gamma5GainInner n := by
      have hbound : gamma5ClassicalB < 1 := by norm_num [gamma5ClassicalB]
      exact mem_filter.mpr ⟨mem_product.mpr
        ⟨mem_range.mpr (truncatedSixthClosure_index_lt n hx0 (hb.1.2.trans_lt hbound)),
          mem_range.mpr (truncatedSixthClosure_index_lt n hy0 (hb.2.1.2.trans_lt hbound))⟩,
        hn1, hn2, hn3, hn4, hn5⟩
    exact (gamma5Gain_approx_at_cell hj
      ⟨truncatedSixthClosure_index_bounds n hx0, truncatedSixthClosure_index_bounds n hy0⟩).symm
  · have hz (n : ℕ) : gamma5GainApprox δ n v = 0 :=
      gamma5Gain_approx_zero (fun j hj hjv => hv (gamma5Gain_inner_subset hj hjv))
    simp only [hz, gamma5GainKernel, if_neg hv]
    exact tendsto_const_nhds

theorem gamma5Gain_approx_integral_tendsto {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    Tendsto (fun n => ∫ v : ℝ × ℝ, gamma5GainApprox δ n v) atTop (𝓝 (gamma5GainIntegral δ)) := by
  rw [gamma5Gain_integral_eq hδ hδhi]
  apply tendsto_integral_of_dominated_convergence
    ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1).indicator (fun _ => (400 : ℝ)))
  · exact fun n => (gamma5Gain_approx_measurable δ n).aestronglyMeasurable
  · exact (integrableOn_const (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne).integrable_indicator
      (measurableSet_Icc.prod measurableSet_Icc)
  · exact fun n => Eventually.of_forall (gamma5Gain_approx_bound hδ hδhi n)
  · filter_upwards [gamma5Gain_strict_ae, gamma5Gain_H_pullback_ae hδ hδhi] with v hv hc
    exact gamma5Gain_approx_tendsto hv hc

end Wu2008DoubleSieve
