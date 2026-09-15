import MathlibNt.Wu2008DoubleSieve.TruncatedSixthClosureEnvelope
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace Wu2008DoubleSieve

open Finset Set Real Filter MeasureTheory
open scoped Classical Topology

noncomputable def truncatedSixthClosureDensity (gain : Bool) (δ : ℝ) (n : ℕ) (j : ℕ × ℕ) : ℝ :=
  truncatedSixthClosureWeight gain δ n j /
    (max truncatedSixthLowerAlpha (truncatedSixthClosureUpper n j).1 *
      max truncatedSixthLowerBeta (truncatedSixthClosureUpper n j).2 *
      max (2 * truncatedSixthLowerAlpha)
        (truncatedSixthLowerC δ - (truncatedSixthClosureLower n j).1 -
          (truncatedSixthClosureLower n j).2))

noncomputable def truncatedSixthClosureStep (gain : Bool) (δ : ℝ) (n : ℕ) (v : ℝ × ℝ) : ℝ :=
  ∑ j ∈ truncatedSixthClosureInner gain δ n,
    (truncatedSixthClosureCell n j).indicator (fun _ => truncatedSixthClosureDensity gain δ n j) v

noncomputable def truncatedSixthClosureKernel (gain : Bool) (δ : ℝ) (v : ℝ × ℝ) : ℝ :=
  if v ∈ truncatedSixthClosureRegion gain δ then
    truncatedSixthClosureCoefficient gain δ (truncatedSixthLowerS δ v.1 v.2) /
      (v.1 * v.2 * (truncatedSixthLowerC δ - v.1 - v.2)) else 0

theorem truncatedSixthClosure_kernel_eq {δ : ℝ} (hδ : 0 ≤ δ) (gain : Bool) :
    truncatedSixthClosureKernel gain δ =
      if gain then truncatedSixthMassAdmissibleKernel δ else truncatedSixthMassWedgeKernel δ := by
  funext v
  have he (hr : truncatedSixthLowerRegion δ v.1 v.2) :=
    truncatedSixthMass_clip_eq (truncatedSixthLower_region_bounds hδ hr).2.2.2
  cases gain
  · by_cases hv : truncatedSixthLowerWedge δ v.1 v.2
    · simp [truncatedSixthClosureKernel, truncatedSixthClosureRegion,
        truncatedSixthClosureCoefficient, truncatedSixthMassWedgeKernel,
        truncatedSixthMassAKernel, hv, hv.1, he hv.1]
    · simp [truncatedSixthClosureKernel, truncatedSixthClosureRegion,
        truncatedSixthMassWedgeKernel, hv]
  · by_cases hv : truncatedSixthLowerAdmissibleRegion δ v.1 v.2
    · simp [truncatedSixthClosureKernel, truncatedSixthClosureRegion,
        truncatedSixthClosureCoefficient, truncatedSixthMassAdmissibleKernel,
        truncatedSixthMassAKernel, truncatedSixthMassHKernel, truncatedSixthMassEffective,
        hv, hv.1, he hv.1, add_div]
    · simp [truncatedSixthClosureKernel, truncatedSixthClosureRegion,
        truncatedSixthMassAdmissibleKernel, hv]

theorem truncatedSixthClosure_density_bounds {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) (gain : Bool) (n : ℕ) (j : ℕ × ℕ) :
    0 ≤ truncatedSixthClosureDensity gain δ n j ∧
      truncatedSixthClosureDensity gain δ n j ≤ truncatedSixthMassKernelBound := by
  have hα := truncatedSixthLower_parameters.1
  have hβ := hα.trans truncatedSixthLower_parameters.2.1
  have hw := truncatedSixthClosure_weight_bounds hδ hδhi gain n j
  have hx : 0 < max truncatedSixthLowerAlpha (truncatedSixthClosureUpper n j).1 :=
    hα.trans_le (le_max_left _ _)
  have hy : 0 < max truncatedSixthLowerBeta (truncatedSixthClosureUpper n j).2 :=
    hβ.trans_le (le_max_left _ _)
  have hz : 0 < max (2 * truncatedSixthLowerAlpha)
      (truncatedSixthLowerC δ - (truncatedSixthClosureLower n j).1 -
        (truncatedSixthClosureLower n j).2) :=
    (mul_pos (by norm_num) hα).trans_le (le_max_left _ _)
  refine ⟨div_nonneg hw.1 (mul_nonneg (mul_nonneg hx.le hy.le) hz.le), ?_⟩
  apply div_le_div₀ (by norm_num : (0 : ℝ) ≤ 10) hw.2 (by positivity)
  exact mul_le_mul (mul_le_mul (le_max_left _ _) (le_max_left _ _) hβ.le hx.le)
    (le_max_left _ _) (by positivity) (mul_nonneg hx.le hy.le)

theorem truncatedSixthClosure_step_at_cell {gain : Bool} {δ : ℝ} {n : ℕ}
    {j : ℕ × ℕ} {v : ℝ × ℝ} (hj : j ∈ truncatedSixthClosureInner gain δ n)
    (hv : v ∈ truncatedSixthClosureCell n j) :
    truncatedSixthClosureStep gain δ n v = truncatedSixthClosureDensity gain δ n j := by
  unfold truncatedSixthClosureStep
  rw [sum_eq_single j]
  · exact Set.indicator_of_mem hv _
  · intro k _ hkj
    exact Set.indicator_of_notMem (fun hk => hkj (truncatedSixthClosure_cell_unique hk hv)) _
  · exact fun hn => False.elim (hn hj)

theorem truncatedSixthClosure_step_zero {gain : Bool} {δ : ℝ} {n : ℕ} {v : ℝ × ℝ}
    (h : ∀ j ∈ truncatedSixthClosureInner gain δ n, v ∉ truncatedSixthClosureCell n j) :
    truncatedSixthClosureStep gain δ n v = 0 := by
  exact sum_eq_zero (fun j hj => Set.indicator_of_notMem (h j hj) _)

theorem truncatedSixthClosure_step_outside {gain : Bool} {δ : ℝ} {v : ℝ × ℝ}
    (hv : v ∉ truncatedSixthClosureRegion gain δ) (n : ℕ) :
    truncatedSixthClosureStep gain δ n v = 0 := by
  apply truncatedSixthClosure_step_zero
  intro j hj hvj
  have hinner := (Finset.mem_filter.mp hj).2
  exact hv (truncatedSixthClosure_region_between hinner.1 hinner.2
    ⟨⟨hvj.1.1, hvj.2.1⟩, ⟨hvj.1.2.le, hvj.2.2.le⟩⟩)

theorem truncatedSixthClosure_step_measurable (gain : Bool) (δ : ℝ) (n : ℕ) :
    Measurable (truncatedSixthClosureStep gain δ n) := by
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.indicator (truncatedSixthClosure_cell_measurable n j)

theorem truncatedSixthClosure_step_bound {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) (gain : Bool) (n : ℕ) (v : ℝ × ℝ) :
    ‖truncatedSixthClosureStep gain δ n v‖ ≤
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1).indicator
        (fun _ => truncatedSixthMassKernelBound) v := by
  have hK : 0 ≤ truncatedSixthMassKernelBound := by
    have hα := truncatedSixthLower_parameters.1
    have hβ := hα.trans truncatedSixthLower_parameters.2.1
    unfold truncatedSixthMassKernelBound
    positivity
  by_cases hex : ∃ j ∈ truncatedSixthClosureInner gain δ n, v ∈ truncatedSixthClosureCell n j
  · obtain ⟨j, hj, hv⟩ := hex
    have hunit := truncatedSixthClosure_cell_mem (Finset.mem_filter.mp hj).1 hv
    have hunit' : v ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
      ⟨⟨hunit.1.1, hunit.1.2.le⟩, ⟨hunit.2.1, hunit.2.2.le⟩⟩
    rw [truncatedSixthClosure_step_at_cell hj hv, Set.indicator_of_mem
      hunit']
    have hb := truncatedSixthClosure_density_bounds hδ hδhi gain n j
    simpa [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2
  · rw [truncatedSixthClosure_step_zero (by simpa only [not_exists, not_and] using hex), norm_zero]
    exact Set.indicator_nonneg (fun _ _ => hK) _

theorem truncatedSixthClosure_density_tendsto {δ : ℝ} {gain : Bool} {v : ℝ × ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100)
    (hv : v ∈ truncatedSixthClosureRegion gain δ)
    (hc : ContinuousAt (truncatedSixthClosureCoefficient gain δ) (truncatedSixthLowerS δ v.1 v.2)) :
    Tendsto (fun n => truncatedSixthClosureDensity gain δ n
      (truncatedSixthClosureIndex n v.1, truncatedSixthClosureIndex n v.2))
      atTop (𝓝 (truncatedSixthClosureKernel gain δ v)) := by
  let j := fun n => (truncatedSixthClosureIndex n v.1, truncatedSixthClosureIndex n v.2)
  have hr := truncatedSixthClosure_region_bounds hv
  have hb := truncatedSixthLower_region_bounds hδ.le hr
  have hx := truncatedSixthClosure_corner_tendsto hb.1.le
  have hy := truncatedSixthClosure_corner_tendsto hb.2.1.le
  have hscont : Continuous (fun v : ℝ × ℝ => truncatedSixthLowerS δ v.1 v.2) := by
    unfold truncatedSixthLowerS
    fun_prop
  have hlo : Tendsto (fun n => truncatedSixthClosureLower n (j n)) atTop (𝓝 v) :=
    hx.1.prodMk_nhds hy.1
  have hup : Tendsto (fun n => truncatedSixthClosureUpper n (j n)) atTop (𝓝 v) :=
    hx.2.prodMk_nhds hy.2
  have hw := truncatedSixthClosure_inf_tendsto
    (fun t => (truncatedSixthClosure_coefficient_bounds hδ hδhi gain t).1) hc
    (fun n => truncatedSixthClosure_s_order (truncatedSixthClosure_corners_order n (j n)))
    (hscont.continuousAt.tendsto.comp hup) (hscont.continuousAt.tendsto.comp hlo)
  have hd := (((tendsto_const_nhds (x := truncatedSixthLowerAlpha)).max hx.2).mul
    ((tendsto_const_nhds (x := truncatedSixthLowerBeta)).max hy.2)).mul
    ((tendsto_const_nhds (x := 2 * truncatedSixthLowerAlpha)).max
      (((tendsto_const_nhds (x := truncatedSixthLowerC δ)).sub hx.1).sub hy.1))
  have hde : max truncatedSixthLowerAlpha v.1 * max truncatedSixthLowerBeta v.2 *
      max (2 * truncatedSixthLowerAlpha) (truncatedSixthLowerC δ - v.1 - v.2) =
      v.1 * v.2 * (truncatedSixthLowerC δ - v.1 - v.2) := by
    rw [max_eq_right hr.1, max_eq_right hr.2.2.1, max_eq_right hb.2.2.1]
  have hden : v.1 * v.2 * (truncatedSixthLowerC δ - v.1 - v.2) ≠ 0 := by
    have hα := truncatedSixthLower_parameters.1
    have hz : 0 < truncatedSixthLowerC δ - v.1 - v.2 := by linarith [hb.2.2.1]
    exact (mul_pos (mul_pos hb.1 hb.2.1) hz).ne'
  have hlim := hw.div hd (by rw [hde]; exact hden)
  change Tendsto (fun n => truncatedSixthClosureDensity gain δ n (j n)) atTop
    (𝓝 (truncatedSixthClosureCoefficient gain δ (truncatedSixthLowerS δ v.1 v.2) /
      (max truncatedSixthLowerAlpha v.1 * max truncatedSixthLowerBeta v.2 *
        max (2 * truncatedSixthLowerAlpha) (truncatedSixthLowerC δ - v.1 - v.2)))) at hlim
  rw [hde] at hlim
  simpa only [truncatedSixthClosureKernel, if_pos hv] using hlim

theorem truncatedSixthClosure_step_tendsto {δ : ℝ} {gain : Bool} {v : ℝ × ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100)
    (hfront : v ∉ frontier (truncatedSixthClosureRegion gain δ))
    (hc : ContinuousAt (truncatedSixthClosureCoefficient gain δ) (truncatedSixthLowerS δ v.1 v.2)) :
    Tendsto (fun n => truncatedSixthClosureStep gain δ n v)
      atTop (𝓝 (truncatedSixthClosureKernel gain δ v)) := by
  by_cases hv : v ∈ truncatedSixthClosureRegion gain δ
  · have hr := truncatedSixthClosure_region_bounds hv
    have hb := truncatedSixthLower_region_bounds hδ.le hr
    have hp := truncatedSixthLower_parameters
    have hx1 : v.1 < 1 := by linarith [hr.2.1, hp.2.2.1, hp.2.2.2.1]
    have hy1 : v.2 < 1 := by linarith [hr.2.2.2.1, hp.2.2.2.1]
    have hin : v ∈ interior (truncatedSixthClosureRegion gain δ) := by
      by_contra h
      exact hfront ⟨subset_closure hv, h⟩
    let j := fun n => (truncatedSixthClosureIndex n v.1, truncatedSixthClosureIndex n v.2)
    have hx := truncatedSixthClosure_corner_tendsto hb.1.le
    have hy := truncatedSixthClosure_corner_tendsto hb.2.1.le
    have hlo : Tendsto (fun n => truncatedSixthClosureLower n (j n)) atTop (𝓝 v) :=
      hx.1.prodMk_nhds hy.1
    have hup : Tendsto (fun n => truncatedSixthClosureUpper n (j n)) atTop (𝓝 v) :=
      hx.2.prodMk_nhds hy.2
    apply (truncatedSixthClosure_density_tendsto hδ hδhi hv hc).congr'
    filter_upwards [hlo.eventually (mem_of_superset (isOpen_interior.mem_nhds hin) interior_subset),
      hup.eventually (mem_of_superset (isOpen_interior.mem_nhds hin) interior_subset)] with n hnlo hnup
    apply (truncatedSixthClosure_step_at_cell ?_ ?_).symm
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨mem_range.mpr (truncatedSixthClosure_index_lt n hb.1.le hx1),
          mem_range.mpr (truncatedSixthClosure_index_lt n hb.2.1.le hy1)⟩, hnlo, hnup⟩
    · exact ⟨truncatedSixthClosure_index_bounds n hb.1.le, truncatedSixthClosure_index_bounds n hb.2.1.le⟩
  · simp only [truncatedSixthClosure_step_outside hv, truncatedSixthClosureKernel, if_neg hv]
    exact tendsto_const_nhds

theorem truncatedSixthClosure_integral_tendsto {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) (gain : Bool) :
    Tendsto (fun n => ∫ v : ℝ × ℝ, truncatedSixthClosureStep gain δ n v) atTop
      (𝓝 (∫ v : ℝ × ℝ, truncatedSixthClosureKernel gain δ v)) := by
  have hcoeff : ∀ᵐ v : ℝ × ℝ, ContinuousAt (truncatedSixthClosureCoefficient gain δ)
      (truncatedSixthLowerS δ v.1 v.2) := by
    cases gain
    · exact Eventually.of_forall (fun _ => truncatedSixthMass_clipped_classical_continuous.continuousAt)
    · exact truncatedSixthMass_effective_pullback_ae hδ hδhi
  apply tendsto_integral_of_dominated_convergence
    ((Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1).indicator (fun _ => truncatedSixthMassKernelBound))
  · exact fun n => (truncatedSixthClosure_step_measurable gain δ n).aestronglyMeasurable
  · exact (integrableOn_const (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne).integrable_indicator
      (measurableSet_Icc.prod measurableSet_Icc)
  · exact fun n => Eventually.of_forall (truncatedSixthClosure_step_bound hδ hδhi gain n)
  · filter_upwards [hcoeff, compl_mem_ae_iff.mpr (truncatedSixthClosure_region_frontier gain δ)]
      with v hc hf
    exact truncatedSixthClosure_step_tendsto hδ hδhi hf hc

end Wu2008DoubleSieve
