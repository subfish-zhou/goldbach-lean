import MathlibNt.Wu2008DoubleSieve.FifthPairFamily
namespace Wu2008DoubleSieve
open Finset Set Real Filter MeasureTheory
open scoped Classical Topology

noncomputable def fifthPairRegion : Set (ℝ × ℝ) :=
  {v | truncatedSixthLowerAlpha ≤ v.1 ∧ v.1 ≤ v.2 ∧ v.2 ≤ truncatedSixthLowerBeta}

noncomputable def fifthPairKernelBound : ℝ :=
  10 / (truncatedSixthLowerAlpha * truncatedSixthLowerAlpha * (2 * truncatedSixthLowerAlpha))

theorem fifthPair_region_bounds {δ : ℝ} {v : ℝ × ℝ}
    (hδ : 0 ≤ δ) (hδhi : δ ≤ 1 / 1000) (hv : v ∈ fifthPairRegion) :
    0 < v.1 ∧ 0 < v.2 ∧ 2 * truncatedSixthLowerAlpha ≤ truncatedSixthLowerC δ - v.1 - v.2 ∧
      2 ≤ truncatedSixthLowerS δ v.1 v.2 ∧ truncatedSixthLowerS δ v.1 v.2 ≤ 5 := by
  have h := fifthPair_triangle_bounds hδ hδhi hv.1 hv.2.1 hv.2.2
  refine ⟨h.1, h.2.1, ?_, h.2.2.1, h.2.2.2.1⟩
  exact (le_div_iff₀ truncatedSixthLower_parameters.1).mp h.2.2.1

theorem fifthPair_region_frontier : volume (frontier fifthPairRegion) = 0 := by
  apply Convex.addHaar_frontier
  intro v hv w hw A B hA hB hsum
  change truncatedSixthLowerAlpha ≤ A * v.1 + B * w.1 ∧
    A * v.1 + B * w.1 ≤ A * v.2 + B * w.2 ∧
    A * v.2 + B * w.2 ≤ truncatedSixthLowerBeta
  refine ⟨?_, add_le_add (mul_le_mul_of_nonneg_left hv.2.1 hA)
    (mul_le_mul_of_nonneg_left hw.2.1 hB), ?_⟩
  · have h := add_le_add (mul_le_mul_of_nonneg_left hv.1 hA) (mul_le_mul_of_nonneg_left hw.1 hB)
    simpa only [← add_mul, hsum, one_mul] using h
  · have h := add_le_add (mul_le_mul_of_nonneg_left hv.2.2 hA) (mul_le_mul_of_nonneg_left hw.2.2 hB)
    simpa only [← add_mul, hsum, one_mul] using h

noncomputable def fifthPairDensity (δ : ℝ) (n : ℕ) (j : ℕ × ℕ) : ℝ :=
  truncatedSixthClosureWeight false δ n j /
    (max truncatedSixthLowerAlpha (truncatedSixthClosureUpper n j).1 *
      max truncatedSixthLowerAlpha (truncatedSixthClosureUpper n j).2 *
      max (2 * truncatedSixthLowerAlpha)
        (truncatedSixthLowerC δ - (truncatedSixthClosureLower n j).1 -
          (truncatedSixthClosureLower n j).2))

noncomputable def fifthPairStep (δ : ℝ) (n : ℕ) (v : ℝ × ℝ) : ℝ :=
  ∑ j ∈ fifthPairInner n,
    (truncatedSixthClosureCell n j).indicator (fun _ => fifthPairDensity δ n j) v

noncomputable def fifthPairKernel (δ : ℝ) (v : ℝ × ℝ) : ℝ :=
  if v ∈ fifthPairRegion then
    truncatedSixthClosureCoefficient false δ (truncatedSixthLowerS δ v.1 v.2) /
      (v.1 * v.2 * (truncatedSixthLowerC δ - v.1 - v.2)) else 0

theorem fifthPair_density_bounds {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) (n : ℕ) (j : ℕ × ℕ) :
    0 ≤ fifthPairDensity δ n j ∧
      fifthPairDensity δ n j ≤ fifthPairKernelBound := by
  have hα := truncatedSixthLower_parameters.1
  have hβ := hα
  have hw := truncatedSixthClosure_weight_bounds hδ (by linarith) false n j
  have hx : 0 < max truncatedSixthLowerAlpha (truncatedSixthClosureUpper n j).1 :=
    hα.trans_le (le_max_left _ _)
  have hy : 0 < max truncatedSixthLowerAlpha (truncatedSixthClosureUpper n j).2 :=
    hβ.trans_le (le_max_left _ _)
  have hz : 0 < max (2 * truncatedSixthLowerAlpha)
      (truncatedSixthLowerC δ - (truncatedSixthClosureLower n j).1 -
        (truncatedSixthClosureLower n j).2) :=
    (mul_pos (by norm_num) hα).trans_le (le_max_left _ _)
  refine ⟨div_nonneg hw.1 (mul_nonneg (mul_nonneg hx.le hy.le) hz.le), ?_⟩
  apply div_le_div₀ (by norm_num : (0 : ℝ) ≤ 10) hw.2 (by positivity)
  exact mul_le_mul (mul_le_mul (le_max_left _ _) (le_max_left _ _) hβ.le hx.le)
    (le_max_left _ _) (by positivity) (mul_nonneg hx.le hy.le)

theorem fifthPair_step_at_cell {δ : ℝ} {n : ℕ}
    {j : ℕ × ℕ} {v : ℝ × ℝ} (hj : j ∈ fifthPairInner n)
    (hv : v ∈ truncatedSixthClosureCell n j) :
    fifthPairStep δ n v = fifthPairDensity δ n j := by
  unfold fifthPairStep
  rw [sum_eq_single j]
  · exact Set.indicator_of_mem hv _
  · intro k _ hkj
    exact Set.indicator_of_notMem (fun hk => hkj (truncatedSixthClosure_cell_unique hk hv)) _
  · exact fun hn => False.elim (hn hj)

theorem fifthPair_step_zero {δ : ℝ} {n : ℕ} {v : ℝ × ℝ}
    (h : ∀ j ∈ fifthPairInner n, v ∉ truncatedSixthClosureCell n j) :
    fifthPairStep δ n v = 0 := by
  exact sum_eq_zero (fun j hj => Set.indicator_of_notMem (h j hj) _)

theorem fifthPair_step_outside {δ : ℝ} {v : ℝ × ℝ}
    (hv : v ∉ fifthPairRegion) (n : ℕ) :
    fifthPairStep δ n v = 0 := by
  apply fifthPair_step_zero
  intro j hj hvj
  have hg := fifthPair_inner_geometry hj
  exact hv ⟨hg.1.trans hvj.1.1,
    hvj.1.2.le.trans (hg.2.1.trans hvj.2.1), hvj.2.2.le.trans hg.2.2⟩

theorem fifthPair_step_measurable (δ : ℝ) (n : ℕ) :
    Measurable (fifthPairStep δ n) := by
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.indicator (truncatedSixthClosure_cell_measurable n j)

theorem fifthPair_step_bound {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) (n : ℕ) (v : ℝ × ℝ) :
    ‖fifthPairStep δ n v‖ ≤
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1).indicator
        (fun _ => fifthPairKernelBound) v := by
  have hK : 0 ≤ fifthPairKernelBound := by
    have hα := truncatedSixthLower_parameters.1
    have hβ := hα
    unfold fifthPairKernelBound
    positivity
  by_cases hex : ∃ j ∈ fifthPairInner n, v ∈ truncatedSixthClosureCell n j
  · obtain ⟨j, hj, hv⟩ := hex
    have hunit := truncatedSixthClosure_cell_mem (Finset.mem_filter.mp hj).1 hv
    have hunit' : v ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
      ⟨⟨hunit.1.1, hunit.1.2.le⟩, ⟨hunit.2.1, hunit.2.2.le⟩⟩
    rw [fifthPair_step_at_cell hj hv, Set.indicator_of_mem
      hunit']
    have hb := fifthPair_density_bounds hδ hδhi n j
    simpa [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2
  · rw [fifthPair_step_zero (by simpa only [not_exists, not_and] using hex), norm_zero]
    exact Set.indicator_nonneg (fun _ _ => hK) _

theorem fifthPair_density_tendsto {δ : ℝ} {v : ℝ × ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000)
    (hv : v ∈ fifthPairRegion)
    (hc : ContinuousAt (truncatedSixthClosureCoefficient false δ) (truncatedSixthLowerS δ v.1 v.2)) :
    Tendsto (fun n => fifthPairDensity δ n
      (truncatedSixthClosureIndex n v.1, truncatedSixthClosureIndex n v.2))
      atTop (𝓝 (fifthPairKernel δ v)) := by
  let j := fun n => (truncatedSixthClosureIndex n v.1, truncatedSixthClosureIndex n v.2)
  have hr := hv
  have hb := fifthPair_region_bounds hδ.le hδhi hr
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
    (fun t => (truncatedSixthClosure_coefficient_bounds hδ (by linarith) false t).1) hc
    (fun n => truncatedSixthClosure_s_order (truncatedSixthClosure_corners_order n (j n)))
    (hscont.continuousAt.tendsto.comp hup) (hscont.continuousAt.tendsto.comp hlo)
  have hd := (((tendsto_const_nhds (x := truncatedSixthLowerAlpha)).max hx.2).mul
    ((tendsto_const_nhds (x := truncatedSixthLowerAlpha)).max hy.2)).mul
    ((tendsto_const_nhds (x := 2 * truncatedSixthLowerAlpha)).max
      (((tendsto_const_nhds (x := truncatedSixthLowerC δ)).sub hx.1).sub hy.1))
  have hde : max truncatedSixthLowerAlpha v.1 * max truncatedSixthLowerAlpha v.2 *
      max (2 * truncatedSixthLowerAlpha) (truncatedSixthLowerC δ - v.1 - v.2) =
      v.1 * v.2 * (truncatedSixthLowerC δ - v.1 - v.2) := by
    rw [max_eq_right hr.1, max_eq_right (hr.1.trans hr.2.1), max_eq_right hb.2.2.1]
  have hden : v.1 * v.2 * (truncatedSixthLowerC δ - v.1 - v.2) ≠ 0 := by
    have hα := truncatedSixthLower_parameters.1
    have hz : 0 < truncatedSixthLowerC δ - v.1 - v.2 := by linarith [hb.2.2.1]
    exact (mul_pos (mul_pos hb.1 hb.2.1) hz).ne'
  have hlim := hw.div hd (by rw [hde]; exact hden)
  change Tendsto (fun n => fifthPairDensity δ n (j n)) atTop
    (𝓝 (truncatedSixthClosureCoefficient false δ (truncatedSixthLowerS δ v.1 v.2) /
      (max truncatedSixthLowerAlpha v.1 * max truncatedSixthLowerAlpha v.2 *
        max (2 * truncatedSixthLowerAlpha) (truncatedSixthLowerC δ - v.1 - v.2)))) at hlim
  rw [hde] at hlim
  simpa only [fifthPairKernel, if_pos hv] using hlim

theorem fifthPair_step_tendsto {δ : ℝ} {v : ℝ × ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000)
    (hfront : v ∉ frontier (fifthPairRegion))
    (hc : ContinuousAt (truncatedSixthClosureCoefficient false δ) (truncatedSixthLowerS δ v.1 v.2)) :
    Tendsto (fun n => fifthPairStep δ n v)
      atTop (𝓝 (fifthPairKernel δ v)) := by
  by_cases hv : v ∈ fifthPairRegion
  · have hr := hv
    have hb := fifthPair_region_bounds hδ.le hδhi hr
    have hp := truncatedSixthLower_parameters
    have hx1 : v.1 < 1 := by linarith [hr.2.1, hr.2.2, hp.2.2.1, hp.2.2.2.1]
    have hy1 : v.2 < 1 := by linarith [hr.2.2, hp.2.2.1, hp.2.2.2.1]
    have hin : v ∈ interior (fifthPairRegion) := by
      by_contra h
      exact hfront ⟨subset_closure hv, h⟩
    let j := fun n => (truncatedSixthClosureIndex n v.1, truncatedSixthClosureIndex n v.2)
    have hx := truncatedSixthClosure_corner_tendsto hb.1.le
    have hy := truncatedSixthClosure_corner_tendsto hb.2.1.le
    have hlo : Tendsto (fun n => truncatedSixthClosureLower n (j n)) atTop (𝓝 v) :=
      hx.1.prodMk_nhds hy.1
    have hup : Tendsto (fun n => truncatedSixthClosureUpper n (j n)) atTop (𝓝 v) :=
      hx.2.prodMk_nhds hy.2
    have hmix : Tendsto (fun n => (truncatedSixthClosureHi n (j n).1,
        truncatedSixthClosureLo n (j n).2)) atTop (𝓝 v) := hx.2.prodMk_nhds hy.1
    apply (fifthPair_density_tendsto hδ hδhi hv hc).congr' 
    filter_upwards [hlo.eventually (mem_of_superset (isOpen_interior.mem_nhds hin) interior_subset),
      hup.eventually (mem_of_superset (isOpen_interior.mem_nhds hin) interior_subset),
      hmix.eventually (mem_of_superset (isOpen_interior.mem_nhds hin) interior_subset)] with n hnlo hnup hnmix
    apply (fifthPair_step_at_cell ?_ ?_).symm
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨mem_range.mpr (truncatedSixthClosure_index_lt n hb.1.le hx1),
          mem_range.mpr (truncatedSixthClosure_index_lt n hb.2.1.le hy1)⟩, hnlo.1, hnmix.2.1, hnup.2.2⟩
    · exact ⟨truncatedSixthClosure_index_bounds n hb.1.le, truncatedSixthClosure_index_bounds n hb.2.1.le⟩
  · simp only [fifthPair_step_outside hv, fifthPairKernel, if_neg hv]
    exact tendsto_const_nhds

theorem fifthPair_integral_tendsto {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) :
    Tendsto (fun n => ∫ v : ℝ × ℝ, fifthPairStep δ n v) atTop
      (𝓝 (∫ v : ℝ × ℝ, fifthPairKernel δ v)) := by
  have hcoeff : ∀ᵐ v : ℝ × ℝ, ContinuousAt (truncatedSixthClosureCoefficient false δ)
      (truncatedSixthLowerS δ v.1 v.2) :=
    Eventually.of_forall (fun _ => truncatedSixthMass_clipped_classical_continuous.continuousAt)
  apply tendsto_integral_of_dominated_convergence
    ((Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1).indicator (fun _ => fifthPairKernelBound))
  · exact fun n => (fifthPair_step_measurable δ n).aestronglyMeasurable
  · exact (integrableOn_const (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne).integrable_indicator
      (measurableSet_Icc.prod measurableSet_Icc)
  · exact fun n => Eventually.of_forall (fifthPair_step_bound hδ hδhi n)
  · filter_upwards [hcoeff, compl_mem_ae_iff.mpr (fifthPair_region_frontier)]
      with v hc hf
    exact fifthPair_step_tendsto hδ hδhi hf hc

end Wu2008DoubleSieve
