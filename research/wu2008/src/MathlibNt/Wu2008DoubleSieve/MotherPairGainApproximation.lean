import MathlibNt.Wu2008DoubleSieve.MotherPairGainRegularity
import MathlibNt.Wu2008DoubleSieve.Gamma5GainApproximation

namespace Wu2008DoubleSieve.MotherPair
open Finset Set Real Filter MeasureTheory
open scoped Classical Topology

noncomputable def gridSample (p : SecondFunctionalParameters) (j : Term)
    (n : ℕ) (i : ℕ × ℕ) : ℝ :=
  Hratio p j (truncatedSixthClosureLo n i.1) (truncatedSixthClosureLo n i.2) +
    1 / (n + 1 : ℕ)

noncomputable def gridInner (p : SecondFunctionalParameters) (j : Term) (n : ℕ) :
    Finset (ℕ × ℕ) :=
  (truncatedSixthClosureCells n).filter (fun i =>
    1/p.S < truncatedSixthClosureLo n i.1 ∧
    truncatedSixthClosureHi n i.1 < truncatedSixthClosureLo n i.2 ∧
    truncatedSixthClosureHi n i.1 < upperP p j ∧
    lowerQ p j < truncatedSixthClosureLo n i.2 ∧
    truncatedSixthClosureHi n i.2 < upperQ p j ∧
    2*truncatedSixthClosureHi n i.2 < 1 ∧
    truncatedSixthClosureHi n i.2 + 2*truncatedSixthClosureHi n i.1 < 1 ∧
    1 < gridSample p j n i ∧ gridSample p j n i < 3)

noncomputable def gridRectangle (p : SecondFunctionalParameters) (j : Term)
    (n : ℕ) (i : {i // i ∈ gridInner p j n}) : GainRectangle p j where
  A := truncatedSixthClosureLo n i.val.1
  B := truncatedSixthClosureHi n i.val.1
  C := truncatedSixthClosureLo n i.val.2
  D := truncatedSixthClosureHi n i.val.2
  sample := gridSample p j n i.val
  lowerP_lt_A := (mem_filter.mp i.property).2.1
  A_lt_B := truncatedSixthClosure_lo_lt_hi _ _
  B_lt_C := (mem_filter.mp i.property).2.2.1
  C_lt_D := truncatedSixthClosure_lo_lt_hi _ _
  B_lt_upperP := (mem_filter.mp i.property).2.2.2.1
  lowerQ_lt_C := (mem_filter.mp i.property).2.2.2.2.1
  D_lt_upperQ := (mem_filter.mp i.property).2.2.2.2.2.1
  twiceD_lt_one := (mem_filter.mp i.property).2.2.2.2.2.2.1
  D_twiceB_lt_one := (mem_filter.mp i.property).2.2.2.2.2.2.2.1
  sample_lower := (mem_filter.mp i.property).2.2.2.2.2.2.2.2.1
  sample_upper := (mem_filter.mp i.property).2.2.2.2.2.2.2.2.2
  ratio_lt_sample := lt_add_of_pos_right _ (by positivity)

/-- The finite family consists of actual strict rectangles, not bounds or certificates. -/
noncomputable def gridFamily (p : SecondFunctionalParameters) (j : Term) (n : ℕ) :
    Finset (GainRectangle p j) :=
  Finset.univ.image (gridRectangle p j n)

theorem grid_inner_subset {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    {j : Term} {n : ℕ} {i : ℕ × ℕ} (hi : i ∈ gridInner p j n) :
    truncatedSixthClosureCell n i ⊆ gainRegion p j := by
  let r := gridRectangle p j n ⟨i,hi⟩
  intro v hv
  change v.1 ∈ Ico r.A r.B ∧ v.2 ∈ Ico r.C r.D at hv
  refine ⟨(pairRegion_iff h j v.1 v.2).mpr ?_, ?_⟩
  · exact ⟨⟨r.lowerP_lt_A.le.trans hv.1.1,hv.1.2.le.trans r.B_lt_upperP.le⟩,
      ⟨max_le (r.lowerQ_lt_C.le.trans hv.2.1)
        (hv.1.2.le.trans (r.B_lt_C.le.trans hv.2.1)),
        hv.2.2.le.trans r.D_lt_upperQ.le⟩⟩
  · exact ⟨by linarith [r.twiceD_lt_one,hv.2.2],
      by linarith [r.D_twiceB_lt_one,hv.1.2,hv.2.2]⟩

theorem grid_family_pairwise (p : SecondFunctionalParameters) (j : Term) (n : ℕ) :
    (↑(gridFamily p j n) : Set (GainRectangle p j)).Pairwise (fun r s =>
      Disjoint (Ico r.A r.B ×ˢ Ico r.C r.D) (Ico s.A s.B ×ˢ Ico s.C s.D)) := by
  intro r hr s hs hrs
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hs
  apply Set.disjoint_left.mpr
  intro v hv hw
  have he : i.val = k.val := truncatedSixthClosure_cell_unique hv hw
  exact hrs (congrArg (gridRectangle p j n) (Subtype.ext he))

theorem grid_rectangle_injective (p : SecondFunctionalParameters) (j : Term) (n : ℕ) :
    Function.Injective (gridRectangle p j n) := by
  intro i k he
  apply Subtype.ext
  have hA := congrArg GainRectangle.A he
  have hC := congrArg GainRectangle.C he
  change truncatedSixthClosureLo n i.val.1 = truncatedSixthClosureLo n k.val.1 at hA
  change truncatedSixthClosureLo n i.val.2 = truncatedSixthClosureLo n k.val.2 at hC
  apply Prod.ext
  · exact_mod_cast (div_left_inj' (by positivity : ((n+1:ℕ):ℝ) ≠ 0)).mp hA
  · exact_mod_cast (div_left_inj' (by positivity : ((n+1:ℕ):ℝ) ≠ 0)).mp hC

noncomputable def gridApprox (p : SecondFunctionalParameters) (j : Term)
    (δ : ℝ) (n : ℕ) (v : ℝ × ℝ) : ℝ :=
  ∑ i ∈ gridInner p j n, (truncatedSixthClosureCell n i).indicator
    (fun v => gamma5GainH δ (gridSample p j n i) * gainSmooth p v) v

theorem grid_approx_at_cell {p : SecondFunctionalParameters} {j : Term}
    {δ : ℝ} {n : ℕ} {i : ℕ × ℕ} {v : ℝ × ℝ}
    (hi : i ∈ gridInner p j n) (hv : v ∈ truncatedSixthClosureCell n i) :
    gridApprox p j δ n v = gamma5GainH δ (gridSample p j n i) * gainSmooth p v := by
  unfold gridApprox
  rw [sum_eq_single i]
  · exact Set.indicator_of_mem hv _
  · intro k _ hki
    exact Set.indicator_of_notMem (fun hk => hki (truncatedSixthClosure_cell_unique hk hv)) _
  · exact fun hn => False.elim (hn hi)

theorem grid_approx_zero {p : SecondFunctionalParameters} {j : Term}
    {δ : ℝ} {n : ℕ} {v : ℝ × ℝ}
    (h : ∀ i ∈ gridInner p j n, v ∉ truncatedSixthClosureCell n i) :
    gridApprox p j δ n v = 0 :=
  sum_eq_zero (fun i hi => Set.indicator_of_notMem (h i hi) _)

theorem grid_approx_measurable {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) (δ : ℝ) (n : ℕ) : Measurable (gridApprox p j δ n) := by
  apply Finset.measurable_sum
  intro i _
  exact (measurable_const.mul (gain_smooth_continuous h).measurable).indicator
    (truncatedSixthClosure_cell_measurable n i)

theorem grid_approx_bound {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) (n : ℕ) (v : ℝ × ℝ) :
    ‖gridApprox p j δ n v‖ ≤ (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1).indicator
      (fun _ => 25/(1-2*(1/p.kappa3))) v := by
  by_cases hex : ∃ i ∈ gridInner p j n, v ∈ truncatedSixthClosureCell n i
  · obtain ⟨i,hi,hv⟩ := hex
    have hu := truncatedSixthClosure_cell_mem (mem_filter.mp hi).1 hv
    rw [grid_approx_at_cell hi hv, Set.indicator_of_mem
      (show v ∈ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1 from
        ⟨⟨hu.1.1,hu.1.2.le⟩,⟨hu.2.1,hu.2.2.le⟩⟩)]
    have hh := gamma5Gain_H_bounds hδ hδhi (gridSample p j n i)
    have hk := gain_smooth_bounds h v
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hh.1 hk.1)]
    exact (mul_le_of_le_one_left hk.1 hh.2).trans hk.2
  · rw [grid_approx_zero (by simpa only [not_exists,not_and] using hex),norm_zero]
    exact Set.indicator_nonneg (fun _ _ => (gain_smooth_bounds h v).1.trans
      (gain_smooth_bounds h v).2) _

theorem grid_sample_tendsto (p : SecondFunctionalParameters) (j : Term) {v : ℝ × ℝ}
    (hx : 0 < v.1) (hy : 0 ≤ v.2) :
    Tendsto (fun n => gridSample p j n
      (truncatedSixthClosureIndex n v.1,truncatedSixthClosureIndex n v.2))
      atTop (𝓝 (Hratio p j v.1 v.2)) := by
  have hm : Tendsto (fun n : ℕ => 1 / ((n+1:ℕ):ℝ)) atTop (𝓝 (0:ℝ)) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hx' := (truncatedSixthClosure_corner_tendsto hx.le).1
  have hy' := (truncatedSixthClosure_corner_tendsto hy).1
  have hc := (gain_ratio_continuousAt p j hx.ne').tendsto.comp (hx'.prodMk_nhds hy')
  simpa only [gridSample,Function.comp_def,add_zero] using hc.add hm

theorem grid_approx_tendsto {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {δ : ℝ} {v : ℝ × ℝ}
    (hs : v ∈ gainRegion p j →
      1/p.S < v.1 ∧ v.1 < upperP p j ∧ lowerQ p j < v.2 ∧ v.2 < upperQ p j ∧
      v.1 < v.2 ∧ 2*v.2 < 1 ∧ v.2+2*v.1 < 1 ∧
      1 < Hratio p j v.1 v.2 ∧ Hratio p j v.1 v.2 < 3)
    (hc : ContinuousAt (gamma5GainH δ) (Hratio p j v.1 v.2)) :
    Tendsto (fun n => gridApprox p j δ n v) atTop (𝓝 (gainKernel p j δ v)) := by
  by_cases hv : v ∈ gainRegion p j
  · have hs := hs hv
    have hb := pairRegion_bounds h j hv.1
    have he := gain_endpoint_order h j
    have hx0 : 0 < v.1 := by linarith [he.1,hb.1]
    have hy0 : 0 ≤ v.2 := hx0.le.trans hb.2.2.1
    have hx := truncatedSixthClosure_corner_tendsto hx0.le
    have hy := truncatedSixthClosure_corner_tendsto hy0
    have hsample := grid_sample_tendsto p j hx0 hy0
    have h1 := hx.1.eventually (lt_mem_nhds hs.1)
    have h2 := Filter.Tendsto.eventually_lt hx.2 hy.1 hs.2.2.2.2.1
    have h3 := hx.2.eventually (gt_mem_nhds hs.2.1)
    have h4 := hy.1.eventually (lt_mem_nhds hs.2.2.1)
    have h5 := hy.2.eventually (gt_mem_nhds hs.2.2.2.1)
    have h6 := (hy.2.const_mul 2).eventually (gt_mem_nhds hs.2.2.2.2.2.1)
    have h7 := (hy.2.add (hx.2.const_mul 2)).eventually (gt_mem_nhds hs.2.2.2.2.2.2.1)
    have h8 := hsample.eventually (lt_mem_nhds hs.2.2.2.2.2.2.2.1)
    have h9 := hsample.eventually (gt_mem_nhds hs.2.2.2.2.2.2.2.2)
    have hlim := (hc.tendsto.comp hsample).mul_const (gainSmooth p v)
    have heq : gainKernel p j δ v = gamma5GainH δ (Hratio p j v.1 v.2)*gainSmooth p v := by
      rw [gainKernel,if_pos hv,gain_smooth_eq ⟨hb.1,hb.2.1⟩ ⟨hb.1.trans hb.2.2.1,hb.2.2.2⟩]
      exact div_eq_mul_one_div _ _
    rw [heq]
    apply hlim.congr'
    filter_upwards [h1,h2,h3,h4,h5,h6,h7,h8,h9] with n hn1 hn2 hn3 hn4 hn5 hn6 hn7 hn8 hn9
    have hi : (truncatedSixthClosureIndex n v.1,truncatedSixthClosureIndex n v.2) ∈
        gridInner p j n := by
      exact mem_filter.mpr ⟨mem_product.mpr
        ⟨mem_range.mpr (truncatedSixthClosure_index_lt n hx0.le (by linarith [hb.2.1,he.2.2.2.2.2.2])),
          mem_range.mpr (truncatedSixthClosure_index_lt n hy0 (by linarith [hb.2.2.2,he.2.2.2.2.2.2]))⟩,
        hn1,hn2,hn3,hn4,hn5,hn6,hn7,hn8,hn9⟩
    exact (grid_approx_at_cell hi
      ⟨truncatedSixthClosure_index_bounds n hx0.le,truncatedSixthClosure_index_bounds n hy0⟩).symm
  · have hz (n : ℕ) : gridApprox p j δ n v = 0 :=
      grid_approx_zero (fun i hi hiv => hv (grid_inner_subset h hi hiv))
    simp only [hz,gainKernel,if_neg hv]
    exact tendsto_const_nhds

theorem grid_integral_tendsto {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    Tendsto (fun n => ∫ v : ℝ × ℝ, gridApprox p j δ n v) atTop (𝓝 (gainIntegral p j δ)) := by
  rw [gain_integral_eq h j hδ hδhi]
  apply tendsto_integral_of_dominated_convergence
    ((Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1).indicator (fun _ => 25/(1-2*(1/p.kappa3))))
  · exact fun n => (grid_approx_measurable h j δ n).aestronglyMeasurable
  · exact (integrableOn_const (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne).integrable_indicator
      (measurableSet_Icc.prod measurableSet_Icc)
  · exact fun n => Eventually.of_forall (grid_approx_bound h j hδ hδhi n)
  · filter_upwards [gain_strict_ae h j,gain_H_pullback_ae h j hδ hδhi] with v hs hc
    exact grid_approx_tendsto h j hs hc

end Wu2008DoubleSieve.MotherPair
