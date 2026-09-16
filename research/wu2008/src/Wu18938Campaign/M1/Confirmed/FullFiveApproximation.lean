import Wu18938Campaign.M1.Confirmed.FullFiveGrid
import Wu18938Campaign.M1.Confirmed.FullFiveFamily

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.FullFive

open Wu2008DoubleSieve MotherPair Finset Set Real Filter MeasureTheory
open scoped Classical Topology

theorem approximation_tendsto {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    {H : ℝ → ℝ} {v : ℝ × ℝ}
    (hs : v ∈ domain p →
      1 / p.S < v.1 ∧ v.1 < v.2 ∧ v.2 < 1 / p.kappa2 ∧
      2 * v.2 < 1 ∧ 1 < p.S * (1 - v.1 - v.2) ∧ p.S * (1 - v.1 - v.2) < 3)
    (hc : ContinuousAt H (p.S * (1 - v.1 - v.2))) :
    Tendsto (fun n => approximation p H n v) atTop (𝓝 (kernel p H v)) := by
  by_cases hv : v ∈ domain p
  · have hs := hs hv
    have he := parameter_order hp
    have hx0 : 0 < v.1 := by linarith [he.1,hv.1]
    have hy0 : 0 ≤ v.2 := hx0.le.trans hv.2.2.1
    have hx := truncatedSixthClosure_corner_tendsto hx0.le
    have hy := truncatedSixthClosure_corner_tendsto hy0
    have hsample := grid_sample_tendsto p .gammaFive hx0 hy0
    have h1 := hx.1.eventually (lt_mem_nhds hs.1)
    have h2 := Filter.Tendsto.eventually_lt hx.2 hy.1 hs.2.1
    have h3 := hy.2.eventually (gt_mem_nhds hs.2.2.1)
    have h4 := (hy.2.const_mul 2).eventually (gt_mem_nhds hs.2.2.2.1)
    have h5 := hsample.eventually (lt_mem_nhds hs.2.2.2.2.1)
    have h6 := hsample.eventually (gt_mem_nhds hs.2.2.2.2.2)
    rw [kernel,if_pos hv]
    apply ((hc.tendsto.comp hsample).mul_const (gainSmooth p v)).congr'
    filter_upwards [h1,h2,h3,h4,h5,h6] with n hn1 hn2 hn3 hn4 hn5 hn6
    have hi : (truncatedSixthClosureIndex n v.1,truncatedSixthClosureIndex n v.2) ∈
        gridInner p n := by
      exact mem_filter.mpr ⟨mem_product.mpr
        ⟨mem_range.mpr (truncatedSixthClosure_index_lt n hx0.le
          (by linarith [hv.2.1,he.2.2.2.1,he.2.2.2.2.1,he.2.2.2.2.2])),
          mem_range.mpr (truncatedSixthClosure_index_lt n hy0 (by linarith [hs.2.2.2.1]))⟩,
        hn1,hn2,hn3,hn4,hn5,hn6⟩
    exact (at_cell hi
      ⟨truncatedSixthClosure_index_bounds n hx0.le,truncatedSixthClosure_index_bounds n hy0⟩).symm
  · have hz (n : ℕ) : approximation p H n v = 0 :=
      outside (fun i hi hiv => hv (grid_inner_subset hi hiv))
    simp only [hz,kernel,if_neg hv]
    exact tendsto_const_nhds

theorem integral_tendsto {p : SecondFunctionalParameters} (hp : WuPaper.R2Gamma5.FullParameters p)
    {H : ℝ → ℝ} (hm : Antitone H)
    (hH : ∀ s ∈ Icc (1 : ℝ) 3, 0 ≤ H s ∧ H s ≤ 1) :
    Tendsto (fun n => ∫ v : ℝ × ℝ, approximation p H n v)
      atTop (𝓝 (∫ v : ℝ × ℝ, kernel p H v)) := by
  apply tendsto_integral_of_dominated_convergence
    ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1).indicator
      (fun _ => 25 / (1 - 2 * (1 / p.kappa3))))
  · intro n
    apply Measurable.aestronglyMeasurable
    apply Finset.measurable_sum
    intro i _
    exact (measurable_const.mul (gain_smooth_continuous hp.toAnalyticParameters).measurable).indicator
      (truncatedSixthClosure_cell_measurable n i)
  · exact (integrableOn_const (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne).integrable_indicator
      (measurableSet_Icc.prod measurableSet_Icc)
  · exact fun n => Filter.Eventually.of_forall (approximation_bound hp.toAnalyticParameters hH n)
  · filter_upwards [strict_ae hp,
      ProfileGrid.monotone_pullback_ae hp.toAnalyticParameters .gammaFive hm] with v hs hc
    exact approximation_tendsto hp.toAnalyticParameters hs hc

theorem integral_sum {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (H : ℝ → ℝ) (n : ℕ) :
    (∫ v : ℝ × ℝ, approximation p H n v) =
      ∑ r ∈ gridFamily p n, H r.sample * rectIntegral r.A r.B r.C r.D := by
  have hi (i : ℕ × ℕ) : Integrable ((truncatedSixthClosureCell n i).indicator
      (fun v => H (gridSample p .gammaFive n i) * gainSmooth p v)) := by
    apply IntegrableOn.integrable_indicator _ (truncatedSixthClosure_cell_measurable n i)
    exact (((continuous_const.mul (gain_smooth_continuous hp)).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
        (Set.prod_mono Ico_subset_Icc_self Ico_subset_Icc_self))
  unfold gridFamily
  rw [Finset.sum_image (grid_rectangle_injective p n).injOn]
  unfold approximation
  rw [integral_finsetSum _ (fun i _ => hi i),← Finset.sum_attach]
  change (∑ i : {i // i ∈ gridInner p n}, _) = _
  apply sum_congr rfl
  intro i _
  let r := gridRectangle p n i
  have heq : (truncatedSixthClosureCell n i.val).indicator
      (fun v => H (gridSample p .gammaFive n i.val) * gainSmooth p v) =
      fun v => H r.sample * (Ico r.A r.B ×ˢ Ico r.C r.D).indicator (gainSmooth p) v := by
    funext v
    change (truncatedSixthClosureCell n i.val).indicator
      (fun v => H r.sample * gainSmooth p v) v =
        H r.sample * (truncatedSixthClosureCell n i.val).indicator (gainSmooth p) v
    by_cases hv : v ∈ truncatedSixthClosureCell n i.val
    · simp only [Set.indicator_of_mem hv]
    · simp only [Set.indicator_of_notMem hv,mul_zero]
  rw [heq,integral_const_mul,smooth_indicator hp r]

theorem sufficient_family {p : SecondFunctionalParameters} (hp : WuPaper.R2Gamma5.FullParameters p)
    {H : ℝ → ℝ} (hm : Antitone H)
    (hH : ∀ s ∈ Icc (1 : ℝ) 3, 0 ≤ H s ∧ H s ≤ 1) {ε : ℝ} (he : 0 < ε) :
    ∃ F : Finset (Rectangle p),
      (F : Set (Rectangle p)).Pairwise (fun r s =>
        Disjoint (Ico r.A r.B ×ˢ Ico r.C r.D) (Ico s.A s.B ×ˢ Ico s.C s.D)) ∧
      (∫ v : ℝ × ℝ, kernel p H v) - ε <
        ∑ r ∈ F, H r.sample * rectIntegral r.A r.B r.C r.D := by
  obtain ⟨n,hn⟩ := ((integral_tendsto hp hm hH).eventually
    (lt_mem_nhds (sub_lt_self _ he))).exists
  rw [integral_sum hp.toAnalyticParameters H n] at hn
  exact ⟨gridFamily p n,grid_family_pairwise p n,hn⟩

end Wu18938Campaign.M1.Confirmed.FullFive
