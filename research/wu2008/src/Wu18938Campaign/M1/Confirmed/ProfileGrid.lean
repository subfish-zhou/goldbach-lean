import MathlibNt.Wu2008DoubleSieve.MotherPairGainSufficiency

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.ProfileGrid

open Wu2008DoubleSieve MotherPair Finset Set Real Filter MeasureTheory
open scoped Classical Topology

def kernel (p : SecondFunctionalParameters) (j : Term) (H : ℝ → ℝ)
    (v : ℝ × ℝ) : ℝ :=
  if v ∈ gainRegion p j then H (Hratio p j v.1 v.2) * gainSmooth p v else 0

def approximation (p : SecondFunctionalParameters) (j : Term) (H : ℝ → ℝ)
    (n : ℕ) (v : ℝ × ℝ) : ℝ :=
  ∑ i ∈ gridInner p j n, (truncatedSixthClosureCell n i).indicator
    (fun v => H (gridSample p j n i) * gainSmooth p v) v

theorem at_cell {p : SecondFunctionalParameters} {j : Term} {H : ℝ → ℝ}
    {n : ℕ} {i : ℕ × ℕ} {v : ℝ × ℝ}
    (hi : i ∈ gridInner p j n) (hv : v ∈ truncatedSixthClosureCell n i) :
    approximation p j H n v = H (gridSample p j n i) * gainSmooth p v := by
  unfold approximation
  rw [sum_eq_single i]
  · exact Set.indicator_of_mem hv _
  · intro k _ hki
    exact Set.indicator_of_notMem (fun hk => hki (truncatedSixthClosure_cell_unique hk hv)) _
  · exact fun hn => False.elim (hn hi)

theorem outside {p : SecondFunctionalParameters} {j : Term} {H : ℝ → ℝ}
    {n : ℕ} {v : ℝ × ℝ}
    (h : ∀ i ∈ gridInner p j n, v ∉ truncatedSixthClosureCell n i) :
    approximation p j H n v = 0 :=
  sum_eq_zero (fun i hi => Set.indicator_of_notMem (h i hi) _)

theorem measurable_approximation {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) (H : ℝ → ℝ) (n : ℕ) : Measurable (approximation p j H n) := by
  apply Finset.measurable_sum
  intro i _
  exact (measurable_const.mul (gain_smooth_continuous hp).measurable).indicator
    (truncatedSixthClosure_cell_measurable n i)

theorem approximation_bound {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) {H : ℝ → ℝ} (hH : ∀ s ∈ Icc (1 : ℝ) 3, 0 ≤ H s ∧ H s ≤ 1)
    (n : ℕ) (v : ℝ × ℝ) :
    ‖approximation p j H n v‖ ≤ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1).indicator
      (fun _ => 25 / (1 - 2 * (1 / p.kappa3))) v := by
  by_cases hex : ∃ i ∈ gridInner p j n, v ∈ truncatedSixthClosureCell n i
  · obtain ⟨i,hi,hv⟩ := hex
    have hu := truncatedSixthClosure_cell_mem (mem_filter.mp hi).1 hv
    rw [at_cell hi hv,Set.indicator_of_mem
      (show v ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 from
        ⟨⟨hu.1.1,hu.1.2.le⟩,⟨hu.2.1,hu.2.2.le⟩⟩)]
    let hs := gridRectangle p j n ⟨i,hi⟩
    have hh := hH hs.sample ⟨hs.sample_lower.le,hs.sample_upper.le⟩
    change 0 ≤ H (gridSample p j n i) ∧ H (gridSample p j n i) ≤ 1 at hh
    have hk := gain_smooth_bounds hp v
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hh.1 hk.1)]
    exact (mul_le_of_le_one_left hk.1 hh.2).trans hk.2
  · rw [outside (by simpa only [not_exists,not_and] using hex),norm_zero]
    exact Set.indicator_nonneg (fun _ _ => (gain_smooth_bounds hp v).1.trans
      (gain_smooth_bounds hp v).2) _

theorem approximation_tendsto {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) {H : ℝ → ℝ} {v : ℝ × ℝ}
    (hs : v ∈ gainRegion p j →
      1 / p.S < v.1 ∧ v.1 < upperP p j ∧ lowerQ p j < v.2 ∧ v.2 < upperQ p j ∧
      v.1 < v.2 ∧ 2 * v.2 < 1 ∧ v.2 + 2 * v.1 < 1 ∧
      1 < Hratio p j v.1 v.2 ∧ Hratio p j v.1 v.2 < 3)
    (hc : ContinuousAt H (Hratio p j v.1 v.2)) :
    Tendsto (fun n => approximation p j H n v) atTop (𝓝 (kernel p j H v)) := by
  by_cases hv : v ∈ gainRegion p j
  · have hs := hs hv
    have hb := pairRegion_bounds hp j hv.1
    have he := gain_endpoint_order hp j
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
    rw [kernel,if_pos hv]
    apply ((hc.tendsto.comp hsample).mul_const (gainSmooth p v)).congr'
    filter_upwards [h1,h2,h3,h4,h5,h6,h7,h8,h9] with n hn1 hn2 hn3 hn4 hn5 hn6 hn7 hn8 hn9
    have hi : (truncatedSixthClosureIndex n v.1,truncatedSixthClosureIndex n v.2) ∈
        gridInner p j n := by
      exact mem_filter.mpr ⟨mem_product.mpr
        ⟨mem_range.mpr (truncatedSixthClosure_index_lt n hx0.le (by linarith [hb.2.1,he.2.2.2.2.2.2])),
          mem_range.mpr (truncatedSixthClosure_index_lt n hy0 (by linarith [hb.2.2.2,he.2.2.2.2.2.2]))⟩,
        hn1,hn2,hn3,hn4,hn5,hn6,hn7,hn8,hn9⟩
    exact (at_cell hi
      ⟨truncatedSixthClosure_index_bounds n hx0.le,truncatedSixthClosure_index_bounds n hy0⟩).symm
  · have hz (n : ℕ) : approximation p j H n v = 0 :=
      outside (fun i hi hiv => hv (grid_inner_subset hp hi hiv))
    simp only [hz,kernel,if_neg hv]
    exact tendsto_const_nhds

theorem monotone_pullback_ae {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) {H : ℝ → ℝ} (hH : Antitone H) :
    ∀ᵐ v : ℝ × ℝ, ContinuousAt H (Hratio p j v.1 v.2) := by
  have hcount : Set.Countable {s | ¬ ContinuousAt H s} := hH.countable_not_continuousAt
  let : Countable {s : ℝ // ¬ ContinuousAt H s} := hcount.to_subtype
  have hn : ∀ᵐ v : ℝ × ℝ, ∀ s : {s : ℝ // ¬ ContinuousAt H s},
      Hratio p j v.1 v.2 ≠ s.val :=
    ae_all_iff.mpr (fun s => gain_ratio_ne_ae hp j s.val)
  filter_upwards [hn] with v hv
  by_contra hc
  exact hv ⟨_,hc⟩ rfl

theorem integral_tendsto {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) {H : ℝ → ℝ} (hm : Antitone H)
    (hH : ∀ s ∈ Icc (1 : ℝ) 3, 0 ≤ H s ∧ H s ≤ 1) :
    Tendsto (fun n => ∫ v : ℝ × ℝ, approximation p j H n v)
      atTop (𝓝 (∫ v : ℝ × ℝ, kernel p j H v)) := by
  apply tendsto_integral_of_dominated_convergence
    ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1).indicator
      (fun _ => 25 / (1 - 2 * (1 / p.kappa3))))
  · exact fun n => (measurable_approximation hp j H n).aestronglyMeasurable
  · exact (integrableOn_const (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne).integrable_indicator
      (measurableSet_Icc.prod measurableSet_Icc)
  · exact fun n => Eventually.of_forall (approximation_bound hp j hH n)
  · filter_upwards [gain_strict_ae hp j,monotone_pullback_ae hp j hm] with v hs hc
    exact approximation_tendsto hp j hs hc

theorem integral_sum {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) (H : ℝ → ℝ) (n : ℕ) :
    (∫ v : ℝ × ℝ, approximation p j H n v) =
      ∑ r ∈ gridFamily p j n, H r.sample * rectIntegral r.A r.B r.C r.D := by
  have hi (i : ℕ × ℕ) : Integrable ((truncatedSixthClosureCell n i).indicator
      (fun v => H (gridSample p j n i) * gainSmooth p v)) := by
    apply IntegrableOn.integrable_indicator _ (truncatedSixthClosure_cell_measurable n i)
    exact (((continuous_const.mul (gain_smooth_continuous hp)).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
        (Set.prod_mono Ico_subset_Icc_self Ico_subset_Icc_self))
  unfold gridFamily
  rw [Finset.sum_image (grid_rectangle_injective p j n).injOn]
  unfold approximation
  rw [integral_finsetSum _ (fun i _ => hi i),← Finset.sum_attach]
  change (∑ i : {i // i ∈ gridInner p j n}, _) = _
  apply sum_congr rfl
  intro i _
  let r := gridRectangle p j n i
  have heq : (truncatedSixthClosureCell n i.val).indicator
      (fun v => H (gridSample p j n i.val) * gainSmooth p v) =
      fun v => H r.sample * (Ico r.A r.B ×ˢ Ico r.C r.D).indicator (gainSmooth p) v := by
    funext v
    change (truncatedSixthClosureCell n i.val).indicator
      (fun v => H r.sample * gainSmooth p v) v =
        H r.sample * (truncatedSixthClosureCell n i.val).indicator (gainSmooth p) v
    by_cases hv : v ∈ truncatedSixthClosureCell n i.val
    · simp only [Set.indicator_of_mem hv]
    · simp only [Set.indicator_of_notMem hv,mul_zero]
  rw [heq,integral_const_mul,gain_smooth_indicator hp r]

theorem sufficient_family {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) {H : ℝ → ℝ} (hm : Antitone H)
    (hH : ∀ s ∈ Icc (1 : ℝ) 3, 0 ≤ H s ∧ H s ≤ 1) {ε : ℝ} (he : 0 < ε) :
    ∃ F : Finset (GainRectangle p j),
      (F : Set (GainRectangle p j)).Pairwise (fun r s =>
        Disjoint (Ico r.A r.B ×ˢ Ico r.C r.D) (Ico s.A s.B ×ˢ Ico s.C s.D)) ∧
      (∫ v : ℝ × ℝ, kernel p j H v) - ε <
        ∑ r ∈ F, H r.sample * rectIntegral r.A r.B r.C r.D := by
  obtain ⟨n,hn⟩ := ((integral_tendsto hp j hm hH).eventually
    (lt_mem_nhds (sub_lt_self _ he))).exists
  rw [integral_sum hp j H n] at hn
  exact ⟨gridFamily p j n,grid_family_pairwise p j n,hn⟩

end Wu18938Campaign.M1.Confirmed.ProfileGrid
