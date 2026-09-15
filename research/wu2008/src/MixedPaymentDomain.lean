import MixedSixthSharp

namespace MixedPayment
open Finset Set Real Filter MeasureTheory Wu2008DoubleSieve MixedSixth
open scoped Classical Topology
noncomputable section

def highRegion (δ : ℝ) : Set (ℝ × ℝ) :=
  {v | truncatedSixthLowerRegion δ v.1 v.2 ∧ (1:ℝ)/4 ≤ v.2}

def highCover (δ : ℝ) (n : ℕ) : Set (ℝ × ℝ) :=
  ⋃ i ∈ highCells δ n, truncatedSixthClosureCell n (coarse i)

theorem highRegion_convex (δ : ℝ) : Convex ℝ (highRegion δ) := by
  intro v hv w hw a b ha hb hab
  refine ⟨(truncatedSixthMass_regions_convex δ).1 hv.1 hw.1 ha hb hab, ?_⟩
  change (1:ℝ)/4 ≤ a*v.2+b*w.2
  nlinarith [mul_le_mul_of_nonneg_left hv.2 ha, mul_le_mul_of_nonneg_left hw.2 hb]

theorem highRegion_closed (δ : ℝ) : IsClosed (highRegion δ) := by
  exact ((isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_fst continuous_const).inter
    ((isClosed_le continuous_const continuous_snd).inter
    ((isClosed_le continuous_snd continuous_const).inter
      (isClosed_le (continuous_fst.add continuous_snd) continuous_const))))).inter
    (isClosed_le continuous_const continuous_snd)

theorem highRegion_frontier (δ : ℝ) : volume (frontier (highRegion δ)) = 0 :=
  (highRegion_convex δ).addHaar_frontier volume

theorem highCover_measurable (δ : ℝ) (n : ℕ) : MeasurableSet (highCover δ n) :=
  MeasurableSet.iUnion (fun i => MeasurableSet.iUnion (fun _ =>
    truncatedSixthClosure_cell_measurable n (coarse i)))

theorem highCover_subset (δ : ℝ) (n : ℕ) : highCover δ n ⊆ highRegion δ := by
  intro v hv
  obtain ⟨i,hi,hv⟩ := mem_iUnion₂.mp hv
  have hg := high_geometry hi
  have hb : truncatedSixthLowerBeta ≤ (1:ℝ)/4 := by norm_num [truncatedSixthLowerBeta]
  change (loX n i ≤ v.1 ∧ v.1 < hiX n i) ∧
    (loY n i ≤ v.2 ∧ v.2 < hiY n i) at hv
  exact ⟨⟨hg.1.trans hv.1.1,hv.1.2.le.trans hg.2.2.2.1,
    hb.trans (hg.2.1.trans hv.2.1),hv.2.2.le.trans hg.2.2.2.2.2.1,
    (add_le_add hv.1.2.le hv.2.2.le).trans hg.2.2.2.2.2.2⟩, hg.2.1.trans hv.2.1⟩

theorem highCover_eventually {δ : ℝ} {v : ℝ × ℝ}
    (hv : v ∈ interior (highRegion δ)) : ∀ᶠ n : ℕ in atTop, v ∈ highCover δ n := by
  have hr := (interior_subset hv).1
  have hp := truncatedSixthLower_parameters
  have hx0 := hp.1.trans_le hr.1
  have hy0 := (hp.1.trans hp.2.1).trans_le hr.2.2.1
  have hx1 : v.1 < 1 := by linarith [hr.2.1,hp.2.2.1,hp.2.2.2.1]
  have hy1 : v.2 < 1 := by linarith [hr.2.2.2.1,hp.2.2.2.1]
  let j := fun n => (truncatedSixthClosureIndex n v.1,truncatedSixthClosureIndex n v.2)
  have hx := truncatedSixthClosure_corner_tendsto hx0.le
  have hy := truncatedSixthClosure_corner_tendsto hy0.le
  have hlo : Tendsto (fun n => truncatedSixthClosureLower n (j n)) atTop (𝓝 v) :=
    hx.1.prodMk_nhds hy.1
  have hup : Tendsto (fun n => truncatedSixthClosureUpper n (j n)) atTop (𝓝 v) :=
    hx.2.prodMk_nhds hy.2
  filter_upwards [hlo.eventually (mem_of_superset (isOpen_interior.mem_nhds hv) interior_subset),
    hup.eventually (mem_of_superset (isOpen_interior.mem_nhds hv) interior_subset)] with n hnlo hnup
  apply mem_iUnion₂.mpr
  refine ⟨Nat.pair (j n).1 (j n).2, ?_, ?_⟩
  · apply mem_image.mpr
    refine ⟨j n,mem_filter.mpr ⟨?_, hnlo.1.1,hnlo.2,hnup.1⟩,rfl⟩
    exact mem_product.mpr ⟨mem_range.mpr (truncatedSixthClosure_index_lt n hx0.le hx1),
      mem_range.mpr (truncatedSixthClosure_index_lt n hy0.le hy1)⟩
  · simpa only [coarse,Nat.unpair_pair,truncatedSixthClosureCell,j,mem_prod,Set.mem_Ico] using
      And.intro (truncatedSixthClosure_index_bounds n hx0.le)
        (truncatedSixthClosure_index_bounds n hy0.le)

/-- Exhaustion of the actual already-constructed high cells; arbitrary integrable
signed kernels are allowed, so the result is not a positivity-only substitute. -/
theorem highCover_integral_tendsto (δ : ℝ) {f : ℝ × ℝ → ℝ} (hf : Integrable f) :
    Tendsto (fun n => ∫ v, (highCover δ n).indicator f v) atTop
      (𝓝 (∫ v, (highRegion δ).indicator f v)) := by
  apply tendsto_integral_of_dominated_convergence (fun v => ‖f v‖)
  · intro n
    exact (hf.indicator (highCover_measurable δ n)).aestronglyMeasurable
  · exact hf.norm
  · intro n
    exact Eventually.of_forall (fun v => norm_indicator_le_norm_self _ _)
  · filter_upwards [compl_mem_ae_iff.mpr (highRegion_frontier δ)] with v hv
    by_cases hmem : v ∈ highRegion δ
    · have hin : v ∈ interior (highRegion δ) := by
        by_contra h
        exact hv ⟨subset_closure hmem,h⟩
      apply tendsto_const_nhds.congr'
      filter_upwards [highCover_eventually hin] with n hn
      simp only [indicator_of_mem hn,indicator_of_mem hmem]
    · have hnot : ∀ n, v ∉ highCover δ n := fun n hn => hmem (highCover_subset δ n hn)
      simp only [indicator_of_notMem hmem,indicator_of_notMem (hnot _)]
      exact tendsto_const_nhds

end
end MixedPayment
