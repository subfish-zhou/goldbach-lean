import MathlibNt.Wu2008DoubleSieve.TruncatedSixthTableIntegral

/-!
# The two moving affine boundaries at delta zero

The coefficient at source coordinate two need not vanish. The changing
indicators stabilize only away from two null lines, not everywhere.
-/

namespace Wu2008DoubleSieve

open Set Real Filter MeasureTheory
open scoped Classical Topology

theorem truncatedSixthTable_cut_stable {f : ℝ → ℝ} {a : ℝ}
    (hf : ContinuousAt f 0) (ha : a ≠ f 0) :
    ∀ᶠ δ in 𝓝 (0 : ℝ), (a ≤ f δ ↔ a ≤ f 0) := by
  rcases lt_or_gt_of_ne ha with h | h
  · filter_upwards [hf.eventually (Ioi_mem_nhds h)] with δ hδ
    exact iff_of_true hδ.le h.le
  · filter_upwards [hf.eventually (Iio_mem_nhds h)] with δ hδ
    exact iff_of_false (not_le.mpr hδ) (not_le.mpr h)

theorem truncatedSixthTable_boundaries_null :
    ∀ᵐ v : ℝ × ℝ,
      v.1 + v.2 ≠ truncatedSixthLowerC 0 - 2 * truncatedSixthLowerAlpha ∧
        v.2 ≠ truncatedSixthLowerC 0 / 2 := by
  have hm : MeasurableSet {v : ℝ × ℝ |
      v.1 + v.2 ≠ truncatedSixthLowerC 0 - 2 * truncatedSixthLowerAlpha ∧
        v.2 ≠ truncatedSixthLowerC 0 / 2} :=
    (measurableSet_eq_fun (measurable_fst.add measurable_snd) measurable_const).compl.inter
      (measurableSet_eq_fun measurable_snd measurable_const).compl
  change ∀ᵐ v : ℝ × ℝ ∂(volume.prod volume), _
  rw [Measure.ae_prod_iff_ae_ae hm]
  apply Eventually.of_forall
  intro x
  have hline : ∀ᵐ y : ℝ, y ≠ truncatedSixthLowerC 0 -
      2 * truncatedSixthLowerAlpha - x := by
    apply ae_iff.mpr
    simp
  have hhorizontal : ∀ᵐ y : ℝ, y ≠ truncatedSixthLowerC 0 / 2 := by
    apply ae_iff.mpr
    simp
  filter_upwards [hline, hhorizontal] with y hy hh
  exact ⟨fun he => hy (by linarith), hh⟩

theorem truncatedSixthTable_region_stable {v : ℝ × ℝ}
    (hline : v.1 + v.2 ≠ truncatedSixthLowerC 0 - 2 * truncatedSixthLowerAlpha)
    (hhor : v.2 ≠ truncatedSixthLowerC 0 / 2) :
    ∀ᶠ δ in 𝓝 (0 : ℝ),
      (truncatedSixthLowerAdmissibleRegion δ v.1 v.2 ↔
        truncatedSixthLowerAdmissibleRegion 0 v.1 v.2) := by
  have hc : Continuous (fun δ => truncatedSixthLowerC δ - 2 * truncatedSixthLowerAlpha) := by
    unfold truncatedSixthLowerC
    fun_prop
  have hh : Continuous (fun δ => truncatedSixthLowerC δ / 2) := by
    unfold truncatedSixthLowerC
    fun_prop
  filter_upwards [truncatedSixthTable_cut_stable hc.continuousAt hline,
    truncatedSixthTable_cut_stable hh.continuousAt hhor] with δ hδ hδ'
  simp only [truncatedSixthLowerAdmissibleRegion, truncatedSixthLowerRegion, hδ, hδ']

theorem truncatedSixthTable_kernel_ae_limit (j : Fin 9) :
    ∀ᵐ v : ℝ × ℝ, Tendsto (fun δ => truncatedSixthTableKernel δ j v)
      (𝓝 (0 : ℝ)) (𝓝 (truncatedSixthTableKernel 0 j v)) := by
  filter_upwards [truncatedSixthTable_boundaries_null] with v hv
  have hreg : Continuous (fun δ => truncatedSixthTableRegular δ j v) :=
    (truncatedSixthTable_regular_continuous j).comp
      (f := fun δ : ℝ => (δ, v)) (continuous_id.prodMk continuous_const)
  have hevent := truncatedSixthTable_region_stable hv.1 hv.2
  by_cases hr : truncatedSixthLowerAdmissibleRegion 0 v.1 v.2
  · have hlim := hreg.continuousAt.tendsto (x := (0 : ℝ))
    rw [show truncatedSixthTableKernel 0 j v = truncatedSixthTableRegular 0 j v by
      simp only [truncatedSixthTableKernel, if_pos hr]]
    apply hlim.congr'
    filter_upwards [hevent] with δ hδ
    simp only [truncatedSixthTableKernel, if_pos (hδ.mpr hr)]
  · rw [show truncatedSixthTableKernel 0 j v = 0 by
      simp only [truncatedSixthTableKernel, if_neg hr]]
    apply tendsto_const_nhds.congr'
    filter_upwards [hevent] with δ hδ
    simp only [truncatedSixthTableKernel, if_neg (fun h => hr (hδ.mp h))]

end Wu2008DoubleSieve
