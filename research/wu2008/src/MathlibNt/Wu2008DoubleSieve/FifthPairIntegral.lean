import MathlibNt.Wu2008DoubleSieve.FifthPairDCT
namespace Wu2008DoubleSieve
open Finset Set Real Filter MeasureTheory
open scoped Classical Topology

/-- Only a continuous off-support extension; it is exactly the original kernel on the triangle. -/
noncomputable def fifthPairRegular (δ : ℝ) (v : ℝ × ℝ) : ℝ :=
  wuLowerCoefficient (truncatedSixthMassClip (truncatedSixthLowerS δ v.1 v.2)) /
    (max truncatedSixthLowerAlpha v.1 * max truncatedSixthLowerAlpha v.2 *
      max (2 * truncatedSixthLowerAlpha) (truncatedSixthLowerC δ - v.1 - v.2))

theorem fifthPair_region_compact : IsCompact fifthPairRegion := by
  apply (isCompact_Icc (a := (truncatedSixthLowerAlpha, truncatedSixthLowerAlpha))
    (b := (truncatedSixthLowerBeta, truncatedSixthLowerBeta))).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst continuous_snd).inter (isClosed_le continuous_snd continuous_const))
  · intro v hv
    exact ⟨⟨hv.1, hv.1.trans hv.2.1⟩, ⟨hv.2.1.trans hv.2.2, hv.2.2⟩⟩

theorem fifthPair_regular_continuous :
    Continuous (fun p : ℝ × (ℝ × ℝ) => fifthPairRegular p.1 p.2) := by
  have hs : Continuous (fun p : ℝ × (ℝ × ℝ) => truncatedSixthLowerS p.1 p.2.1 p.2.2) := by
    unfold truncatedSixthLowerS truncatedSixthLowerC
    fun_prop
  apply (truncatedSixthMass_clipped_classical_continuous.comp hs).div
    (by unfold truncatedSixthLowerC; fun_prop)
  intro p
  have hα := truncatedSixthLower_parameters.1
  have hx := hα.trans_le (le_max_left truncatedSixthLowerAlpha p.2.1)
  have hy := hα.trans_le (le_max_left truncatedSixthLowerAlpha p.2.2)
  have hz := (mul_pos (by norm_num : (0 : ℝ) < 2) hα).trans_le
    (le_max_left (2 * truncatedSixthLowerAlpha) (truncatedSixthLowerC p.1 - p.2.1 - p.2.2))
  exact (mul_pos (mul_pos hx hy) hz).ne'

theorem fifthPair_kernel_regular {δ : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 1 / 1000) :
    fifthPairKernel δ = fifthPairRegion.indicator (fifthPairRegular δ) := by
  funext v
  by_cases hv : v ∈ fifthPairRegion
  · have hb := fifthPair_region_bounds hδ hδhi hv
    simp only [fifthPairKernel, if_pos hv, Set.indicator_of_mem hv, fifthPairRegular,
      truncatedSixthClosureCoefficient, Bool.false_eq_true, if_false,
      max_eq_right hv.1, max_eq_right (hv.1.trans hv.2.1), max_eq_right hb.2.2.1]
  · simp only [fifthPairKernel, if_neg hv, Set.indicator_of_notMem hv]

theorem fifthPair_kernel_integrable {δ : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 1 / 1000) :
    Integrable (fifthPairKernel δ) := by
  rw [fifthPair_kernel_regular hδ hδhi]
  have hc : Continuous (fifthPairRegular δ) :=
    fifthPair_regular_continuous.comp (f := fun v : ℝ × ℝ => (δ, v))
      (continuous_const.prodMk continuous_id)
  exact (hc.continuousOn.integrableOn_compact fifthPair_region_compact).integrable_indicator
    fifthPair_region_compact.isClosed.measurableSet

theorem fifthPair_kernel_original {δ : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 1 / 1000)
    {v : ℝ × ℝ} (hv : v ∈ fifthPairRegion) :
    fifthPairKernel δ v = wuLowerCoefficient (truncatedSixthLowerS δ v.1 v.2) /
      (v.1 * v.2 * (truncatedSixthLowerC δ - v.1 - v.2)) := by
  have hb := fifthPair_region_bounds hδ hδhi hv
  simp only [fifthPairKernel, if_pos hv, truncatedSixthClosureCoefficient,
    Bool.false_eq_true, if_false, truncatedSixthMass_clip_eq hb.2.2.2]

/-- Exact iterated integral over the entire triangle, including its boundary. -/
theorem fifthPair_literal_integral {δ : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 1 / 1000) :
    fifthPairFdelta δ = 4 * ∫ v : ℝ × ℝ, fifthPairKernel δ v := by
  have hp := truncatedSixthLower_parameters
  have houter : Function.support (fun y => ∫ x, fifthPairKernel δ (x,y)) ⊆
      Set.Icc truncatedSixthLowerAlpha truncatedSixthLowerBeta := by
    intro y hy
    by_contra h
    apply hy
    change (∫ x, fifthPairKernel δ (x,y)) = 0
    have hz : (fun x => fifthPairKernel δ (x,y)) = 0 := by
      funext x
      have hn : (x,y) ∉ fifthPairRegion := fun hv => h ⟨hv.1.trans hv.2.1, hv.2.2⟩
      simp [fifthPairKernel, hn]
    rw [hz]
    simp
  rw [show (∫ v : ℝ × ℝ, fifthPairKernel δ v) = ∫ y, ∫ x, fifthPairKernel δ (x,y) from
      integral_prod_symm _ (fifthPair_kernel_integrable hδ hδhi),
    truncatedSixthMass_integral_eq_interval hp.2.1.le houter]
  unfold fifthPairFdelta
  congr 1
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le hp.2.1.le] at hy
  have hinner : Function.support (fun x => fifthPairKernel δ (x,y)) ⊆
      Set.Icc truncatedSixthLowerAlpha y := by
    intro x hx
    by_cases hv : (x,y) ∈ fifthPairRegion
    · exact ⟨hv.1, hv.2.1⟩
    · exact False.elim (hx (by simp [fifthPairKernel, hv]))
  dsimp only
  rw [truncatedSixthMass_integral_eq_interval hy.1 hinner]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le hy.1] at hx
  exact (fifthPair_kernel_original hδ hδhi (v := (x,y)) ⟨hx.1, hx.2, hy.2⟩).symm

end Wu2008DoubleSieve
