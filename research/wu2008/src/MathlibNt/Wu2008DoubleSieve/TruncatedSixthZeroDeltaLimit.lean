import MathlibNt.Wu2008DoubleSieve.TruncatedSixthZeroDeltaClassical

/-!
# The classical right limit at delta zero

The canonical coefficient is zero at the moving boundary. The
regularized classical kernel therefore represents the literal
integral on the fixed rectangle, including at delta zero.
-/

namespace Wu2008DoubleSieve

open Set Real Filter MeasureTheory
open scoped Classical Topology

theorem truncatedSixthZeroDelta_extension_continuous :
    Continuous truncatedSixthZeroDeltaExtension := by
  have hinner : Continuous (fun p : ℝ × ℝ =>
      ∫ y in Icc truncatedSixthLowerBeta truncatedSixthLowerSigma,
        truncatedSixthZeroDeltaRegular p.1 (p.2, y)) := by
    apply continuous_parametric_integral_of_continuous
      (f := fun (p : ℝ × ℝ) (y : ℝ) => truncatedSixthZeroDeltaRegular p.1 (p.2, y))
      (μ := volume) _ isCompact_Icc
    change Continuous (fun p : (ℝ × ℝ) × ℝ => truncatedSixthZeroDeltaRegular p.1.1 (p.1.2, p.2))
    exact truncatedSixthZeroDelta_regular_continuous.comp
      (f := fun p : (ℝ × ℝ) × ℝ => (p.1.1, (p.1.2, p.2)))
      (show Continuous (fun p : (ℝ × ℝ) × ℝ => (p.1.1, (p.1.2, p.2))) by fun_prop)
  have houter : Continuous (fun δ : ℝ =>
      ∫ x in Icc truncatedSixthLowerAlpha truncatedSixthLowerBeta,
        ∫ y in Icc truncatedSixthLowerBeta truncatedSixthLowerSigma,
          truncatedSixthZeroDeltaRegular δ (x, y)) :=
    continuous_parametric_integral_of_continuous
      (f := fun (δ x : ℝ) => ∫ y in Icc truncatedSixthLowerBeta truncatedSixthLowerSigma,
        truncatedSixthZeroDeltaRegular δ (x, y)) (μ := volume) hinner isCompact_Icc
  have heq (δ : ℝ) : truncatedSixthZeroDeltaExtension δ =
      4 * ∫ x in Icc truncatedSixthLowerAlpha truncatedSixthLowerBeta,
        ∫ y in Icc truncatedSixthLowerBeta truncatedSixthLowerSigma,
          truncatedSixthZeroDeltaRegular δ (x, y) := by
    unfold truncatedSixthZeroDeltaExtension
    rw [intervalIntegral.integral_of_le truncatedSixthLower_parameters.2.1.le,
      ← integral_Icc_eq_integral_Ioc]
    simp_rw [intervalIntegral.integral_of_le truncatedSixthLower_parameters.2.2.1.le,
      ← integral_Icc_eq_integral_Ioc]
  change Continuous (fun δ => truncatedSixthZeroDeltaExtension δ)
  simp_rw [heq]
  exact houter.const_mul 4

theorem truncatedSixthZeroDelta_Fdelta_right_limit :
    Tendsto truncatedSixthLowerFdelta (𝓝[>] (0 : ℝ)) (𝓝 truncatedSixthLowerF6lin) := by
  have hlim : Tendsto truncatedSixthZeroDeltaExtension (𝓝[>] (0 : ℝ))
      (𝓝 (truncatedSixthZeroDeltaExtension 0)) :=
    truncatedSixthZeroDelta_extension_continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [truncatedSixthZeroDelta_extension_eq (le_refl 0)] at hlim
  change Tendsto truncatedSixthZeroDeltaExtension (𝓝[>] (0 : ℝ)) (𝓝 truncatedSixthLowerF6lin) at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact truncatedSixthZeroDelta_extension_eq (le_of_lt hδ)

theorem truncatedSixthZeroDelta_Fdelta_close {ε : ℝ} (hε : 0 < ε) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ < δ0 →
        |truncatedSixthLowerFdelta δ - truncatedSixthLowerF6lin| < ε := by
  obtain ⟨r, hr, hclose⟩ :=
    Metric.tendsto_nhdsWithin_nhds.mp truncatedSixthZeroDelta_Fdelta_right_limit ε hε
  refine ⟨min r (1 / 100), lt_min hr (by norm_num), min_le_right _ _, ?_⟩
  intro δ hδ hδ0
  have hdist : dist δ 0 < r := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hδ] using hδ0.trans_le (min_le_left _ _)
  exact (show dist (truncatedSixthLowerFdelta δ) truncatedSixthLowerF6lin < ε from
    hclose hδ hdist)

end Wu2008DoubleSieve
