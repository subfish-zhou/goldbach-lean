import W01ContinuousCount

/-! Monotone continuous count coefficients let independent node bounds be combined. -/
noncomputable section
namespace WuTarget.W01Continuous
open Real Set MeasureTheory NodeExtension Wu2008DoubleSieve QuarterTrim
open scoped Classical Interval

theorem upperProfile_mono {x y : Fin 9 → ℝ} (hxy : ∀ k, x k ≤ y k) (t : ℝ) :
    upperProfile x t ≤ upperProfile y t := by
  unfold upperProfile
  apply add_le_add
  · by_cases ht : t ∈ Icc 1 (rNode 2)
    · simpa only [indicator_of_mem ht] using hxy 0
    · simp only [indicator_of_notMem ht, le_refl]
  · apply Finset.sum_le_sum
    intro i hi
    by_cases ht : t ∈ Ioc (rNode (i-1)) (rNode i)
    · simpa only [indicator_of_mem ht] using
        extendedNode_mono hxy (by have := (Finset.mem_Icc.mp hi).1; omega)
          (Finset.mem_Icc.mp hi).2
    · simp only [indicator_of_notMem ht, le_refl]

theorem hContinuous_mono {x y : Fin 9 → ℝ} (hxy : ∀ k, x k ≤ y k)
    {s : ℝ} (hs : s ∈ Icc 2 (41/10)) : hContinuous x s ≤ hContinuous y s := by
  unfold hContinuous
  apply intervalIntegral.integral_mono_on (by norm_num [rNode]; linarith [hs.2])
    (upperProfile_div_integrable x).intervalIntegrable
    (upperProfile_div_integrable y).intervalIntegrable
  intro t ht
  exact div_le_div_of_nonneg_right (upperProfile_mono hxy t) (by linarith [hs.1, ht.1])

theorem continuousGain_mono {x y : Fin 9 → ℝ}
    (hx : ∀ k, 0 ≤ x k) (hxy : ∀ k, x k ≤ y k) : continuousGain x ≤ continuousGain y := by
  have hy : ∀ k, 0 ≤ y k := fun k => (hx k).trans (hxy k)
  unfold continuousGain continuousGamma
  apply mul_le_mul_of_nonneg_left
    (integral_mono (continuousUniform_integrable hx le_rfl)
      (continuousUniform_integrable hy le_rfl) ?_) (by norm_num)
  intro v
  unfold continuousUniform
  split_ifs with hv
  · unfold kernel
    exact div_le_div_of_nonneg_right (hContinuous_mono hxy (u_bounds hv))
      (DirectFiniteF6.denominator_bounds hv).1.le
  · exact le_rfl

theorem continuousCoefficient_mono {x y : Fin 9 → ℝ}
    (hx : ∀ k, 0 ≤ x k) (hxy : ∀ k, x k ≤ y k) :
    continuousCoefficient x ≤ continuousCoefficient y := by
  have h := continuousGain_mono hx hxy
  unfold continuousCoefficient
  linarith only [h]

end WuTarget.W01Continuous
#print axioms WuTarget.W01Continuous.continuousCoefficient_mono
