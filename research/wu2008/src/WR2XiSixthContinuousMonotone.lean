import WR2XiSourceSixth

noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
open Real Set MeasureTheory QuarterTrim NodeExtension Wu2008DoubleSieve
open WuTarget.W01Continuous
open scoped Classical

theorem upperProfile_mono {x y : Fin 9 → ℝ} (hxy : ∀ i, x i ≤ y i) (t : ℝ) :
    upperProfile x t ≤ upperProfile y t := by
  unfold upperProfile
  apply add_le_add
  · by_cases ht : t ∈ Icc 1 (rNode 2)
    · simpa only [indicator_of_mem ht] using hxy 0
    · simp only [indicator_of_notMem ht, le_refl]
  · apply Finset.sum_le_sum
    intro i hi
    by_cases ht : t ∈ Ioc (rNode (i-1)) (rNode i)
    · simp only [indicator_of_mem ht]
      exact extendedNode_mono hxy (by have := (Finset.mem_Icc.mp hi).1; omega)
        (Finset.mem_Icc.mp hi).2
    · simp only [indicator_of_notMem ht, le_refl]

theorem hContinuous_mono {x y : Fin 9 → ℝ} (hxy : ∀ i, x i ≤ y i)
    {s : ℝ} (hs : 2 ≤ s) (hs4 : s ≤ 41/10) : hContinuous x s ≤ hContinuous y s := by
  apply intervalIntegral.integral_mono_on (by norm_num [rNode]; linarith)
    (upperProfile_div_integrable x).intervalIntegrable (upperProfile_div_integrable y).intervalIntegrable
  intro t ht
  exact div_le_div_of_nonneg_right (upperProfile_mono hxy t) (by linarith [ht.1])

theorem continuousGain_mono {x y : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hy : ∀ i, 0 ≤ y i) (hxy : ∀ i, x i ≤ y i) : continuousGain x ≤ continuousGain y := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 4)
  apply integral_mono (continuousUniform_integrable hx le_rfl) (continuousUniform_integrable hy le_rfl)
  intro v
  by_cases hv : v ∈ StaircaseShrink.domain 0
  · simp only [continuousUniform,if_pos hv]
    have hu := u_bounds hv
    exact div_le_div_of_nonneg_right (hContinuous_mono hxy hu.1 hu.2)
      (DirectFiniteF6.denominator_bounds hv).1.le
  · simp only [continuousUniform,if_neg hv, le_refl]

theorem candidate_gain_le_amount :
    continuousGain RationalCandidate.lowerH ≤ SourceSixth.amount := by
  have hm := continuousGain_mono RationalCandidate.lowerH_nonneg CandidateCount.nodes_nonneg
    CandidateCount.candidate_le_nodes
  have hh : 0 ≤ HighConsumer.highGain :=
    mul_nonneg (by norm_num) (integral_nonneg HighConsumer.highGainKernel_nonneg)
  exact hm.trans (le_add_of_nonneg_right hh)

end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.candidate_gain_le_amount
