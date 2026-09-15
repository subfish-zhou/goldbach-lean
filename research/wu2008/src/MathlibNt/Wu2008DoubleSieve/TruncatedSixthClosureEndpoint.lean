import MathlibNt.Wu2008DoubleSieve.TruncatedSixthClosureAssembly

/-!
# The literal fixed-delta truncated-sixth lower-count endpoint

The inner mesh is chosen from the proved integral approximation first,
then the coefficient tolerance, then the actual-count threshold.
Only positive inner classical and admissible count atoms are used.
-/

namespace Wu2008DoubleSieve

open Real Filter
open scoped Classical Topology

theorem truncatedSixthClosure_actual_lower {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (truncatedSixthLowerFdelta δ + truncatedSixthLowerHadmdelta δ - ε) *
        wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
      (truncatedSixthMass N ((N : ℝ) ^ truncatedSixthLowerAlpha)
        ((N : ℝ) ^ truncatedSixthLowerBeta) ((N : ℝ) ^ truncatedSixthLowerSigma)
        ((N : ℝ) ^ truncatedSixthLowerLambda) : ℝ) := by
  obtain ⟨n, hmass⟩ := truncatedSixthClosure_sum_sufficient hδ hδhi (half_pos hε)
  let R := truncatedSixthClosureTotalR false δ n + truncatedSixthClosureTotalR true δ n
  have hR : 0 ≤ R := add_nonneg (truncatedSixthClosure_totalR_nonneg false δ n)
    (truncatedSixthClosure_totalR_nonneg true δ n)
  let η := min 1 (ε / (60 * (R + 1)))
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hηhi : η ≤ 1 := min_le_left _ _
  have hηbound : η ≤ ε / (60 * (R + 1)) := min_le_right _ _
  have hbudget : 15 * η * R ≤ ε / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 60 * (R + 1))).mp hηbound
    nlinarith
  have hpert0 := truncatedSixthClosure_perturbation false δ η n
  have hpert1 := truncatedSixthClosure_perturbation true δ η n
  have hcoefficient :
      truncatedSixthLowerFdelta δ + truncatedSixthLowerHadmdelta δ - ε ≤
        truncatedSixthClosurePerturbedSum false δ η n +
          truncatedSixthClosurePerturbedSum true δ η n - ε / 4 := by
    dsimp [R] at hbudget
    linarith
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (truncatedSixthClosure_family_count hδ hδhi hη hηhi (show 0 < ε / 4 by positivity) n)
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN he
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hcount := hT N ((le_max_right _ _).trans hN) he
  have hmain := (mul_le_mul_of_nonneg_right hcoefficient (truncatedSixthClosure_scale_nonneg hN4)).trans hcount
  simpa only [truncatedSixthMassScale, mul_div_assoc, mul_assoc] using hmain

end Wu2008DoubleSieve
