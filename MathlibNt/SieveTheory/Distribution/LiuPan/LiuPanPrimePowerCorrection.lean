import MathlibNt.SieveTheory.Liu.LogarithmicIntegral.LiuTrueLiPan
import MathlibNt.SieveTheory.Liu.Weights.LiuWeightMainSum

/-!
# Global bound for Liu's AP prime-power correction

This module bounds the progression-restricted correction by the unrestricted
nonprime von Mangoldt sum. On nonzero von Mangoldt support, `n >= 2`, so the
normalizing logarithm is bounded below by the exact constant `log 2`.
-/

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiuWeight

open Filter Finset
open AnalyticNumberTheory.Sieve
open ArithmeticFunction

/-- The unrestricted nonprime von Mangoldt sum with the logarithmic
normalization occurring in the prime-power correction. -/
noncomputable def globalPrimePowerCorrection (y : ℕ) : ℝ :=
  ∑ n ∈ range (y + 1), if n.Prime then 0 else Λ n / Real.log (n : ℝ)


private theorem globalPrimePowerCorrection_term_le (n : ℕ) :
    (if n.Prime then 0 else Λ n / Real.log (n : ℝ)) ≤
      (if n.Prime then 0 else Λ n / Real.log 2) := by
  by_cases hp : n.Prime
  · simp [hp]
  simp only [hp, if_false]
  by_cases hΛ : Λ n = 0
  · simp [hΛ]
  have hn : 2 ≤ n := IsPrimePow.two_le (vonMangoldt_ne_zero_iff.mp hΛ)
  exact div_le_div_of_nonneg_left vonMangoldt_nonneg (Real.log_pos one_lt_two)
    (Real.log_le_log (by norm_num) (by exact_mod_cast hn))


private theorem sum_not_prime_vonMangoldt_eq_psi_sub_theta (y : ℕ) :
    (∑ n ∈ range (y + 1), if n.Prime then 0 else Λ n) =
      Chebyshev.psi y - Chebyshev.theta y := by
  have h := Chebyshev.psi_sub_theta_eq_sum_not_prime (y : ℝ)
  rw [Nat.floor_natCast] at h
  rw [h, Nat.range_succ_eq_Icc_zero]
  rw [← add_sum_Ioc_eq_sum_Icc (Nat.zero_le y)]
  simp [sum_filter]

/-- The unrestricted correction is at most the Chebyshev prime-power tail
divided by the exact lower bound `log 2` for its denominator. -/
theorem globalPrimePowerCorrection_le_psi_sub_theta (y : ℕ) :
    globalPrimePowerCorrection y ≤
      (Chebyshev.psi y - Chebyshev.theta y) / Real.log 2 := by
  unfold globalPrimePowerCorrection
  calc
    (∑ n ∈ range (y + 1), if n.Prime then 0 else
        Λ n / Real.log (n : ℝ)) ≤
        ∑ n ∈ range (y + 1), if n.Prime then 0 else Λ n / Real.log 2 := by
      apply sum_le_sum
      intro n hn
      exact globalPrimePowerCorrection_term_le n
    _ = (∑ n ∈ range (y + 1), if n.Prime then 0 else Λ n) / Real.log 2 := by
      rw [sum_div]
      apply sum_congr rfl
      intro n hn
      by_cases hp : n.Prime <;> simp [hp]
    _ = (Chebyshev.psi y - Chebyshev.theta y) / Real.log 2 := by
      rw [sum_not_prime_vonMangoldt_eq_psi_sub_theta]


/-- Effective Chebyshev control gives a nonnegative constant for which the
global logarithmically normalized correction is `O(sqrt y)`. -/
theorem exists_globalPrimePowerCorrection_le_sqrt :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℕ,
      globalPrimePowerCorrection y ≤ C * Real.sqrt y := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let D := max C 0 / Real.log 2
  refine ⟨D,
    div_nonneg (le_max_right C 0) (le_of_lt (Real.log_pos one_lt_two)), ?_⟩
  intro y
  calc
    globalPrimePowerCorrection y ≤
        (Chebyshev.psi y - Chebyshev.theta y) / Real.log 2 :=
      globalPrimePowerCorrection_le_psi_sub_theta y
    _ ≤ (max C 0 * Real.sqrt y) / Real.log 2 := by
      apply (div_le_div_iff_of_pos_right (Real.log_pos one_lt_two)).2
      exact (hC (y : ℝ)).trans
        (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.sqrt_nonneg _))
    _ = D * Real.sqrt y := by
      dsimp [D]
      ring


/-! ## Lifting the global estimate through Liu's finite maxima -/


end MathlibNt.SieveTheory.LiuWeight
