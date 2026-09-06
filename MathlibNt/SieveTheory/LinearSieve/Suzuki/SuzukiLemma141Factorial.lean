import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma141ElementaryMass

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open SwitchingPrinciple

/-- The elementary symmetric mass is bounded by the corresponding power sum,
with the exact factorial denominator. -/
theorem suzukiElementaryMass_le_pow_div_factorial
    (S : BoundingSieve) (n z : ℕ) :
    suzukiElementaryMass S n z ≤
      (∑ p ∈ suzukiSupportedBelow S z, S.nu p) ^ n / n.factorial := by
  have hnu : ∀ p ∈ suzukiSupportedBelow S z, 0 ≤ S.nu p := by
    intro p hp
    have hpP := (mem_filter.mp hp).1
    exact (S.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hpP)
      (Nat.mem_primeFactors.mp hpP).2.1).le
  have hmul := LinearSieve.factorial_mul_sum_powersetCard_prod_le_pow_sum
    (suzukiSupportedBelow S z) S.nu hnu n
  have hfac : (0 : ℝ) < n.factorial := by positivity
  unfold suzukiElementaryMass
  apply (le_div_iff₀ hfac).2
  simpa [mul_comm] using hmul

/-- Lemma 14.1 factorial bound, combining source domination by the elementary
symmetric mass with its ordered-tuple/factorial estimate. -/
theorem suzukiSourceV_le_pow_div_factorial
    (S : BoundingSieve) (n D z : ℕ) :
    suzukiSourceV S n D z ≤
      (∑ p ∈ suzukiSupportedBelow S z, S.nu p) ^ n / n.factorial :=
  (suzukiSourceV_le_elementaryMass S n D z).trans
    (suzukiElementaryMass_le_pow_div_factorial S n z)


end MathlibNt.SieveTheory
