import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma141LocalProductMass
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma143NatCeilSupport
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma142InfiniteTail

/-!
# Suzuki Lemmas 14.1--14.3: explicit uniform exponential tail

This file closes the dimension-one local-product hypothesis into the pointwise
Lemma 14.1 source estimate and then combines the natural-ceiling support theorem
with Lemma 14.2.  The resulting bound is uniform in `N`.
-/

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open SwitchingPrinciple

/-- The explicit source parameter supplied by the dimension-one local-product
bound. -/
noncomputable def suzukiSourceL (z K : ℝ) : ℝ :=
  Real.log (Real.log z / Real.log 2) +
    Real.log (1 + K / Real.log 2)

/-- The natural and real presentations of the supported prime mass agree at a
natural cutoff. -/
theorem suzukiPrimeMassBelow_natCast (S : BoundingSieve) (z : ℕ) :
    (∑ p ∈ suzukiSupportedBelow S z, S.nu p) =
      suzukiPrimeMassBelow S (z : ℝ) := by
  unfold suzukiSupportedBelow suzukiPrimeMassBelow
  congr 1
  ext p
  simp

/-- Pointwise Lemma 14.1, with its source parameter discharged directly from
Suzuki's dimension-one local-product hypothesis. -/
theorem suzukiLemma14_1_pointwise_of_localProduct
    (S : BoundingSieve) {K : ℝ} (n D z : ℕ)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hz : 2 ≤ z) :
    suzukiSourceV S n D z ≤
      suzukiSourceL (z : ℝ) K ^ n / (n.factorial : ℝ) := by
  let A : ℝ := ∑ p ∈ suzukiSupportedBelow S z, S.nu p
  have hA : 0 ≤ A := by
    apply Finset.sum_nonneg
    intro p hp
    have hpP := (Finset.mem_filter.mp hp).1
    exact (S.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hpP)
      (Nat.mem_primeFactors.mp hpP).2.1).le
  have hzR : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hAL : A ≤ suzukiSourceL (z : ℝ) K := by
    dsimp only [A]
    rw [suzukiPrimeMassBelow_natCast S z]
    exact lemmaFourteenOne_localProduct_mass hlocal hzR
  have hpow : A ^ n ≤ suzukiSourceL (z : ℝ) K ^ n := by
    exact pow_le_pow_left₀ hA hAL n
  exact (suzukiSourceV_le_pow_div_factorial S n D z).trans
    (div_le_div_of_nonneg_right hpow (by positivity))

/-- The explicit form of Lemma 14.3 at the natural-ceiling cutoff.  Here
`M = ⌊s - 2⌋₊ + 1`; all former majorant, power, and mass premises have been
eliminated, and the right-hand side is independent of `N`. -/
theorem suzukiLemma14_3_natCeil_uniform_explicit
    (S : BoundingSieve) {N D z : ℕ} {s K : ℝ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hD : 1 < D) (hs : 2 ≤ s)
    (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    suzukiActualT S N D z ≤
      suzukiSourceL (z : ℝ) K ^ (⌊s - 2⌋₊ + 1) /
          ((⌊s - 2⌋₊ + 1).factorial : ℝ) *
        Real.exp (suzukiSourceL (z : ℝ) K) := by
  let L := suzukiSourceL (z : ℝ) K
  let M := ⌊s - 2⌋₊ + 1
  have hs0 : 0 < s := by linarith
  have hDreal : (1 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hpow_gt_one : (1 : ℝ) < (D : ℝ) ^ (1 / s) := by
    exact Real.one_lt_rpow hDreal (one_div_pos.mpr hs0)
  have hzgt : 1 < z := by
    rw [hz, Nat.lt_ceil]
    simpa [one_div] using hpow_gt_one
  have hz2 : 2 ≤ z := by omega
  have hL : 0 ≤ L := by
    let A : ℝ := ∑ p ∈ suzukiSupportedBelow S z, S.nu p
    have hA : 0 ≤ A := by
      apply Finset.sum_nonneg
      intro p hp
      have hpP := (Finset.mem_filter.mp hp).1
      exact (S.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hpP)
        (Nat.mem_primeFactors.mp hpP).2.1).le
    have hzR : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz2
    have hAL : A ≤ L := by
      dsimp only [A, L]
      rw [suzukiPrimeMassBelow_natCast S z]
      exact lemmaFourteenOne_localProduct_mass hlocal hzR
    exact hA.trans hAL
  have htail : suzukiActualT S N D z ≤ suzukiExponentialTail L M := by
    apply suzukiActualT_le_exponentialTail_of_support S hL
    · intro n hn
      dsimp only [M] at hn
      exact suzukiSourceV_eq_zero_below_natCeil_rpow S hD hs hz (by omega)
    · intro n
      dsimp only [L]
      exact suzukiLemma14_1_pointwise_of_localProduct S n D z hlocal hz2
  have hexp :
      suzukiExponentialTail L M ≤
        L ^ M / (M.factorial : ℝ) * Real.exp L := by
    exact (suzuki_lemma14_2_infinite_tail L M hL).2
  exact htail.trans hexp


end MathlibNt.SieveTheory
