/-
Sharp source-native `V₁` bound at a natural-ceiling target cutoff.
The discrete source carrier is transported exactly to the strict real carrier;
there is no equality between the cast ceiling and the real root and no cutoff
error term.
-/
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144BaseOne
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiVnSemanticResolution
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiVOneNaturalBridge

open scoped Classical BigOperators Interval
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers

/-- The integral cubic source condition is the real cubic-root lower cutoff. -/
theorem roundedBaseOne_cube_carrier_iff (D p : ℕ) :
    D ≤ p ^ 3 ↔ (D : ℝ) ^ (1 / 3 : ℝ) ≤ (p : ℝ) := by
  exact cube_carrier_bridge D p

/-- The strict Euler suffix identity needed to identify the source summands
with the summands in the real-cutoff Suzuki `V₁`. -/
theorem roundedBaseOne_V_mul_localRatio_eq_sourceEuler
    (S : BoundingSieve) {p : ℕ} {x : ℝ} (hpx : (p : ℝ) < x) :
    suzukiVProduct S x * suzukiLocalRatio S (p : ℝ) x =
      sourceDiscreteEuler S p := by
  exact suzukiVProduct_mul_localRatio_eq_sourceDiscreteEuler S hpx

/-- Exact strict-carrier bridge from source `V₁` at a natural ceiling to
Suzuki's unnormalized real-cutoff `V₁`. -/
theorem roundedBaseOne_sourceV_one_eq_realVOne
    (S : BoundingSieve) {D z : ℕ} {x : ℝ} (hz : z = ⌈x⌉₊) :
    suzukiSourceV S 1 D z = suzukiVOne S (D : ℝ) 2 x := by
  classical
  rw [suzukiSourceV_one, suzukiVOne, suzukiVOneNormalized, suzukiYOne,
    suzukiLemmaEightSixPrimeSum, Finset.mul_sum]
  norm_num
  apply Finset.sum_congr
  · ext p
    simp only [suzukiSupportedBelow, Finset.mem_filter, hz, Nat.lt_ceil,
      roundedBaseOne_cube_carrier_iff, and_assoc, and_comm]
  · intro p hp
    have hpx : (p : ℝ) < x := (Finset.mem_filter.mp hp).2.2
    symm
    have hratio :
        (∏ q ∈ S.prodPrimes.primeFactors.filter (fun q : ℕ =>
          p ≤ q ∧ (q : ℝ) < x), (1 - S.nu q))⁻¹ =
          suzukiLocalRatio S (p : ℝ) x := by
      unfold suzukiLocalRatio
      rw [← Finset.prod_inv_distrib]
      congr 2
      ext q
      simp
    rw [hratio]
    calc
      suzukiVProduct S x * (S.nu p * suzukiLocalRatio S (p : ℝ) x) =
          S.nu p * (suzukiVProduct S x * suzukiLocalRatio S (p : ℝ) x) := by ring
      _ = S.nu p * sourceDiscreteEuler S p := by
        rw [roundedBaseOne_V_mul_localRatio_eq_sourceEuler S hpx]

/-- Strict real cutoffs are unchanged by replacing the cutoff by its natural
ceiling, even though the cast ceiling is generally not the real cutoff. -/
theorem roundedBaseOne_V_natCeil_eq_real
    (S : BoundingSieve) {x : ℝ} {z : ℕ} (hz : z = ⌈x⌉₊) :
    suzukiVProduct S (z : ℝ) = suzukiVProduct S x := by
  exact SwitchingPrinciple.suzukiVProduct_natCeil_eq S hz

/-- Sharp source-native base-one estimate at
`z = ceil(D^(1/s))`.  All cutoff transport is by equality of strict finite
carriers; no cast-ceiling/root equality and no cutoff error are used. -/
theorem suzukiSourceV_one_le_V_natCeil_mul_fOne_add_localError
    {S : BoundingSieve} {D z : ℕ} {s K : ℝ}
    (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊)
    (hD : 1 < (D : ℝ)) (hs : 0 < s) (hs3 : s ≤ 3)
    (hroot2 : 2 ≤ (D : ℝ) ^ (1 / s))
    (hK : 0 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K) :
    suzukiSourceV S 1 D z ≤ suzukiVProduct S (z : ℝ) *
      (finiteSourceLayer 1 2 1 s + 9 * K / (s * Real.log (D : ℝ))) := by
  have hbase :
      suzukiVOne S (D : ℝ) 2 ((D : ℝ) ^ (1 / s)) ≤
        suzukiVProduct S ((D : ℝ) ^ (1 / s)) *
          (finiteSourceLayer 1 2 1 s + K * (2 + 1) ^ 2 /
            (s * Real.log (D : ℝ))) := by
    exact suzukiVOne_le_V_mul_fOne_add_localError
      (S := S) (D := (D : ℝ)) (β := (2 : ℝ))
      (z := (D : ℝ) ^ (1 / s)) (s := s) (K := K)
      hD (by norm_num) hs (by norm_num at hs3 ⊢; exact hs3)
      rfl hroot2 hK hlocal
  rw [roundedBaseOne_sourceV_one_eq_realVOne S hz]
  rw [roundedBaseOne_V_natCeil_eq_real S hz]
  convert hbase using 1; ring


end MathlibNt.SieveTheory
