/-
Sharp source-native `V₁` bound at a natural-ceiling target cutoff.
The discrete source carrier is transported exactly to the strict real carrier;
there is no equality between the cast ceiling and the real root and no cutoff
error term.
-/
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144BaseOne
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiVnSemanticResolution

open scoped Classical BigOperators Interval
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers

/-- The integral cubic source condition is the real cubic-root lower cutoff. -/
theorem roundedBaseOne_cube_carrier_iff (D p : ℕ) :
    D ≤ p ^ 3 ↔ (D : ℝ) ^ (1 / 3 : ℝ) ≤ (p : ℝ) := by
  have hcast : (D : ℝ) ≤ (p : ℝ) ^ 3 ↔ D ≤ p ^ 3 := by
    norm_cast
  have hr := Real.rpow_inv_le_iff_of_pos
    (x := (D : ℝ)) (y := (p : ℝ)) (z := (3 : ℝ))
    (by positivity) (by positivity) (by norm_num)
  norm_num [one_div] at hr ⊢
  exact hcast.symm.trans hr.symm

/-- The strict Euler suffix identity needed to identify the source summands
with the summands in the real-cutoff Suzuki `V₁`. -/
theorem roundedBaseOne_V_mul_localRatio_eq_sourceEuler
    (S : BoundingSieve) {p : ℕ} {x : ℝ} (hpx : (p : ℝ) < x) :
    suzukiVProduct S x * suzukiLocalRatio S (p : ℝ) x =
      sourceDiscreteEuler S p := by
  classical
  let B := S.prodPrimes.primeFactors.filter (fun q : ℕ => (q : ℝ) < x)
  let A := S.prodPrimes.primeFactors.filter (fun q : ℕ => q < p)
  let C := S.prodPrimes.primeFactors.filter
    (fun q : ℕ => (p : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < x)
  have hA : B.filter (fun q => q < p) = A := by
    ext q
    simp only [B, A, Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · rintro ⟨hqP, hqp⟩
      have hqr : (q : ℝ) < (p : ℝ) := by exact_mod_cast hqp
      exact ⟨⟨hqP, hqr.trans hpx⟩, hqp⟩
  have hC : B.filter (fun q => ¬ q < p) = C := by
    ext q
    simp only [B, C, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hqP, hqx⟩, hnqp⟩
      have hpq : p ≤ q := Nat.le_of_not_gt hnqp
      exact ⟨hqP, (by exact_mod_cast hpq), hqx⟩
    · rintro ⟨hqP, hpq, hqx⟩
      have hpq' : p ≤ q := by exact_mod_cast hpq
      exact ⟨⟨hqP, hqx⟩, Nat.not_lt_of_ge hpq'⟩
  have hpartition :
      (∏ q ∈ B, (1 - S.nu q)) =
        (∏ q ∈ A, (1 - S.nu q)) * (∏ q ∈ C, (1 - S.nu q)) := by
    rw [← hA, ← hC]
    exact (Finset.prod_filter_mul_prod_filter_not B (fun q => q < p)
      (fun q => 1 - S.nu q)).symm
  have hCne : (∏ q ∈ C, (1 - S.nu q)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    have hqP : q ∈ S.prodPrimes.primeFactors :=
      (Finset.mem_filter.mp hq).1
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hqP
    have hqdiv : q ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hqP).2.1
    exact ne_of_gt (sub_pos.mpr (S.nu_lt_one_of_prime q hqprime hqdiv))
  unfold suzukiVProduct suzukiLocalRatio sourceDiscreteEuler suzukiSupportedBelow
  change (∏ q ∈ B, (1 - S.nu q)) *
      (∏ q ∈ C, (1 - S.nu q)⁻¹) = ∏ q ∈ A, (1 - S.nu q)
  rw [Finset.prod_inv_distrib, hpartition]
  field_simp

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
    simp only [suzukiSupportedBelow, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hpP, hpz⟩, hp3⟩
      have hpx : (p : ℝ) < x := by
        rw [hz, Nat.lt_ceil] at hpz
        exact hpz
      exact ⟨hpP, (roundedBaseOne_cube_carrier_iff D p).mp hp3, hpx⟩
    · rintro ⟨hpP, hroot, hpx⟩
      have hpz : p < z := by
        rw [hz, Nat.lt_ceil]
        exact hpx
      exact ⟨⟨hpP, hpz⟩, (roundedBaseOne_cube_carrier_iff D p).mpr hroot⟩
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
  classical
  unfold suzukiVProduct
  congr 1
  ext p
  simp only [Finset.mem_filter]
  rw [Nat.cast_lt, hz, Nat.lt_ceil]

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
  convert hbase using 1 <;> ring


end MathlibNt.SieveTheory
