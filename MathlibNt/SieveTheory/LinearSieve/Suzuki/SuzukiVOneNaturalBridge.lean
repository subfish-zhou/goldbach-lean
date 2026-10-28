import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiDiscreteParityRecurrence
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144BaseOne

open scoped Classical BigOperators Interval
open Finset
namespace MathlibNt.SieveTheory
open LinearSieve SwitchingPrinciple

theorem SwitchingPrinciple.suzukiVProduct_natCeil_eq
    (S : BoundingSieve) {x : ℝ} {z : ℕ} (hz : z = ⌈x⌉₊) :
    suzukiVProduct S (z : ℝ) = suzukiVProduct S x := by
  classical
  unfold suzukiVProduct
  congr 1
  ext p
  simp only [Finset.mem_filter]
  rw [Nat.cast_lt, hz, Nat.lt_ceil]

 theorem cube_carrier_bridge (Dnat p : ℕ) :
    Dnat ≤ p ^ 3 ↔ (Dnat : ℝ) ^ (1 / 3 : ℝ) ≤ (p : ℝ) := by
  have hcast : (Dnat : ℝ) ≤ (p : ℝ) ^ 3 ↔ Dnat ≤ p ^ 3 := by
    norm_cast
  have hr := Real.rpow_inv_le_iff_of_pos
    (x := (Dnat : ℝ)) (y := (p : ℝ)) (z := (3 : ℝ))
    (by positivity) (by positivity) (by norm_num)
  norm_num [one_div] at hr ⊢
  exact hcast.symm.trans hr.symm

@[simp] theorem suzukiYOne_two (D : ℝ) :
    suzukiYOne D 2 = D ^ (1 / 3 : ℝ) := by
  norm_num [suzukiYOne]
theorem suzukiVProduct_mul_localRatio_eq_sourceDiscreteEuler
    (S : BoundingSieve) {p : ℕ} {z : ℝ} (hpz : (p : ℝ) < z) :
    suzukiVProduct S z * suzukiLocalRatio S (p : ℝ) z = sourceDiscreteEuler S p := by
  classical
  let B := S.prodPrimes.primeFactors.filter (fun q : ℕ => (q : ℝ) < z)
  let A := S.prodPrimes.primeFactors.filter (fun q : ℕ => q < p)
  let C := S.prodPrimes.primeFactors.filter
    (fun q : ℕ => (p : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < z)
  have hA : B.filter (fun q => q < p) = A := by
    ext q
    simp only [B, A, Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · rintro ⟨hqP, hqp⟩
      have hqr : (q : ℝ) < (p : ℝ) := by exact_mod_cast hqp
      exact ⟨⟨hqP, hqr.trans hpz⟩, hqp⟩
  have hC : B.filter (fun q => ¬ q < p) = C := by
    ext q
    simp only [B, C, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hqP, hqz⟩, hnqp⟩
      have hpq : p ≤ q := Nat.le_of_not_gt hnqp
      exact ⟨hqP, (by exact_mod_cast hpq), hqz⟩
    · rintro ⟨hqP, hpq, hqz⟩
      have hpq' : p ≤ q := by exact_mod_cast hpq
      exact ⟨⟨hqP, hqz⟩, Nat.not_lt_of_ge hpq'⟩
  have hpartition :
      (∏ q ∈ B, (1 - S.nu q)) =
        (∏ q ∈ A, (1 - S.nu q)) * (∏ q ∈ C, (1 - S.nu q)) := by
    rw [← hA, ← hC]
    exact (Finset.prod_filter_mul_prod_filter_not B (fun q => q < p)
      (fun q => 1 - S.nu q)).symm
  have hCne : (∏ q ∈ C, (1 - S.nu q)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    have hqP : q ∈ S.prodPrimes.primeFactors := by
      exact (Finset.mem_filter.mp hq).1
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hqP
    have hqdiv : q ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hqP).2.1
    exact ne_of_gt (sub_pos.mpr (S.nu_lt_one_of_prime q hqprime hqdiv))
  unfold suzukiVProduct suzukiLocalRatio sourceDiscreteEuler suzukiSupportedBelow
  change (∏ q ∈ B, (1 - S.nu q)) *
      (∏ q ∈ C, (1 - S.nu q)⁻¹) = ∏ q ∈ A, (1 - S.nu q)
  rw [Finset.prod_inv_distrib, hpartition, mul_assoc, mul_inv_cancel₀ hCne, mul_one]
