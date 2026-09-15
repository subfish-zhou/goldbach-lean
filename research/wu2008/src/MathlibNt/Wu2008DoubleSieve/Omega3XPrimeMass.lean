import MathlibNt.SieveTheory.LiLiuPrereqBuchstabPrimeSums
import MathlibNt.Wu2008DoubleSieve.Omega3XGeometry

/-!
# Uniform reciprocal mass on actual prime intervals

The frozen PNT prime-tail estimate, not an integer harmonic bound, gives
`5 / η` on `[N^η,N]`. Cubing this bound retains ordered triple labels.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter LiLiuPrereqBuchstab
open scoped Classical Topology

theorem omega3X_prime_interval_reciprocal_le {N : ℕ} {η : ℝ}
    (hN : 2 ≤ N) (hη : 0 < η) (hstart : primeErrorStart ≤ (N : ℝ) ^ η) :
    (∑ p ∈ primesIcc ((N : ℝ) ^ η) N, 1 / (p : ℝ)) ≤ 5 / η := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < log (N : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < N by omega))
  by_cases hbound : (N : ℝ) ^ η ≤ N
  · calc
      _ ≤ ∑ p ∈ primesIcc ((N : ℝ) ^ η) N,
          log (N : ℝ) * (1 / ((p : ℝ) * log p)) := by
        apply sum_le_sum
        intro p hp
        obtain ⟨hpp, _, hpN⟩ := mem_primesIcc hN0.le |>.mp hp
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
        have hlogp : 0 < log (p : ℝ) :=
          log_pos (by exact_mod_cast hpp.one_lt)
        calc
          _ = log (p : ℝ) * (1 / ((p : ℝ) * log p)) := by
            field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_right (log_le_log hp0 hpN) (by positivity)
      _ = log (N : ℝ) *
          ∑ p ∈ primesIcc ((N : ℝ) ^ η) N, 1 / ((p : ℝ) * log p) :=
        (mul_sum ..).symm
      _ ≤ log (N : ℝ) * (5 / log ((N : ℝ) ^ η)) :=
        mul_le_mul_of_nonneg_left (sum_primesIcc_inv_mul_log_le hstart hbound) hlogN.le
      _ = 5 / η := by rw [log_rpow hN0]; field_simp
  · have hempty : primesIcc ((N : ℝ) ^ η) N = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨_, hpL, hpN⟩ := mem_primesIcc hN0.le |>.mp hp
      exact hbound (hpL.trans hpN)
    rw [hempty, sum_empty]
    positivity

theorem omega3X_prime_triple_reciprocal_le {N : ℕ} {η : ℝ}
    (hN : 2 ≤ N) (hη : 0 < η) (hstart : primeErrorStart ≤ (N : ℝ) ^ η)
    (S : Finset (ℕ × ℕ × ℕ))
    (hS : ∀ p ∈ S,
      p.1 ∈ primesIcc ((N : ℝ) ^ η) N ∧
      p.2.1 ∈ primesIcc ((N : ℝ) ^ η) N ∧
      p.2.2 ∈ primesIcc ((N : ℝ) ^ η) N) :
    (∑ p ∈ S, 1 / ((p.1 : ℝ) * p.2.1 * p.2.2)) ≤ (5 / η) ^ 3 := by
  let P := primesIcc ((N : ℝ) ^ η) N
  let H : ℝ := ∑ p ∈ P, 1 / (p : ℝ)
  have hH0 : 0 ≤ H := sum_nonneg fun p _ => by positivity
  have hH : H ≤ 5 / η := omega3X_prime_interval_reciprocal_le hN hη hstart
  have hsub : S ⊆ P.product (P.product P) := by
    intro p hp
    exact mem_product.mpr ⟨(hS p hp).1, mem_product.mpr (hS p hp).2⟩
  calc
    _ ≤ ∑ p ∈ P.product (P.product P),
        1 / ((p.1 : ℝ) * p.2.1 * p.2.2) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    _ = H ^ 3 := by
      simp only [product_eq_sprod, sum_product]
      dsimp [H]
      rw [pow_succ, pow_two]
      simp only [sum_mul, mul_sum]
      apply sum_congr rfl
      intro p1 _
      apply sum_congr rfl
      intro p2 _
      apply sum_congr rfl
      intro p3 _
      ring
    _ ≤ _ := pow_le_pow_left₀ hH0 hH 3

end Wu2008DoubleSieve
