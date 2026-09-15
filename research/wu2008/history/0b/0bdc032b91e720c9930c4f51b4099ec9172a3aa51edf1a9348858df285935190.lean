import MathlibNt.Wu2008DoubleSieve.Omega3NonCoprimeMass
import MathlibNt.SieveTheory.Selberg.SelbergUpperBound

/-!
# The complete squarefree Euler mass in the switched non-coprime error

The frozen divisor/Euler estimate is used with its constant preceding N.
No unproved uniformity is extracted from a pointwise existential bound.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

theorem omega3_sieve_euler_mass :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N → ∀ z : ℝ, z ≤ N →
      (∑ q ∈ (ordinarySievePrimeProduct N z).divisors,
        (3 : ℝ) ^ q.primeFactors.card / Nat.totient q) ≤ C * log N ^ 3 := by
  obtain ⟨C, hC⟩ :=
    MathlibNt.SieveTheory.SelbergUpperBound.divisor_sum_bound_squarefree 3 (by norm_num)
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro N hN z hz
  have hP := ordinarySievePrimeProduct_pos N z
  have hbound := hC (ordinarySievePrimeProduct N z) N hP
    (ordinarySievePrimeProduct_squarefree N z) (by
      intro p hp hpd
      have hmem := Nat.mem_primeFactors.mpr ⟨hp, hpd, hP.ne'⟩
      rw [ordinarySievePrimeProduct, Nat.primeFactors_prod
        (fun _r hr => (mem_primeWindow.mp hr).1)] at hmem
      exact_mod_cast (mem_primeWindow.mp hmem).2.2.2.le.trans hz) hN
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, rpow_natCast] at hbound
  exact hbound.trans
    (mul_le_mul_of_nonneg_right ((le_abs_self C).trans (by linarith))
      (pow_nonneg (log_natCast_nonneg N) 3))

theorem omega3_non_coprime_euler_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 3 ≤ N →
      ∀ (i : ℕ) (δ s t z Y B : ℝ) (W : Fin i → Finset ℕ) (M : Finset ℕ),
      z ≤ N → 0 < Y → 0 ≤ B →
      M ⊆ (ordinarySievePrimeProduct N z).divisors →
      (∀ q ∈ M, q ≤ N) →
      (∀ c ∈ omega3CofactorLabels N δ s t W,
        0 < omega3CofactorValue c ∧ omega3CofactorValue c ≤ N ∧
        ∀ p : ℕ, p.Prime → p ∣ omega3CofactorValue c → Y ≤ p) →
      (∀ e : ℕ, (∑ c ∈ (omega3CofactorLabels N δ s t W).filter
        (fun c => omega3CofactorValue c = e), (convolutionCoeff W c.1 : ℝ)) ≤ B) →
      (∑ q ∈ M, ((3 : ℝ) ^ q.primeFactors.card / Nat.totient q) *
        ∑ c ∈ (omega3CofactorLabels N δ s t W).filter
          (fun c => ¬ (omega3CofactorValue c).Coprime q),
          (convolutionCoeff W c.1 : ℝ) * (omega3CofactorPrimeFibreLE N δ s c).card) ≤
        C * B * N * ((1 + log N) * log N ^ 4 / (Y * log 2)) := by
  obtain ⟨C, hC, hmass⟩ := omega3_sieve_euler_mass
  refine ⟨C, hC, ?_⟩
  intro N hN i δ s t z Y B W M hz hY hB hM hqN hgeom hfibre
  have hnonneg : 0 ≤ B * N * ((1 + log N) * log N / (Y * log 2)) := by
    have := log_natCast_nonneg N
    positivity
  calc
    _ ≤ ∑ q ∈ M, ((3 : ℝ) ^ q.primeFactors.card / Nat.totient q) *
        (B * N * ((1 + log N) * log N / (Y * log 2))) := by
      apply sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact omega3_non_coprime_mass_le W hY hB
        (Nat.pos_of_mem_divisors (hM hq)) (hqN q hq) hgeom hfibre
    _ = (∑ q ∈ M, (3 : ℝ) ^ q.primeFactors.card / Nat.totient q) *
        (B * N * ((1 + log N) * log N / (Y * log 2))) := (sum_mul ..).symm
    _ ≤ (C * log N ^ 3) *
        (B * N * ((1 + log N) * log N / (Y * log 2))) := by
      apply mul_le_mul_of_nonneg_right _ hnonneg
      exact (sum_le_sum_of_subset_of_nonneg hM (fun q _ _ => by positivity)).trans
        (hmass N hN z hz)
    _ = _ := by ring

end Wu2008DoubleSieve
