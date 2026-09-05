import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Generic Selberg main-term identities

Identities for the Selberg terms of an arbitrary `BoundingSieve`: the prime
value of `g`, and the closed factorization of the divisor sum
`Σ_{d | P} g(d) = ∏_{p | P} (1 - ν(p))⁻¹` over the squarefree sifting
product.  These are the finite algebraic core of the Selberg main term,
shared by every Goldbach-type sieve problem.
-/

namespace AnalyticNumberTheory.Sieve

open Finset Real

/-- The Selberg term of any `BoundingSieve` at a prime is
`ν(p) · (1 - ν(p))⁻¹`. -/
theorem selbergTerm_prime {S : BoundingSieve} {p : ℕ} (hp : p.Prime) :
    S.selbergTerms p = S.nu p * (1 - S.nu p)⁻¹ := by
  rw [BoundingSieve.selbergTerms_apply, Nat.Prime.primeFactors hp]
  simp

/-- The Selberg divisor sum of any `BoundingSieve` factors over its prime
factors: `Σ_{d | P} g(d) = ∏_{p | P} (1 - ν(p))⁻¹`. -/
theorem selbergSum_eq_prod_inv {S : BoundingSieve} :
    ∑ d ∈ S.prodPrimes.divisors, S.selbergTerms d =
      ∏ p ∈ S.prodPrimes.primeFactors, (1 - S.nu p)⁻¹ := by
  rw [← ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_add_of_squarefree
    S.selbergTerms_isMultiplicative S.prodPrimes_squarefree]
  apply Finset.prod_congr rfl
  intro p hp
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  rw [selbergTerm_prime hp_prime]
  have hp_dvd : p ∣ S.prodPrimes := Nat.dvd_of_mem_primeFactors hp
  have hlt : S.nu p < 1 := S.nu_lt_one_of_prime p hp_prime hp_dvd
  have hne : (1 : ℝ) - S.nu p ≠ 0 := by linarith
  field_simp [hne]
  ring

end AnalyticNumberTheory.Sieve
