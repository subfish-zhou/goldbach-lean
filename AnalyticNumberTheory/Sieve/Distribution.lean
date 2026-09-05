import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic.Linarith

/-!
# Generic distribution lemmas

Finite lemmas connecting the multiples of a modulus in an additive sieve
support to prime-counting congruences, and the coprimality characterization
used to identify sieve remainders.
-/

namespace AnalyticNumberTheory.Sieve

/-- A natural is coprime to a product exactly when no prime divisor of the
product divides it. -/
theorem coprime_prod_iff_no_prime_dvd {P a : ℕ} :
    Nat.Coprime P a ↔ ∀ r : ℕ, r.Prime → r ∣ P → ¬ r ∣ a := by
  constructor
  · intro hcop r hr hrP hra
    exact Nat.not_coprime_of_dvd_of_dvd hr.one_lt hrP hra hcop
  · intro hno
    apply Nat.coprime_of_dvd'
    intro r hr hrP hra
    exact False.elim (hno r hr hrP hra)

/-- For `p < N`, divisibility `d ∣ N - p` is the congruence `p ≡ N [MOD d]`. -/
theorem prime_dvd_complement_iff_modEq {N p d : ℕ} (hp_lt : p < N) :
    d ∣ N - p ↔ p ≡ N [MOD d] := by
  exact (Nat.modEq_iff_dvd' (le_of_lt hp_lt)).symm

end AnalyticNumberTheory.Sieve
