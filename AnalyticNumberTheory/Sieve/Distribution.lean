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


/-- For `p < N`, divisibility `d ∣ N - p` is the congruence `p ≡ N [MOD d]`. -/
theorem prime_dvd_complement_iff_modEq {N p d : ℕ} (hp_lt : p < N) :
    d ∣ N - p ↔ p ≡ N [MOD d] := by
  exact (Nat.modEq_iff_dvd' (le_of_lt hp_lt)).symm

end AnalyticNumberTheory.Sieve
